From Coq Require Import
     Lists.List
     Arith.Le
     Arith
     Omega
     Bool.

Import ListNotations.

From stdpp Require Import
     fin_maps.

From LibTx Require Import
     Storage
     EqDec
     FoldIn
     Handlers.MQ
     Handlers.Deterministic
     ConsistencyLevels
     SLOT.

From RecordUpdate Require Import
     RecordSet.
Import RecordSetNotations.

Definition Offset := MQ.Offset.

Inductive PID :=
| Importer
| TxPid : nat -> PID.

Class LockerCtx {Key Value KVStore : Set}
      `{Storage Key Value KVStore}
      `{FinMap Key KeyMap} `{FinMap PID PidMap}
 := {}.

Section defs.
  Context `{LockerCtx}.

  (** ** Cell encapsulates operations with a single key (read, write, delete): *)
  Record Cell : Set :=
    mkCell
      { cell_seqno : Offset;
        cell_write : option (option Value);
      }.
  Instance etaCall : Settable _ := settable! mkCell <cell_seqno; cell_write>.

  Definition CellStore := KeyMap Cell.
  Definition SeqNoStore := KeyMap Offset.

  (** Transaction log entry *)
  Record Tx :=
    mkTx
      { tx_id : PID;
        tx_ws : Offset;
        tx_tlogn : Offset;
        tx_cells : CellStore;
      }.
  Instance etaTx : Settable _ := settable! mkTx <tx_id; tx_ws; tx_tlogn; tx_cells>.

  Record ImporterState :=
    mkImpState
      { imp_ws : Offset;
        imp_tlogn : Offset;
        imp_lit : Offset;
        imp_seqnos : SeqNoStore;
      }.
  Instance etaImpSt : Settable _ := settable! mkImpState <imp_ws; imp_tlogn; imp_lit; imp_seqnos>.

  Let Event := @Event PID Key Value.

  (** IO handler: *)
  Definition Handler := Var.t ImporterState <+> @MQ.t PID Tx <+>
                        KV.t Key Value KVStore <+> History.t Event <+>
                        ProcessDictionary.t Tx PidMap _ _ <+> Self.t.

  Let req_t := get_handler_req_pid Handler.
  Let ret_t := get_handler_ret_pid Handler.
  Definition TE := @TraceElem PID req_t ret_t.
  Definition Thread := @Thread req_t ret_t.

  (** ** Syscalls: *)
  (** Get offset of the last imported transaction: *)
  Definition get_importer_state : req_t.
    lift (@Var.read ImporterState).
  Defined.

  (** Update offset of the last imported transaction (only the
  importer process is supposed to call this): *)
  Definition update_importer_state (new_state : ImporterState) : req_t.
    lift (Var.write new_state).
  Defined.

  (** Fetch a transaction from the distributed log (blocking call): *)
  Definition pull_tx (offset : Offset) : req_t.
    lift (@MQ.fetch Tx offset).
  Defined.

  (** Try to push a transaction to the distributed log (may fail): *)
  Definition push_tx (tx : Tx) : req_t.
    lift (MQ.produce tx).
  Defined.

  (** Dirty read: *)
  Definition read_d (key : Key) : req_t.
    lift (@Deterministic.KV.read Key Value key).
  Defined.

  (** Dirty write (only the importer process is supposed to call this): *)
  Definition write_d (key : Key) (val : Value) : req_t.
    lift (Deterministic.KV.write key val).
  Defined.

  (** Dirty delete (only the importer process is supposed to call this): *)
  Definition delete_d (key : Key) : req_t.
    lift (@Deterministic.KV.delete Key Value key).
  Defined.

  (** Log a transaction event, such as read, write of commit *)
  Definition log (event : PID -> Event) : req_t.
    lift (event).
  Defined.

  (** Log a transaction event, such as read, write of commit *)
  Definition pd_get : req_t.
    lift (ProcessDictionary.pd_get (Val := Tx)).
  Defined.

  (** Log a transaction event, such as read, write of commit *)
  Definition pd_set (tx : Tx) : req_t.
    lift (ProcessDictionary.pd_put tx).
  Defined.

  (** Get pid of the caller process *)
  Definition self : req_t.
    lift (Self.self).
  Defined.

  (** ** State getters *)
  Definition s_get_log (s : h_state Handler) : list Event.
    simpl in s. now decompose_state.
  Defined.

  Definition s_get_mq (s : h_state Handler) : list Tx.
    simpl in s. now decompose_state.
  Defined.

  Definition s_get_importer_state (s : h_state Handler) : ImporterState.
    simpl in s. now decompose_state.
  Defined.

  Definition s_get_process_dictionary (s : h_state Handler) : PidMap Tx.
    simpl in s. now decompose_state.
  Defined.

  Definition pristine_state ws s :=
    forall seqnos,
      s_get_mq s = [] /\
      s_get_process_dictionary s = empty /\
      s_get_log s = [] /\
      s_get_importer_state s = {| imp_ws := ws;
                                  imp_tlogn := 0;
                                  imp_lit := 0;
                                  imp_seqnos := seqnos
                               |}.

  Section TransactionProc.
    (** Get or create transaction context of a process *)
    Definition get_tx_context cont : Thread :=
      do ctx <- pd_get;
      match ctx with
      | Some ctx =>
          cont ctx
      | None =>
          do s <- get_importer_state;
          do txId <- self;
          cont {| tx_id := txId;
                  tx_ws := s.(imp_ws);
                  tx_tlogn := s.(imp_lit);
                  tx_cells := empty
               |}
      end.

    (** Get seqno of a key: *)
    Definition get_seqno_ key s :=
      match s with
        {| imp_seqnos := s; imp_lit := tlogn; imp_ws := ws |} =>
        match s !! key with
        | Some seqno => seqno
        | None => tlogn - ws
        end
      end.

    Definition get_seqno key cont : Thread :=
      do s <- get_importer_state;
      cont (get_seqno_ key s).

    Definition get_cell key tx_context cont :=
      match tx_context.(tx_cells) !! key with
      | Some x =>
          cont x
      | None =>
          call seqno <- get_seqno key;
          cont {| cell_seqno := seqno; cell_write := None |}
      end.

    Definition read_t key cont : Thread :=
      call tx_context <- get_tx_context;
      call cell <- get_cell key tx_context;
      match cell.(cell_write) with
      | Some v =>
          do _ <- log (read key v);
          cont v
      | None =>
          do v <- read_d key;
          let tx_context' := set tx_cells <[key := cell]> tx_context in
          do _ <- pd_set tx_context';
          do _ <- log (read key v);
          cont v
      end.

    Definition modify_key_t key val cont :=
      call tx_context <- get_tx_context;
      call cell <- get_cell key tx_context;
      let cell' := cell <|cell_write := Some val|> in
      let tx_context' := set tx_cells <[key := cell']> tx_context in
      do _ <- pd_set tx_context';
      do _ <- log (write key val);
      cont I.

    Definition write_t key val cont :=
      modify_key_t key (Some val) cont.

    Definition delete_t key cont :=
      modify_key_t key None cont.

    Fixpoint pre_commit (n_retry : nat) cont : Thread :=
      call tx_context <- get_tx_context;
      do ret <- push_tx tx_context;
      match ret, n_retry with
      | Some offset, _ =>
          cont (Some offset)
      | None, S n_retry =>
          pre_commit n_retry cont
      | _, _ =>
          do _ <- log abort;
          cont None
      end.

    Definition transaction {ret} (tx_fun : (ret -> Thread) -> Thread) cont :=
      call ret <- tx_fun;
      call _ <- pre_commit 1;
      (* TODO: wait for confirmation from the importer *)
      cont I.

  End TransactionProc.

  Section Importer.
    Definition validate_seqnos (tx : Tx) (s : ImporterState) : bool :=
      let seqnos := imp_seqnos s in
      let cells := map_to_list (tx_cells tx) in
      forallb (fun it => match it with
                        (key, cell) => Nat.eqb (cell_seqno cell) (get_seqno_ key s)
                      end) cells.

    Definition validate_tx (s : ImporterState) (tx : Tx) : bool :=
      match s with
      | {| imp_ws := ws; imp_seqnos := seqnos; imp_lit := tlogn |} =>
        (tlogn - (tx_tlogn tx) <? ws) && validate_seqnos tx s
      end.

    Definition update_state (s : ImporterState) (tx : Tx) :=
      let seqnos := imp_seqnos s in
      let tlogn := imp_tlogn s in
      let cells := map_to_list (tx_cells tx) in
      let seqnos' := fold_left
                       (fun acc it =>
                          match it with
                          | (key, {| cell_write := Some _ |}) => <[key := tlogn]> acc
                          | _                                 => acc
                          end) cells seqnos in
      s <| imp_seqnos := seqnos' |> <| imp_lit := imp_tlogn s |>.

    Definition import_ops (cells : CellStore) (cont0 : Thread) : Thread :=
      fold_left (fun cont it =>
                   match it with
                   | (key, {| cell_write := Some (Some val) |}) =>
                     do _ <- write_d key val; cont
                   | (key, {| cell_write := Some None |}) =>
                     do _ <- delete_d key; cont
                   | _ =>
                     cont
                   end) (map_to_list cells) cont0.

    Definition importer_step cont :=
      do s <- get_importer_state;
      let tlogn := 1 + (imp_tlogn s) in
      let s' := s <| imp_tlogn := tlogn |> in
      do tx <- pull_tx tlogn;
      if validate_tx s' tx then
        import_ops (tx_cells tx) (
        do _ <- update_importer_state (update_state s' tx);
        do _ <- log commit;
        cont I)
      else
        do _ <- update_importer_state s';
        do _ <- log abort;
        cont I.

    Fail CoFixpoint importer : Thread :=
      call _ <- importer_step;
      importer. (* TODO *)

  End Importer.

  (** * First, let's prove some very humble liveness properties
    *)
  Section simple_liveness_props.
    Definition readonlyTxEnsemble pid key :=
      ThreadGenerator (TxPid pid)
                      (transaction (fun cont =>
                                      call _ <- read_t key;
                                      cont I)
                                   finale).

    Definition importerEnsemble  :=
      ThreadGenerator Importer (importer_step finale).

    Goal forall repl_window_size pid key,
        -{{ pristine_state repl_window_size }}
           readonlyTxEnsemble pid key (* -|| importerEnsemble *)
         {{ fun s => committed (TxPid pid) (s_get_log s) }}.
    Proof.
      intros. intros t Ht. unfold_ht.
(*       bruteforce Ht Hls. subst. *)
      (* repeat trace_step Hls. *)
      (* subst. *)
    Abort.
  End simple_liveness_props.
End defs.

(* Definition tx_keys (tx : Tx) : list (KT L.Key) := *)
(*   match tx with *)
(*   | {| reads := rr; writes := ww |} => *)
(*     map (fun x => match x with (x, _) => x end) (rr ++ ww) *)
(*   end. *)

(* (** Prove that importing a valid transaction advances offset of the *)
(* last imported transaction *) *)
(* Lemma consume_valid_tx_offset_advance : forall hwm S tx, *)
(*     let (valid, S') := consume_tx S hwm tx in *)
(*     valid = true -> *)
(*     my_tlogn S' = hwm. *)
(* Proof. *)
(*   intros. *)
(*   unfold consume_tx. *)
(*   destruct (check_tx S hwm tx); destruct S; intros H; easy. *)
(* Qed. *)

(** Key subset equality property: "for each key in [l] the value is
    the same in [S1] and [S2]": *)
(* Definition subset_s_eq l S1 S2 : Prop := *)
(*   forall k sn, In (k, sn) l -> *)
(*           get_seqno k S1 = sn /\ get_seqno k S2 = sn. *)

(* Lemma subset_s_eq_comm : forall l S1 S2, subset_s_eq l S1 S2 <-> subset_s_eq l S2 S1. *)
(* Proof. *)
(*   intros. *)
(*   unfold subset_s_eq. split; intros; apply and_comm; auto. *)
(* Qed. *)

(* Lemma subset_s_eq_forallb : forall ws o1 o2 s1 s2 l, *)
(*     let S1 := mkState ws o1 s1 in *)
(*     let S2 := mkState ws o2 s2 in *)
(*     subset_s_eq l S1 S2 -> *)
(*     forallb *)
(*       (fun x : KT L.Key * nat => let (k, v) := x in v =? get_seqno k S1) l = *)
(*     forallb *)
(*       (fun x : KT L.Key * nat => let (k, v) := x in v =? get_seqno k S2) l. *)
(* Proof. *)
(*   intros. *)
(*   repeat rewrite forallb_forallb'. *)
(*   subst S1. subst S2. *)
(*   generalize dependent H. *)
(*   induction l as [|[k o] l IHl0]. *)
(*   - easy. *)
(*   - intros H. *)
(*     (* First, let's prove premise for the induction hypothesis: *) *)
(*     assert (IHl : subset_s_eq l {| sync_window_size := ws; my_tlogn := o1; seqnos := s1 |} *)
(*                                 {| sync_window_size := ws; my_tlogn := o2; seqnos := s2 |}). *)
(*     { unfold subset_s_eq in *. *)
(*       intros. *)
(*       apply H. apply in_cons. assumption. *)
(*     } *)
(*     apply IHl0 in IHl. *)
(*     (* Now let's get rid of the head term: *) *)
(*     unfold forallb' in *. *)
(*     unfold subset_s_eq in H. *)
(*     simpl in *. *)
(*     repeat rewrite Bool.andb_true_r. *)
(*     specialize (H k o) as [H1 H2]. *)
(*     { left. reflexivity. } *)
(*     rewrite H1, H2. *)
(*     repeat rewrite <-beq_nat_refl. *)
(*     (* ...and prove the property for the tail: *) *)
(*     apply IHl. *)
(* Qed. *)

(* (** Prove that only the subset of keys affected by the transaction *)
(* affects the result of lock check *) *)
(* Lemma check_tx_subset_eq_p : forall hwm S1 S2 tx, *)
(*     sync_window_size S1 = sync_window_size S2 -> *)
(*     subset_s_eq (reads tx) S1 S2 -> *)
(*     subset_s_eq (writes tx) S1 S2 -> *)
(*     check_tx S1 hwm tx = check_tx S2 hwm tx. *)
(* Proof. *)
(*   intros hwm S1 S2 tx Hws Hrl Hwl. *)
(*   unfold check_tx. *)
(*   (* Prove a trivial case when transaction is out of replication *)
(*   window: *) *)
(*   destruct S1 as [ws o1 s1]. destruct S2 as [ws2 o2 s2]. *)
(*   destruct tx as [tx_o rl wl tx_commit tx_p]. *)
(*   simpl in *. rewrite <-Hws in *. *)
(*   destruct (hwm - tx_o <? ws); try easy. *)
(*   (* ...Now check seqnos: *) *)
(*   repeat rewrite Bool.andb_true_l. *)
(*   rewrite subset_s_eq_forallb with (o2 := o2) (s2 := s2) (l := rl) by assumption. *)
(*   rewrite subset_s_eq_forallb with (o2 := o2) (s2 := s2) (l := wl) by assumption. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma consume_tx_subset_eq_p : forall hwm S1 S2 tx, *)
(*     sync_window_size S1 = sync_window_size S2 -> *)
(*     subset_s_eq (reads tx) S1 S2 -> *)
(*     subset_s_eq (writes tx) S1 S2 -> *)
(*     let (res1, S1') := consume_tx S1 hwm tx in *)
(*     let (res2, S2') := consume_tx S2 hwm tx in *)
(*     res1 = res2 /\ subset_s_eq (reads tx) S1' S2' /\ subset_s_eq (writes tx) S1' S2'. *)
(* Proof. *)
(*   intros hwm S1 S2 tx Hws Hrl Hwl. *)
(*   unfold consume_tx. *)
(*   rewrite (check_tx_subset_eq_p hwm S1 S2 tx). *)
(*   destruct (check_tx S2 hwm tx); *)
(*     destruct S1 as [ws1 o1 s1]; *)
(*     destruct S2 as [ws2 o2 s2]; *)
(*     destruct tx as [tx_o rl wl tx_commit tx_p]; *)
(*     simpl in *; *)
(*     rewrite Hws in *; *)
(*     split; split; try easy. *)
(*   - subst. *)
(*     unfold update_seqnos. simpl in *. *)
(*     (* Here it's beneficial to iterate the list backwards to make a *)
(*     goal closely matching with the inductive hypothesis: *) *)
(*     replace wl with (rev (rev wl)) by apply rev_involutive. *)
(*     induction (rev wl). *)
(*     + simpl. assumption. *)
(*     + simpl. repeat rewrite fold_left_app. simpl. *)
(*       admit. *)
(*   - unfold update_seqnos. simpl in *. *)
(*     (* Here it's beneficial to iterate the list backwards to make a *)
(*     goal closely matching with the inductive hypothesis: *) *)
(*     replace wl with (rev (rev wl)) by apply rev_involutive. *)
(*     induction (rev wl). *)
(*     + easy. *)
(*     + simpl. repeat rewrite fold_left_app. simpl. *)
(* Abort. *)
(* End UnboundedSpec. *)

(*   - split; try easy. *)
(*     split. *)
(*   - simpl. *)
(*     destruct S1 as [ws ] *)



(* Inductive ReachableState {window_size : nat} {offset : Offset} : State -> Prop := *)
(* | InitState : *)
(*     ReachableState (mkState window_size offset S.new) *)
(* | NextState : forall (tx : Tx) seqnos, *)
(*     let s := mkState window_size offset seqnos in *)
(*     ReachableState s -> *)
(*     ReachableState (next_state s (S offset) tx). *)

(* Definition s_eq (s1 s2 : State) := *)
(*   match s1, s2 with *)
(*   | (mkState ws1 o1 s1), (mkState ws2 o2 s2) => ws1 = ws2 /\ o1 = o2 /\ s1 =s= s2 *)
(*   end. *)

(* Notation "a =S= b" := (s_eq a b) (at level 50). *)

(* Definition replay_erases_initial_stateP := *)
(*   forall (tlog : Tlog) (o0 : Offset), *)
(*     let ws := List.length tlog in *)
(*     forall s1 s2, *)
(*       replay' o0 tlog (mkState ws o0 (collect_garbage ws o0 s1)) =S= *)
(*       replay' o0 tlog (mkState ws o0 (collect_garbage ws o0 s2)). *)

(* Definition garbage_collect_works := *)
(*   forall ws offset seqnos, *)
(*     let s' := collect_garbage ws offset seqnos in *)
(*     forallS s' (fun k Hin => match getT k s' Hin with *)
(*                           | (_, v) => offset - v < ws *)
(*                           end). *)

(* Lemma replay_erases_initial_state : *)
(*   garbage_collect_works -> replay_erases_initial_stateP. *)
(* Proof. *)
(*   unfold replay_erases_initial_stateP. intros Hgc tlog o s1 s2. *)
(*   set (S1 := {| sync_window_size := length tlog; my_tlogn := o; seqnos := collect_garbage (length tlog) o s1 |}). *)
(*   set (S2 := {| sync_window_size := length tlog; my_tlogn := o; seqnos := collect_garbage (length tlog) o s2 |}). *)
(*   replace tlog with (rev (rev tlog)) by apply rev_involutive. *)
(*   remember (rev tlog) as tlogr. *)
(*   induction tlogr as [|tx tlogr IH]. *)
(*   { simpl. *)
(*     repeat split; auto. *)
(*     rewrite <-rev_length. rewrite <- Heqtlogr. simpl. *)
(*     assert (Hempty : forall k s, S.get k (collect_garbage 0 o s) = None). *)
(*     { intros. *)
(*       unfold collect_garbage. *)
(*       admit. *)
(*     } *)
(*     intros k. *)
(*     repeat rewrite Hempty. reflexivity. *)
(*   } *)
(*   { simpl. *)

(*     set (l := length tlog) in *. *)
(*     replace (length (tx :: tlog)) with (S l) in * by reflexivity. *)
(*     set (s1' := collect_garbage l o s1) in *. *)
(*     set (s2' := collect_garbage l o s2) in *. *)
(*     set (s1'' := collect_garbage (S l) o s1) in *. *)
(*     set (s2'' := collect_garbage (S l) o s2) in *. *)
(*     simpl. *)
(*     destruct tx. *)
(*     - (* Write transaction *) *)
(*       destruct (o - local_tlogn w <? S l) in *. *)
(*       + give_up. *)
(*       + *)
(*   } *)

(*     specialize (Hgc 0 o s1) as Hs1. *)
(*     specialize (Hgc 0 o s2) as Hs2. *)
(*     simpl in *. *)
(*     remember (S.get k s1) as v1. *)
(*     remember (S.get k s2) as v2. *)
(*     destruct v1; destruct v2. *)

(*     specialize (Hgc 0 o s1) as Hs1. *)
(*     specialize (Hgc 0 o s2) as Hs2. *)


(*     unfold garbage_collect_works in Hgc. *)

(*     destruct Hs1; destruct Hs2; simpl; auto; destruct tx as [txw]. *)
(*     - unfold next_state.v *)
(*       cbv. *)
(*       remember (S o0 - (local_tlogn txw) <? 0) as ss. *)
(*       destruct (S o0 - (local_tlogn txw) <? 0). *)
(*       + *)






(* Theorem replay_state_is_consistent : *)
(*   forall (* ..for all window size 'ws' and transaction log 'tlog' *)
(*        containing 'high_wm_offset' entries... *) *)
(*     (ws : nat) *)
(*     (tlog : Tlog) *)
(*     (* ...any two followers starting from a valid offset... *) *)
(*     start_offset1 (Hso1 : start_offset1 <= length tlog) *)
(*     start_offset2 (Hso2 : start_offset2 <= length tlog) *)
(*   , (* ...will eventually reach the same state: *) *)
(*     replay tlog (initial_state ws start_offset1) = *)
(*     replay tlog (initial_state ws start_offset2). *)
(* Proof. *)
(*   intros. *)
(*   unfold initial_state. *)
(*   remember (rev tlog) as tlog'. *)
(*   induction rtlog; *)
(*     rewrite <- rev_length in *. *)
(*   - (* Tlog is empty *) *)
(*     simpl in *. destruct Heqrtlog. *)
(*     apply le_n_0_eq in Hso1. *)
(*     apply le_n_0_eq in Hso2. *)
(*     subst. reflexivity. *)
(*   - *)
