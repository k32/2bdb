From Coq Require Import
     Lists.List
     Arith.Le
     Arith
     Omega
     Bool.

Import ListNotations.

From LibTx Require Import
     Storage
     EqDec
     FoldIn
     Process
     Handler
     Handlers.MQ
     Handlers.Deterministic.

From RecordUpdate Require Import
     RecordSet.
Import RecordSetNotations.

Definition Offset := MQ.Offset.

Section defs.
  Context {PID Key Value KVStore SeqnoStore : Set}
          `{HStore1 : @Storage Key Value KVStore}
          `{HStore2: @Storage Key Offset SeqnoStore}
          `{HKeq_dec : EqDec Key}.

  (** Encapsulate updates to a single value: *)
  Record Cell : Set :=
    mkCell
      { cell_seqno : Offset;
        cell_write : option (option Value);
      }.
  Instance etaCall : Settable _ := settable! mkCell <cell_seqno; cell_write>.

  Context {CellStore : Set} `{HStoreCell: @Storage Key Cell CellStore}.

  (** Transaction log entry *)
  Record Tx : Set :=
    mkTx
      { tx_id : PID;
        tx_ws : Offset;
        tx_tlogn : Offset;
        tx_cells : CellStore;
      }.
  Instance etaTx : Settable _ := settable! mkTx <tx_id; tx_ws; tx_tlogn; tx_cells>.

  Record ImporterState : Set :=
    mkImpState
      { imp_ws : Offset;
        imp_tlogn : Offset;
        imp_lit : Offset;
        imp_seqnos : SeqnoStore;
      }.
  Instance etaImpSt : Settable _ := settable! mkImpState <imp_ws; imp_tlogn; imp_lit; imp_seqnos>.

  (** IO handler: *)
  Definition Handler := (@Deterministic.Var.t PID ImporterState <+> @MQ.t PID Tx) <+>
                        @Deterministic.KV.t PID Key Value KVStore _.

  Definition ctx := hToCtx Handler.
  Let req_t := ctx_req_t ctx.


  Notation "'do' V '<-' I ; C" := (@t_cont ctx (I) (fun V => C))
                                    (at level 100, C at next level, V ident, right associativity).

  Notation "'done' I" := (@t_cont ctx (I) (fun _ => t_dead))
                           (at level 100, right associativity).

  Notation "'call' V '<-' I ; C" := (I (fun V => C))
                                      (at level 100, C at next level, V ident,
                                       right associativity, only parsing).

  (** ** Syscalls: *)
  (** Get offset of the last imported transaction: *)
  Definition get_importer_state : req_t :=
    inl (inl (Var.read)).

  (** Update offset of the last imported transaction (only the
  importer process is supposed to call this): *)
  Definition update_importer_state new_state : req_t :=
    inl (inl (Var.write new_state)).

  (** Fetch a transaction from a distributed log (blocking call): *)
  Definition pull_tx offset : req_t :=
    inl (inr (MQ.fetch offset)).

  (** Try to push a transaction to the distributed log (may fail): *)
  Definition push_tx tx : req_t :=
    inl (inr (MQ.produce tx)).

  (** Dirty read: *)
  Definition read_d key : req_t :=
    inr (Deterministic.KV.read key).

  (** Dirty write (only the importer process is supposed to call this): *)
  Definition write_d key val : req_t :=
    inr (Deterministic.KV.write key val).


  (** Dirty delete (only the importer process is supposed to call this): *)
  Definition delete_d key : req_t :=
    inr (Deterministic.KV.delete key).

  Section TransactionProc.
    (** Get seqno of a key: *)
    Definition get_seqno_ key s :=
      match s with
        {| imp_seqnos := s; imp_lit := tlogn; imp_ws := ws |} =>
        match Storage.get key s with
        | Some seqno => seqno
        | None => tlogn - ws
        end
      end.

    Definition get_seqno key cont : Thread :=
      do s <- get_importer_state;
      cont (get_seqno_ key s).

    Definition get_cell key tx_context cont :=
      match Storage.get key tx_context.(tx_cells) with
      | Some x =>
          cont x
      | None =>
          call seqno <- get_seqno key;
          cont {| cell_seqno := seqno; cell_write := None |}
      end.

    Definition read_t key tx_context cont :=
      call cell <- get_cell key tx_context;
      match cell.(cell_write) with
      | Some v =>
          cont (v, tx_context)
      | None =>
          do v <- read_d key;
          let tx_context' := set tx_cells (put key cell) tx_context in
          cont (v, tx_context')
      end.

    Definition write_t key val tx_context cont :=
      call cell <- get_cell key tx_context;
      let cell' := cell <|cell_write := Some (Some val)|> in
      let tx_context' := set tx_cells (put key cell') tx_context in
      cont (I, tx_context).

    Definition start_tx self cont :=
      do s <- get_importer_state;
      cont {| tx_id := self;
              tx_ws := s.(imp_ws);
              tx_tlogn := s.(imp_lit);
              tx_cells := Storage.new
           |}.

    CoFixpoint pre_commit tx_context cont :=
      do ret <- push_tx tx_context;
      match ret with
      | Some offset =>
          cont offset
      | None =>
          pre_commit tx_context cont
      end.

    CoFixpoint transaction self (tx_fun : Tx -> (Tx -> Thread) -> Thread) cont :=
      call tx_context <- start_tx self;
      call tx_context' <- tx_fun tx_context;
      call _ <- pre_commit tx_context;
      cont I.
  End TransactionProc.

  Section Importer.
    Definition validate_seqnos (tx : Tx) (s : ImporterState) : bool :=
      let seqnos := imp_seqnos s in
      let cells := tx_cells tx in
      let keys := keys cells in
      forallb' keys (fun key Hin =>
                       let cell := getT key cells Hin in
                       Nat.eqb (cell_seqno cell) (get_seqno_ key s)).

    Definition validate_tx (s : ImporterState) (tx : Tx) : bool :=
      match s with
      | {| imp_ws := ws; imp_seqnos := seqnos; imp_lit := tlogn |} =>
        (tlogn - (tx_tlogn tx) <? ws) && validate_seqnos tx s
      end.

    Definition update_state (s : ImporterState) (tx : Tx) :=
      let lit := imp_lit s in
      let cells := tx_cells tx in
      let keys := keys cells in
      let seqnos := imp_seqnos s in
      let seqnos' := foldl' keys (fun key Hin acc =>
                                    match getT key cells Hin with
                                    | {| cell_write := Some _ |} => put key lit acc
                                    | _                          => seqnos
                                    end) seqnos in
      s <| imp_seqnos := seqnos' |> <| imp_lit := imp_tlogn s |>.

    Definition import_ops cells cont : Thread :=
      foldl' (keys cells)
             (fun key Hin cont =>
                match getT key cells Hin with
                | {| cell_write := Some (Some val) |} =>
                    do _ <- write_d key val;
                    cont
                | {| cell_write := Some None |} =>
                    do _ <- delete_d key;
                    cont
                | _ =>
                    cont
                end) (cont I).

    Definition importer_step cont :=
      do s <- get_importer_state;
      let tlogn := 1 + (imp_tlogn s) in
      let s' := s <| imp_tlogn := tlogn |> in
      do tx <- pull_tx tlogn;
      if validate_tx s' tx then
        call _ <- import_ops (tx_cells tx);
        do _ <- update_importer_state (update_state s' tx);
        cont I
      else
        do _ <- update_importer_state s';
        cont I.

    Fail CoFixpoint importer : Thread :=
      call _ <- importer_step;
      importer. (* TODO *)

  End Importer.
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

(* (** Key subset equality property: "for each key in [l] the value is *)
(* the same in [S1] and [S2]": *) *)
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
