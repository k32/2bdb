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

Definition Offset := MQ.Offset.

Section SingleNode.
  Context {PID Key Value St1 St2 : Set}
          `{HStore1 : @Storage Key Value St1}
          `{HStore2: @Storage Key Offset St2}
          `{HKeq_dec : EqDec Key}.

  (** Transaction log entry *)
  Record Tx :=
    mkTx
      { tx_ws : Offset;
        tx_tlogn : Offset;
        tx_reads : list (Key * Offset);
        tx_writes : list (Key * Offset);
        (* tx_commit : bool;  TODO: later *)
        tx_payload : list (Key * Value);
      }.
  Instance etaTx : Settable _ := settable! mkTx <tx_ws; tx_tlogn; tx_reads; tx_writes; (* tx_commit; *) tx_payload>.

  (** IO handler: *)
  Let initial_tlogn o := o = 0.
  Let initial_kv (s : St1) := s = Storage.new.
  Let initial_seqnos (s : St2) := s = Storage.new.

  Definition Handler := (@Deterministic.AtomicVar.t PID MQ.Offset _ <+> @MQ.t PID Tx) <+>
                        (@Deterministic.KV.t PID Key Offset St2 _ <+>
                         @Deterministic.KV.t PID Key Value St1 _).
  Definition ctx := hToCtx Handler.
  Let req_t := ctx_req_t ctx.

  (** ** Syscalls: *)
  (** Get offset of the last imported transaction: *)
  Definition get_tlogn : req_t :=
    inl (inl (AtomicVar.read)).

  (** Update offset of the last imported transaction (only the
  importer process is supposed to call this): *)
  Definition update_tlogn n : req_t :=
    inl (inl (AtomicVar.write n)).

  (** Fetch a transaction from a distributed log (blocking call): *)
  Definition pull_tx offset : req_t :=
    inl (inr (MQ.fetch offset)).

  (** Try to push a transaction to the distributed log (may fail): *)
  Definition push_tx tx : req_t :=
    inl (inr (MQ.produce tx)).

  (** Get seqno of a key: *)
  Definition try_get_seqno key : req_t :=
    inr (inl (Deterministic.KV.read key)).

  (** Update seqno of a key: *)
  Definition update_seqno key n : req_t :=
    inr (inl (Deterministic.KV.write key n)).

  (** Dirty read: *)
  Definition read_d key : req_t :=
    inr (inr (Deterministic.KV.read key)).

  (** Dirty write (only the importer process is supposed to call
  this): *)
  Definition write_d key val : req_t :=
    inr (inr (Deterministic.KV.write key val)).

  (** Dirty detele (only the importer process is supposed to call
  this): *)
  Definition delete_d key : req_t :=
    inr (inr (Deterministic.KV.delete key)).

  Notation "'do' V '<-' I ; C" := (@t_cont ctx (I) (fun V => C))
                                    (at level 100, C at next level, V ident, right associativity).

  Notation "'done' I" := (@t_cont ctx (I) (fun _ => t_dead))
                           (at level 100, right associativity).

  Notation "'call' V '<-' I ; C" := (I (fun V => C))
                                      (at level 100, C at next level, V ident, right associativity).


  Definition get_seqno key tx_context cont :=
    do v0 <- try_get_seqno key;
    match v0 with
    | Some v =>
        cont v
    | None =>
        do tlogn <- get_tlogn;
        cont (tlogn - tx_context.(tx_ws))
    end.

  Definition read_t key tx_context cont :=
    match tx_context with
    | {| tx_reads := rr |} =>
      call seqno <- get_seqno key tx_context;
      do val <- read_d key;
      cont (val, tx_context)
    end.

  Definition write_t key value tx_context cont :=
    call seqno <- get_seqno key tx_context;
    cont (I, tx_context).

  Definition validate_seqnos (tx : Tx) cont :=
    match
    done try_get_seqno 1.

  Definition validate_seqnos (tx : Tx) (s : State) : bool :=
    let f x := match x with
               | (k, v) => Nat.eqb v (get_seqno k s)
               end in
    match tx with
    | {| reads := r; writes := w |} => forallb f r && forallb f w
    end.

Definition check_tx (s : State) (offset : Offset) (tx : Tx) : bool :=
  match s with
  | {| sync_window_size := ws; seqnos := seqnos |} =>
    (offset - (last_imported_offset tx) <? ws) && validate_seqnos tx s
  end.

Definition update_seqnos (tx : Tx) (offset : Offset) (seqnos : Seqnos) : Seqnos :=
  let ww := writes tx in
  let f acc x := match x with
                 | (k, v) => S.put k offset acc
                 end in
  fold_left f ww seqnos.

Definition consume_tx (S : State) (offset : Offset) (tx : Tx) : bool * State :=
  match S with
  | {| sync_window_size := ws; seqnos := s |} =>
    if check_tx S offset tx then
      (true, mkState ws offset (update_seqnos tx offset s))
    else
      (false, S)
  end.

(* Fixpoint replay' offset (tlog : Tlog) (s : State) : State := *)
(*   match tlog with *)
(*   | tx :: tail => *)
(*     match check_tx s offset tx with *)
(*     | (_, s') => replay' (S offset) tail s' *)
(*     end *)
(*   | [] => s *)
(*   end. *)

(* Definition replay (tlog : Tlog) (s : State) : State := *)
(*   let start := my_tlogn s in *)
(*   let tlog' := skipn start tlog in *)
(*   replay' start tlog' s. *)

End Unbounded.

Module UnboundedSpec (S : Storage.Interface).

Module L := Unbounded(S). Import L.
Module SP := Storage.Properties(S). Import SP.
Module SE := Storage.Equality(S). Import SE.

Definition tx_keys (tx : Tx) : list (KT L.Key) :=
  match tx with
  | {| reads := rr; writes := ww |} =>
    map (fun x => match x with (x, _) => x end) (rr ++ ww)
  end.

(** Prove that importing a valid transaction advances offset of the
last imported transaction *)
Lemma consume_valid_tx_offset_advance : forall hwm S tx,
    let (valid, S') := consume_tx S hwm tx in
    valid = true ->
    my_tlogn S' = hwm.
Proof.
  intros.
  unfold consume_tx.
  destruct (check_tx S hwm tx); destruct S; intros H; easy.
Qed.

(** Key subset equality property: "for each key in [l] the value is
the same in [S1] and [S2]": *)
Definition subset_s_eq l S1 S2 : Prop :=
  forall k sn, In (k, sn) l ->
          get_seqno k S1 = sn /\ get_seqno k S2 = sn.

Lemma subset_s_eq_comm : forall l S1 S2, subset_s_eq l S1 S2 <-> subset_s_eq l S2 S1.
Proof.
  intros.
  unfold subset_s_eq. split; intros; apply and_comm; auto.
Qed.

Lemma subset_s_eq_forallb : forall ws o1 o2 s1 s2 l,
    let S1 := mkState ws o1 s1 in
    let S2 := mkState ws o2 s2 in
    subset_s_eq l S1 S2 ->
    forallb
      (fun x : KT L.Key * nat => let (k, v) := x in v =? get_seqno k S1) l =
    forallb
      (fun x : KT L.Key * nat => let (k, v) := x in v =? get_seqno k S2) l.
Proof.
  intros.
  repeat rewrite forallb_forallb'.
  subst S1. subst S2.
  generalize dependent H.
  induction l as [|[k o] l IHl0].
  - easy.
  - intros H.
    (* First, let's prove premise for the induction hypothesis: *)
    assert (IHl : subset_s_eq l {| sync_window_size := ws; my_tlogn := o1; seqnos := s1 |}
                                {| sync_window_size := ws; my_tlogn := o2; seqnos := s2 |}).
    { unfold subset_s_eq in *.
      intros.
      apply H. apply in_cons. assumption.
    }
    apply IHl0 in IHl.
    (* Now let's get rid of the head term: *)
    unfold forallb' in *.
    unfold subset_s_eq in H.
    simpl in *.
    repeat rewrite Bool.andb_true_r.
    specialize (H k o) as [H1 H2].
    { left. reflexivity. }
    rewrite H1, H2.
    repeat rewrite <-beq_nat_refl.
    (* ...and prove the property for the tail: *)
    apply IHl.
Qed.

(** Prove that only the subset of keys affected by the transaction
affects the result of lock check *)
Lemma check_tx_subset_eq_p : forall hwm S1 S2 tx,
    sync_window_size S1 = sync_window_size S2 ->
    subset_s_eq (reads tx) S1 S2 ->
    subset_s_eq (writes tx) S1 S2 ->
    check_tx S1 hwm tx = check_tx S2 hwm tx.
Proof.
  intros hwm S1 S2 tx Hws Hrl Hwl.
  unfold check_tx.
  (* Prove a trivial case when transaction is out of replication
  window: *)
  destruct S1 as [ws o1 s1]. destruct S2 as [ws2 o2 s2].
  destruct tx as [tx_o rl wl tx_commit tx_p].
  simpl in *. rewrite <-Hws in *.
  destruct (hwm - tx_o <? ws); try easy.
  (* ...Now check seqnos: *)
  repeat rewrite Bool.andb_true_l.
  rewrite subset_s_eq_forallb with (o2 := o2) (s2 := s2) (l := rl) by assumption.
  rewrite subset_s_eq_forallb with (o2 := o2) (s2 := s2) (l := wl) by assumption.
  reflexivity.
Qed.

Lemma consume_tx_subset_eq_p : forall hwm S1 S2 tx,
    sync_window_size S1 = sync_window_size S2 ->
    subset_s_eq (reads tx) S1 S2 ->
    subset_s_eq (writes tx) S1 S2 ->
    let (res1, S1') := consume_tx S1 hwm tx in
    let (res2, S2') := consume_tx S2 hwm tx in
    res1 = res2 /\ subset_s_eq (reads tx) S1' S2' /\ subset_s_eq (writes tx) S1' S2'.
Proof.
  intros hwm S1 S2 tx Hws Hrl Hwl.
  unfold consume_tx.
  rewrite (check_tx_subset_eq_p hwm S1 S2 tx).
  destruct (check_tx S2 hwm tx);
    destruct S1 as [ws1 o1 s1];
    destruct S2 as [ws2 o2 s2];
    destruct tx as [tx_o rl wl tx_commit tx_p];
    simpl in *;
    rewrite Hws in *;
    split; split; try easy.
  - subst.
    unfold update_seqnos. simpl in *.
    (* Here it's beneficial to iterate the list backwards to make a
    goal closely matching with the inductive hypothesis: *)
    replace wl with (rev (rev wl)) by apply rev_involutive.
    induction (rev wl).
    + simpl. assumption.
    + simpl. repeat rewrite fold_left_app. simpl.
      admit.
  - unfold update_seqnos. simpl in *.
    (* Here it's beneficial to iterate the list backwards to make a
    goal closely matching with the inductive hypothesis: *)
    replace wl with (rev (rev wl)) by apply rev_involutive.
    induction (rev wl).
    + easy.
    + simpl. repeat rewrite fold_left_app. simpl.
Abort.
End UnboundedSpec.

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
