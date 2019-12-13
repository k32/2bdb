Require Import Coq.Lists.List Coq.Arith.Le.
Require Coq.Vectors.Vector.
Import ListNotations.
Require Import Storage.
Require Import Arith.
Require Import Omega.
Require Bool.

Module Unbounded (S : Storage.Interface).

Definition Offset := nat.

Variable Key : Storage.Keq_dec.
Variable Value : Set.
Variable TxPayload : Set.

(** Transaction log entry *)
Record Tx :=
  mkTx
    { last_imported_offset : Offset;
      reads : list (Storage.KT Key * Offset);
      writes : list (Storage.KT Key * Offset);
      commit : bool;
      payload : TxPayload;
    }.

Definition Tlog := list Tx.

Definition Seqno : Set := Offset.

Definition Seqnos := S.t Key Seqno.

(** State of the follower process *)
Record State :=
  mkState
    { sync_window_size : nat;
      my_tlogn : Offset;
      seqnos : Seqnos;
    }.

Definition get_seqno (k : Storage.KT Key) (s : State) : Offset :=
  match S.get k (seqnos s) with
  | Some v => v
  | None   => 0
  end.

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

Definition tx_keys (tx : Tx) : list (Storage.KT L.Key) :=
  match tx with
  | {| reads := rr; writes := ww |} =>
    map (fun x => match x with (x, _) => x end) (rr ++ ww)
  end.

Lemma consume_one_read_tx_p : forall ws o1 o2 hwm s1 s2 k tx_o tx_p,
    let S1 := mkState ws o1 s1 in
    let S2 := mkState ws o2 s2 in
    let tx := mkTx tx_o [(k, tx_o)] [] true tx_p in
    get_seqno k S1 = get_seqno k S2 ->
    let (res1, S1') := consume_tx S1 hwm tx in
    let (res2, S2') := consume_tx S2 hwm tx in
    res1 = res2 /\
    get_seqno k S1' = get_seqno k S2'.
Proof.
  intros.
  simpl.
  rewrite H.
  destruct (hwm - tx_o <? ws).
  - destruct (tx_o =? get_seqno k S2); simpl; split; auto.
  - simpl. auto.
Qed.

Lemma consume_one_write_tx_p : forall ws o1 o2 hwm s1 s2 k tx_o tx_p,
    let S1 := mkState ws o1 s1 in
    let S2 := mkState ws o2 s2 in
    let tx := mkTx tx_o [] [(k, tx_o)] true tx_p in
    get_seqno k S1 = get_seqno k S2 ->
    let (res1, S1') := consume_tx S1 hwm tx in
    let (res2, S2') := consume_tx S2 hwm tx in
    res1 = res2 /\
    get_seqno k S1' = get_seqno k S2'.
Proof.
  intros.
  simpl.
  rewrite H.
  destruct (hwm - tx_o <? ws).
  - destruct (tx_o =? get_seqno k S2); simpl; split; auto.
    unfold update_seqnos, get_seqno. simpl.
    repeat rewrite S.keep. reflexivity.
  - simpl. auto.
Qed.

Inductive ReachableState {window_size : nat} {offset : Offset} : State -> Prop :=
| InitState :
    ReachableState (mkState window_size offset S.new)
| NextState : forall (tx : Tx) seqnos,
    let s := mkState window_size offset seqnos in
    ReachableState s ->
    ReachableState (next_state s (S offset) tx).

Definition s_eq (s1 s2 : State) :=
  match s1, s2 with
  | (mkState ws1 o1 s1), (mkState ws2 o2 s2) => ws1 = ws2 /\ o1 = o2 /\ s1 =s= s2
  end.

Notation "a =S= b" := (s_eq a b) (at level 50).

Definition replay_erases_initial_stateP :=
  forall (tlog : Tlog) (o0 : Offset),
    let ws := List.length tlog in
    forall s1 s2,
      replay' o0 tlog (mkState ws o0 (collect_garbage ws o0 s1)) =S=
      replay' o0 tlog (mkState ws o0 (collect_garbage ws o0 s2)).

Definition garbage_collect_works :=
  forall ws offset seqnos,
    let s' := collect_garbage ws offset seqnos in
    forallS s' (fun k Hin => match getT k s' Hin with
                          | (_, v) => offset - v < ws
                          end).

Lemma replay_erases_initial_state :
  garbage_collect_works -> replay_erases_initial_stateP.
Proof.
  unfold replay_erases_initial_stateP. intros Hgc tlog o s1 s2.
  set (S1 := {| sync_window_size := length tlog; my_tlogn := o; seqnos := collect_garbage (length tlog) o s1 |}).
  set (S2 := {| sync_window_size := length tlog; my_tlogn := o; seqnos := collect_garbage (length tlog) o s2 |}).
  replace tlog with (rev (rev tlog)) by apply rev_involutive.
  remember (rev tlog) as tlogr.
  induction tlogr as [|tx tlogr IH].
  { simpl.
    repeat split; auto.
    rewrite <-rev_length. rewrite <- Heqtlogr. simpl.
    assert (Hempty : forall k s, S.get k (collect_garbage 0 o s) = None).
    { intros.
      unfold collect_garbage.
      admit.
    }
    intros k.
    repeat rewrite Hempty. reflexivity.
  }
  { simpl.

    set (l := length tlog) in *.
    replace (length (tx :: tlog)) with (S l) in * by reflexivity.
    set (s1' := collect_garbage l o s1) in *.
    set (s2' := collect_garbage l o s2) in *.
    set (s1'' := collect_garbage (S l) o s1) in *.
    set (s2'' := collect_garbage (S l) o s2) in *.
    simpl.
    destruct tx.
    - (* Write transaction *)
      destruct (o - local_tlogn w <? S l) in *.
      + give_up.
      +
  }

    specialize (Hgc 0 o s1) as Hs1.
    specialize (Hgc 0 o s2) as Hs2.
    simpl in *.
    remember (S.get k s1) as v1.
    remember (S.get k s2) as v2.
    destruct v1; destruct v2.

    specialize (Hgc 0 o s1) as Hs1.
    specialize (Hgc 0 o s2) as Hs2.


    unfold garbage_collect_works in Hgc.

    destruct Hs1; destruct Hs2; simpl; auto; destruct tx as [txw].
    - unfold next_state.v
      cbv.
      remember (S o0 - (local_tlogn txw) <? 0) as ss.
      destruct (S o0 - (local_tlogn txw) <? 0).
      +






Theorem replay_state_is_consistent :
  forall (* ..for all window size 'ws' and transaction log 'tlog'
       containing 'high_wm_offset' entries... *)
    (ws : nat)
    (tlog : Tlog)
    (* ...any two followers starting from a valid offset... *)
    start_offset1 (Hso1 : start_offset1 <= length tlog)
    start_offset2 (Hso2 : start_offset2 <= length tlog)
  , (* ...will eventually reach the same state: *)
    replay tlog (initial_state ws start_offset1) =
    replay tlog (initial_state ws start_offset2).
Proof.
  intros.
  unfold initial_state.
  remember (rev tlog) as tlog'.
  induction rtlog;
    rewrite <- rev_length in *.
  - (* Tlog is empty *)
    simpl in *. destruct Heqrtlog.
    apply le_n_0_eq in Hso1.
    apply le_n_0_eq in Hso2.
    subst. reflexivity.
  -
