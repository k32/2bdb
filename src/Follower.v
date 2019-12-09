Require Import Coq.Lists.List Coq.Arith.Le.
Require Coq.Vectors.Vector.
Import ListNotations.
Require Import Storage.
Require Import Arith.
Require Import Omega.
Require Bool.

Module Follower (S : Storage.Interface).
(* TODO: redefine everything using NZCyclic axioms *)
Module Fin := Coq.Vectors.Fin.
Module Vec := Coq.Vectors.Vector.

Definition Offset := nat.

Variable Key : Storage.Keq_dec.
Variable Value : Set.

(** Transaction log entry *)
Record write_tx :=
  mkWriteTx
    { local_tlogn : Offset;
      reads : list (Storage.KT Key * Offset);
      writes : list (Storage.KT Key * Offset);
      payload : list (Storage.KT Key * Value);
    }.

Inductive Tx : Type :=
| TxW : write_tx -> Tx.

Definition Tlog := list Tx.

Definition Seqno : Set := Offset * Offset.

Definition Seqnos := S.t Key Seqno.

(** State of the follower process *)
Record State :=
  mkState
    { sync_window_size : nat;
      my_tlogn : Offset;
      seqnos : Seqnos;
    }.

Definition initial_state tlogn ws :=
  mkState ws (tlogn - ws) S.new.

Definition get_seqno (k : Storage.KT Key) (s : State) : Offset :=
  match S.get k (seqnos s) with
  | Some (v, _) => v
  | None        => 0
  end.

(* TODO *)
Definition next_seqno (k : Storage.KT Key) (s : State) :=
  (S (get_seqno k s), my_tlogn s).

Definition validate_reads (tx : write_tx) (s : State) : bool :=
  let f x := match x with
             | (k, v) => Nat.eqb v (get_seqno k s)
             end in
  match tx with
  | {| reads := r |} => forallb f r
  end.

Definition validate_writes (tx : write_tx) (s : State) : bool :=
  let f x := match x with
             | (k, v) =>
               let (nsn, _) := next_seqno k s in
               Nat.eqb v nsn
             end in
  match tx with
  | {| writes := w |} => forallb f w
  end.

Definition validate_seqnos (tx : write_tx) (s : State) : bool :=
  andb (validate_reads tx s) (validate_writes tx s).

(** Find cached seqnos that are too old *)
Definition collect_garbage (ws : nat) (offset : Offset) (seqnos : Seqnos) : Seqnos :=
  let f k := match S.get k seqnos with
             | Some (_, o) => leb ws (offset - o)
             | None        => false
             end in
  let old_keys := filter f (S.keys seqnos) in
  fold_left (fun acc k => S.delete k acc) old_keys seqnos.

(** Merge seqnos from a valid transaction to the list *)
Definition update_seqnos (tx : write_tx) (offset : Offset) (seqnos : Seqnos) : Seqnos :=
  let ww := writes tx in
  let tlogn := local_tlogn tx in
  let f acc x := match x with
                 | (k, v) => S.put k (v, tlogn) acc
                 end in
  fold_left f ww seqnos.

Definition check_tx (s : State) (offset : Offset) (tx : Tx) : bool * State :=
  match s with
  | {| sync_window_size := ws; seqnos := seqnos |} =>
    let seqnos' := collect_garbage ws offset seqnos in
    let s' := mkState ws offset seqnos' in
    match tx with
    | TxW txw =>
      match offset - (local_tlogn txw) <? ws with
      | false =>
        (* Node that produced the transaction is way out of date, drop
        this transaction immediately *)
        (false, s')
      | true =>
        (* First sanity check passed, let's proceed to more expensive checks *)
        match validate_seqnos txw s' with
        | false =>
          (* Seqnos don't add up. Drop transaction *)
          (false, s')
        | true =>
          (* Hurray, this transaction is valid! *)
          let seqnos'' := update_seqnos txw offset seqnos' in
          (true, mkState ws offset seqnos'')
        end
      end
    end
  end.

Definition next_state (s : State) (offset : Offset) (tx : Tx) :=
  match check_tx s offset tx with
  | (_, s') => s'
  end.

Fixpoint replay' offset (tlog : Tlog) (s : State) : State :=
  match tlog with
  | tx :: tail =>
    match check_tx s offset tx with
    | (_, s') => replay' (S offset) tail s'
    end
  | [] => s
  end.

Definition replay (tlog : Tlog) (s : State) : State :=
  let start := my_tlogn s in
  let tlog' := skipn start tlog in
  replay' start tlog' s.

End Follower.

Module FollowerSpec (S : Storage.Interface).

Module Follower' := Follower(S).
Import Follower'.
Module Fin := Coq.Vectors.Fin.
Module Vec := Coq.Vectors.Vector.
Module SP := Storage.Properties(S).
Import SP.
Module SE := Storage.Equality(S).
Import SE.

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

Global Opaque collect_garbage validate_reads validate_writes validate_seqnos
       leb fold_left andb update_seqnos Nat.sub forallb.

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
  induction tlog as [|tx tlog IH].
  { simpl.
    repeat split; auto.
    intros k.
    specialize (Hgc 0 o s1) as Hs1.
    specialize (Hgc 0 o s2) as Hs2.
    simpl in *.
    remember (S.get k  as sg.
    destruct S.get; destruct S.get.
    -
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
