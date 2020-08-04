(** * SLOT model checker *)
From LibTx.SLOT Require Export
     Hoare
     Ensemble.

From Coq Require Import
     List
     Program.Basics
     Logic.Classical_Prop.

Import ListNotations.

Open Scope hoare_scope.

Lemma te_comm_dec : forall `{StateSpace} a b, trace_elems_commute a b \/ not (trace_elems_commute a b).
Proof.
  intros.
  apply classic.
Qed.

Ltac remove_commuting_interleavings :=
  lazymatch goal with
  | [Ht : Interleaving ?t1 ?t2 ?t, Hls : LongStep ?s ?t ?s' |- _] =>
    let t' := fresh in
    let Ht' := fresh in
    let Hls' := fresh in
    destruct (canonicalize_ilv te_comm_dec t1 t2 t Ht s s' Hls) as [t' [Ht' Hls']];
    (* Fail here if [t] is used in any hypothesis except [Hls]: *)
    clear Ht; clear Hls; clear t;
    rename t' into t; rename Ht' into Ht; rename Hls' into Hls'
  end.

Ltac transform_ensemble e :=
  lazymatch type of e with
  | (?a = ?b) =>
    subst a || subst b
  | (Parallel ?e1 ?e2) ?t =>
    let t_l := fresh "t_l" in
    let Ht_l := fresh "Ht_l" in
    let t_r := fresh "t_r" in
    let Ht_r := fresh "Ht_r" in
    let t := fresh "t" in
    let Ht := fresh "Ht" in
    destruct e as [t_l t_r t Ht_l Ht_r Ht];
    repeat remove_commuting_interleavings;
    transform_ensemble Ht_l;
    transform_ensemble Ht_r
  | ?x =>
    fail 1 "I don't know how to deconstruct " x
  end.

Tactic Notation "transform_ensemble" ident(e) := transform_ensemble e.

Ltac bruteforce :=
  lazymatch goal with
    [ |- -{{?P}} ?e {{?Q}} ] =>
    (* Preparations: *)
    let t := fresh "t" in
    let Ht := fresh "Ht" in
    intros t Ht; unfold_ht;
    transform_ensemble Ht
  end.

Section tests.
  Context `{StateSpace}.

  Goal forall (a b c d e f : TE) Q,
      trace_elems_commute a c ->
      trace_elems_commute a d ->
      trace_elems_commute b c ->
      trace_elems_commute b d ->
      -{{const True}} eq [a; b] -|| (eq [c; d] -|| eq [e; f]) {{Q}}.
  Proof.
    intros.
    bruteforce.
  Abort.
End tests.
