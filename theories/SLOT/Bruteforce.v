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

Ltac uniq_interleaving :=
  lazymatch goal with
  | ?e1 -|| ?e2 =>
    apply (uniq_ilv_correct te_comm_dec) in x
  | ?foo => idtac foo
  end.

Ltac bruteforce :=
  lazymatch goal with
    [ |- -{{?P}} ?e {{?Q}} ] =>
    uniq_interleaving
  end.

Section tests.
  Context `{StateSpace}.

  Goal forall (a b c d : TE) Q,
      trace_elems_commute a b ->
      trace_elems_commute c b ->
      trace_elems_commute a d ->
      trace_elems_commute c d ->
      -{{const True}} eq [a; c] -|| eq [b; d] {{Q}}.
  Proof.
    intros.
    bruteforce.
    match goal with
    | [H : UniqueInterleaving ?a ?b ?c |- _] =>
      inversion_ H; try contradiction
    end.
  Abort.
End tests.
