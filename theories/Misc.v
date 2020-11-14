From Coq Require Import
     List
     Logic.Decidable
     Relations.

Ltac symm_not :=
  let H := fresh
  in unfold not;
     intros H;
     symmetry in H;
     generalize dependent H.

Open Scope list_scope.

Section forall_dec.
  Context {A} (P : A -> Prop).

  Definition Forall_dec l :
    (forall a, decidable (P a)) ->
    decidable (Forall P l).
  Proof.
    intros Hdec.
    induction l.
    { left. constructor. }
    { destruct IHl as [Hl|Hl].
      - destruct (Hdec a).
        + left. constructor; auto.
        + right. intros H'.
          inversion H'. auto.
      - right. intros H.
        inversion H. auto.
    }
  Defined.
End forall_dec.
