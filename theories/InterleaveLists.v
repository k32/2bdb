From Coq Require Import
     List
     Tactics
     Arith.Even.

Import ListNotations.

Section Permutation.
  Context {T : Type} (can_swap : T -> T -> Prop).
  Let L := list T.

  (* This datastructure reflects a _permutation_ that is needed to
  interleave lists: *)
  Inductive Permutation (l : L) : L -> Prop :=
  | perm_orig :
      Permutation l l
  | perm_shuf : forall l' r' a b,
      Permutation l (l' ++ a :: b :: r') ->
      can_swap a b ->
      Permutation l (l' ++ b :: a :: r').

  (* TODO: Prove completeness of this definition *)
End Permutation.

Section tests.
  Let comm a b := odd a /\ even b.

  Local Hint Constructors odd.
  Local Hint Constructors even.

  Let even2 : ~odd 2.
  Proof.
    intros H.
    apply (not_even_and_odd 2); auto.
  Qed.

  Local Hint Resolve even2.

  Goal Permutation comm [] [].
  Proof. constructor; auto. Qed.

  Goal Permutation comm [1; 3; 2; 4] [1; 2; 3; 4].
  Proof.
    replace [1; 2; 3; 4] with ([1] ++ 2 :: 3 :: [4]) by auto.
    constructor.
    - replace ([1] ++ [3; 2; 4]) with ([1; 3] ++ [2; 4]) by auto.
      constructor.
    - split; auto.
  Qed.

  Goal ~Permutation comm [2; 4] [4; 2].
  Proof.
    intros H.
    inversion H.
    assert (Hl' : l' = []).
    { destruct l'.
      + reflexivity.
      + repeat (destruct l'; inversion H0).
    }
    subst. simpl in *.
    inversion H0. subst.
    firstorder.
  Qed.
End tests.
