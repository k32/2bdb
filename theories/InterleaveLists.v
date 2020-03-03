From Coq Require Import
     List
     Tactics
     Arith.Even.

Import ListNotations.

Section defn.

Context {T : Type} (commute : T -> T -> Prop).
Let L := list T.

(* This datastructure reflects a _permutation_ that is needed to
interleave lists: *)
Inductive InterleaveLists (l r : L) : L -> Prop :=
| intl_orig :
    InterleaveLists l r (l ++ r)
| intl_shuf : forall l' r' a b,
    InterleaveLists l r (l' ++ a :: b :: r') ->
    commute a b ->
    InterleaveLists l r (l' ++ b :: a :: r').

(* TODO: Prove completeness of this defintion *)

End defn.

Section tests.

Let comm a b := odd a /\ even b.

Example example_interleaved_list_1 : InterleaveLists comm [] [] [].
Proof. constructor; auto. Qed.

Example example_interleaved_list_2 : InterleaveLists comm [1; 3] [2; 4] [1; 3; 2; 4].
Proof.
  replace [1; 3; 2; 4] with ([1; 3] ++ [2; 4]) by auto.
  constructor.
Qed.

Example example_interleaved_list_3 : InterleaveLists comm [1; 3] [2; 4] [1; 2; 3; 4].
Proof.
  replace [1; 2; 3; 4] with ([1] ++ 2 :: 3 :: [4]) by auto.
  constructor.
  - replace ([1] ++ [3; 2; 4]) with ([1; 3] ++ [2; 4]) by auto.
    constructor.
  - split; repeat constructor.
Qed.

End tests.
