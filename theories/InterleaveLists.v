From Coq Require Import
     List
     Tactics.

Import ListNotations.

Section defns.

Context {T : Type} (prop_l prop_r : T -> Prop).
Let L := list T.

Inductive InterleavedList : L -> L -> L -> Prop :=
| tri_l_nil : forall l,
    Forall prop_r l ->
    InterleavedList [] l l
| tri_r_nil : forall l,
    Forall prop_l l ->
    InterleavedList l [] l
| tri_l_cons : forall a b x l,
    prop_l x ->
    InterleavedList a b l ->
    InterleavedList (x :: a) b (x :: l)
| tri_r_cons : forall a b x l,
    prop_r x ->
    InterleavedList a b l ->
    InterleavedList a (x :: b) (x :: l).

End defns.

Section tests.

Let P := fun (_:nat) => True.

Example example_interleaved_list_1 : InterleavedList P P [] [] [].
Proof. constructor; auto. Qed.

Example example_interleaved_list_2 : InterleavedList P P [1; 2] [3; 4] [1; 3; 2; 4].
Proof. repeat (constructor; auto). Qed.

Example example_interleaved_list_3 : InterleavedList P P [1; 2] [3; 4] [3; 1; 4; 2].
Proof. repeat (constructor; auto). Qed.

Example example_interleaved_list_4 : InterleavedList P P [1; 2] [3; 4] [4; 1; 3; 2].
Proof. repeat (constructor; auto). Fail easy. Abort.

Example example_interleaved_list_5 : InterleavedList P P [1; 2] [3; 4] [3; 1; 4; 4; 2].
Proof. repeat (constructor; auto). Fail easy. Abort.

End tests.
