(* LibTx, proofs about distributed systems design
   Copyright (C) 2019-2021  k32

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, version 3 of the License.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)
From Coq Require Import
     List
     Tactics
     Arith.Even
     Relations.

Import ListNotations.

Section defn.
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

  Hint Constructors Permutation : permutation.

  Lemma permut_cons a l1 l2 :
    Permutation l1 l2 ->
    Permutation (a :: l1) (a :: l2).
  Proof.
    intros.
    remember (a :: l1) as l1_.
    (* remember (a :: l2) as l2_. *)
    induction H; subst.
    - auto with permutation.
    - specialize (perm_shuf (a :: l1) (a :: l') r' a0 b IHPermutation H0) as Hs.
      assumption.
  Qed.

  (* TODO: Prove completeness of this definition *)

  Definition fixed (l : L) : Prop :=
    forall a b, In a l -> In b l -> ~can_swap a b.

  Lemma permut_fixed : forall l l',
      fixed l ->
      Permutation l l' ->
      l = l'.
  Proof with auto with *.
    intros.
    induction H0...
    exfalso.
    assert (Ha : In a l). { subst... }
    assert (Hb : In b l). { subst... }
    firstorder.
  Qed.

  Definition orthogonal (l1 l2 : L) : Prop :=
    forall a b, In a l1 -> In b l2 -> can_swap a b.

  Lemma permut_orth_concat_symm : forall (l1 l2 : L),
      orthogonal l1 l2 ->
      Permutation (l1 ++ l2) (l2 ++ l1).
  Abort.

  Lemma permut_trans : transitive L Permutation.
  Proof.
    intros l1 l2 l3 H12 H23.
    induction H23.
    - assumption.
    - constructor; assumption.
  Qed.

  Lemma permut_nil a : Permutation a [] -> a = [].
  Proof.
    intros H.
    inversion H.
    - reflexivity.
    - destruct l'; autorewrite with list; discriminate.
  Qed.

  Lemma permut_head' a b t :
    can_swap a b ->
    Permutation (a :: b :: t) (b :: a :: t).
  Proof.
    intros H.
    replace (a :: b :: t) with ([] ++ a :: b :: t) by reflexivity.
    replace (b :: a :: t) with ([] ++ b :: a :: t) by reflexivity.
    apply perm_shuf.
    - constructor.
    - assumption.
  Qed.

  Lemma permut_head a b t1 t2 :
    can_swap a b ->
    Permutation (b :: a :: t1) t2 ->
    Permutation (a :: b :: t1) t2.
  Proof.
    intros Hab H.
    induction H.
    - now apply permut_head'.
    - now apply perm_shuf.
  Qed.
End defn.

Hint Constructors Permutation : permutation.
Hint Resolve permut_trans : permutation.

Section tests.
  Let comm a b := odd a /\ even b.

  Hint Constructors odd : permutation.
  Hint Constructors even  : permutation.

  Let even2 : ~odd 2.
  Proof.
    intros H.
    apply (not_even_and_odd 2); auto with permutation.
  Qed.

  Hint Resolve even2.

  Goal Permutation comm [] [].
  Proof. constructor; auto. Qed.

  Goal Permutation comm [1; 3; 2; 4] [1; 2; 3; 4].
  Proof.
    replace [1; 2; 3; 4] with ([1] ++ 2 :: 3 :: [4]) by auto.
    constructor.
    - replace ([1] ++ [3; 2; 4]) with ([1; 3] ++ [2; 4]) by auto.
      constructor.
    - split; auto with permutation.
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
