(*** List iterators that preserve evidence that each processed element belongs to the list *)
(** Many proofs about processing keys in the [Storage.t] require some
sort of [In k (keys s)] hypothesis. This module defines versions of
common list processing functions that provide this hypothesis *)

From Coq Require
     Omega
     Vector
     List
     Program.

(* From Containers Require Import *)
(*      OrderedType *)
(*      OrderedTypeEx *)
(*      MapInterface *)
(*      MapFacts *)
(*      MapAVLInstance. *)

Import List ListNotations Omega Program.
Module Vec := Vector.
Module Fin := Fin.

(** Version of list foldr that preserves evidence that key passed
into the function is a member of the input list *)
Definition foldl' {A B} : forall (l : list A), (forall (a : A), In a l -> B -> B) -> B -> B.
  refine (fix foldl' l f acc0 :=
            (match l as l0 return (l = l0 -> B) with
             | [] => fun _ => acc0
             | a :: t => fun Hl => foldl' t _ (f a _ acc0)
             end) (eq_refl l)).
  - (* Create a copy of [f] typed so it works with [t]: *)
    intros a' Ha't acc'.
    apply (in_cons a a' t) in Ha't.
    rewrite <- Hl in Ha't.
    apply (f a' Ha't acc').
  - (* Prove that a is in l: *)
    rewrite Hl.
    apply in_eq.
Defined.

(** Proof of equivalence of [fold_left] with [foldl']. It can be used
to replace one with another for easier reasoning *)
Theorem fold_left_foldl' : forall {A B} (l : list A) (f : B -> A -> B) (a : B),
    fold_left f l a = foldl' l (fun elem HIn acc => f acc elem) a.
Proof.
  intros.
  generalize dependent a.
  induction l.
  - easy.
  - intros a'. simpl.
    rewrite IHl.
    reflexivity.
Qed.

(** Version of [forallb] that preserves the evidence that each element
passed into the predicate function [p] is a member of the list [l] *)
Definition forallb' {T} (l : list T) (p : forall k, In k l -> bool) :=
  @foldl' T bool l (fun k HIn acc => andb (p k HIn) acc) true.

(** Proof of equivalence of [forallb] and [forallb']. It can be used
to replace [forallb] with [forallb'] for easier reasoning *)
Theorem forallb_forallb' : forall {T} p (l : list T),
    forallb p l = forallb' l (fun k HIn => p k).
Proof.
  intros.
  induction l.
  - easy.
  - unfold forallb'. simpl.
    rewrite IHl.
    rewrite Bool.andb_true_r.
    rewrite Bool.andb_comm.
    destruct (p a).
    + rewrite Bool.andb_true_r. reflexivity.
    + rewrite Bool.andb_false_r.
      { clear IHl.
        induction l.
        - easy.
        - intros.
          simpl.
          rewrite Bool.andb_false_r.
          rewrite <-IHl.
          reflexivity.
      }
Qed.

Definition seq_vec : forall (N : nat), Vec.t (Fin.t N) N.
  intros N.
  induction N.
  - apply Vec.nil.
  - assert (aid : N < S N) by omega.
    apply Fin.of_nat_lt in aid.
    apply (Vec.cons _ aid N (Vec.map Fin.FS IHN)).
Defined.

Definition vec_same {A} (N : nat) (a : A) : Vec.t A N.
  induction N; constructor.
  - exact a.
  - assumption.
Defined.

(* Definition find' {K V} `{OrderedType K} (k : K) (m : Map[K,V]) (HIn : MapInterface.In k m) : V. *)
(*   refine ( *)
(*       let v := MapInterface.find k m in *)
(*       (match v as v' return v = v' -> V with *)
(*        | Some v => fun _ => v *)
(*        | None   => _ *)
(*        end) eq_refl). *)
(*   intros. *)
(*   exfalso. *)
(*   subst v. *)
(*   apply in_find_iff in HIn. *)
(*   contradiction. *)
(* Qed. *)
