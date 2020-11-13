(*** List iterators that preserve evidence that each processed element belongs to the list *)
(** Many proofs about processing keys in the [Storage.t] require some
sort of [In k (keys s)] hypothesis. This module defines versions of
common list processing functions that provide this hypothesis *)

From Coq Require
     Vector
     List
     micromega.Lia
     Program.

Import List ListNotations Lia Program.
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
    rewrite IHl, Bool.andb_true_r, Bool.andb_comm.
    destruct (p a).
    + now rewrite Bool.andb_true_r.
    + rewrite Bool.andb_false_r.
      { clear IHl.
        induction l.
        - easy.
        - intros.
          simpl.
          rewrite Bool.andb_false_r.
          now rewrite <-IHl.
      }
Qed.

Definition seq_vec : forall (N : nat), Vec.t (Fin.t N) N.
  intros N.
  induction N.
  - apply Vec.nil.
  - assert (aid : N < S N) by constructor.
    apply Fin.of_nat_lt in aid.
    apply (Vec.cons _ aid N (Vec.map Fin.FS IHN)).
Defined.

Definition vec_same {A} (N : nat) (a : A) : Vec.t A N.
  induction N; constructor.
  - exact a.
  - assumption.
Defined.

Lemma shiftin_same {A} N (l : A) :
  (Vec.shiftin l (vec_same N l)) = vec_same (S N) l.
Proof.
  induction N.
  - reflexivity.
  - simpl. now rewrite IHN.
Qed.

Definition fin_to_nat {N} (n : Fin.t N) : nat :=
  match Fin.to_nat n with
    exist _ a C => a
  end.

Fixpoint last_fin (N : nat) : Fin.t (S N) :=
  match N with
  | 0 => Fin.F1
  | S n => Fin.FS (last_fin n)
  end.

Goal fin_to_nat (last_fin 0) = 0.
  reflexivity.
Qed.

Goal fin_to_nat (last_fin 3) = 3.
  reflexivity.
Qed.

Lemma last_fin_to_nat N :
  fin_to_nat (last_fin N) = N.
Abort. (* TODO *)

Lemma shiftin_nth_last {A} N (vec : Vec.t A N) (a : A) :
  Vec.nth (Vec.shiftin a vec) (last_fin N) = a.
Proof.
  now induction vec.
Qed.

Lemma shiftin_replace_last {A} N (vec : Vec.t A N) (a b : A) :
  Vec.replace (Vec.shiftin a vec) (last_fin N) b = Vec.shiftin b vec.
Proof.
  induction vec.
  - reflexivity.
  - simpl. now rewrite IHvec.
Qed.

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
