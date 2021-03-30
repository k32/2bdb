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

(** * Storage interface *)
(** This module defines a "black box" storage engine *)
From Coq Require Import
     String
     List.

Import ListNotations.
Import Decidable.
Import Sumbool.

From LibTx Require Import
     Misc
     FoldIn
     EqDec.

Set Implicit Arguments.

Section defns.
  Context {K V : Type} `{HKeq_dec : EqDec K}.

  Class Storage t : Type :=
    { new : t;
      put : K -> V -> t -> t;
      get : K -> t -> option V;
      keys : t -> list K;
      delete : K -> t -> t;

      (* Axioms: *)
      new_empty : forall k, get k new = None;
      keep : forall s k v, get k (put k v s) = Some v;
      distinct : forall s k1 k2 v2,
          k1 <> k2 ->
          get k1 s = get k1 (put k2 v2 s);
      delete_keep : forall s k,
          get k (delete k s) = None;
      delete_distinct : forall s k1 k2,
          k1 <> k2 ->
          get k1 s = get k1 (delete k2 s);
      keys_some : forall s k,
          In k (keys s) <-> exists v, get k s = Some v;
    }.

  Section Operations.
    Context {T} `{HT_Storage : Storage T}.

    (** Total version of get *)
    Definition getT k (s : T) (H : In k (keys s)) : V.
      remember (get k s) as v.
      destruct v.
      - destruct Heqv. apply v.
      - exfalso. (* This is how one does exceptions in Coq :joy_cat: *)
        apply keys_some in H.
        rewrite <- Heqv in H.
        destruct H.
        inversion H.
    Defined.

    (** Atomically apply a function to all elements of the storage *)
    Definition a_map (f : V -> V) (s : T) : T :=
      let g k Hk acc :=
          let v0 := getT k s Hk
          in put k (f v0) acc
      in foldl' (keys s) g new.

    Definition forallS (s : T) (prop : forall (k : K), In k (keys s) -> Prop) : Prop :=
      let f k Hin acc := prop k Hin /\ acc
      in foldl' (keys s) f True.
  End Operations.
End defns.

Section Equality.
  Context {K V} {T1 T2} `{@Storage K V T1, Storage K V T2}.

  Inductive s_eq (s1 : T1) (s2 : T2) :=
  | s_eq_ : (forall k, get k s1 = get k s2) -> s_eq s1 s2.
End Equality.

Notation "s1 =s= s2" := (s_eq s1 s2) (at level 50).
Hint Constructors s_eq : storage.

Section props.
  Context {K V : Type} `{HKeq_dec : EqDec K} {T} `{HT_Storage : @Storage K V T}.

  Lemma s_eq_self : forall (s : T), s =s= s.
  Proof.
    firstorder.
  Qed.

  Lemma new_keys_empty : keys new = [].
  Proof.
    remember (keys new) as k.
    destruct k.
    - reflexivity.
    - exfalso.
      assert (Hk : In k (keys new)).
      { rewrite <-Heqk. apply in_eq. }
      apply keys_some in Hk.
      destruct Hk as [v nonsense].
      specialize (new_empty k) as empty.
      rewrite nonsense in empty.
      easy.
  Qed.

  Lemma empty_keys_eq_new s :
    Storage.keys s = [] ->
    s =s= new.
  Proof.
    intros H. constructor. intros k.
    rewrite new_empty.
    specialize (keys_some s k) as nonsense. rewrite H in nonsense.
    destruct (get k s).
    2:{ reflexivity. }
    exfalso.
    assert (H2 : exists v0 : V, Some v = Some v0) by now exists v.
    apply nonsense in H2.
    inversion H2.
  Qed.

  Lemma put_eq_eq : forall (s1 s2 : T) k v,
      s1 =s= s2 ->
      put k v s1 =s= put k v s2.
  Proof.
    intros s1 s2 k v Heq.
    constructor.
    intros x.
    destruct (eq_dec x k) as [H|H].
    - subst. repeat rewrite keep. reflexivity.
    - repeat rewrite <- distinct;
      firstorder.
  Qed.

  Lemma put_same : forall (s : T) k v,
      get k s = Some v ->
      s =s= put k v s.
  Proof.
    intros s k v Hkv.
    constructor.
    intros x.
    destruct (eq_dec x k) as [H|H].
    - subst. rewrite keep, Hkv. reflexivity.
    - rewrite <-distinct; easy.
  Qed.

  Lemma put_distict_comm : forall (s : T) k1 k2 v1 v2,
      k1 <> k2 ->
      put k2 v2 (put k1 v1 s) =s= put k1 v1 (put k2 v2 s).
  Proof.
    intros s k1 k2 v1 v2 H12.
    apply s_eq_.
    intros k.
    destruct (eq_dec k k1) as [|Hnk1]; subst.
    - rewrite <-distinct;
      repeat rewrite keep;
      easy.
    - destruct (eq_dec k k2) as [|Hnk2]; subst.
      + replace (get k2 (put k1 v1 (put k2 v2 s))) with (get k2 (put k2 v2 s)).
        repeat rewrite keep.
        reflexivity.
        apply distinct; auto.
      + repeat rewrite <- distinct; auto.
  Qed.

  Theorem keys_none : forall (s : T) k,
      ~In k (keys s) -> get k s = None.
  Proof.
    intros.
    specialize (keys_some s k) as [Hs Hs_rev].
    destruct (get k s).
    - exfalso. apply H. apply Hs_rev. exists v. reflexivity.
    - reflexivity.
  Qed.

  Theorem keys_some' : forall (s : T) k v,
      Some v = get k s -> In k (keys s).
  Proof.
    intros.
    apply keys_some. exists v. easy.
  Qed.
End props.

Section WriteLog.
  Context {K V : Type} `{HKeq_dec : EqDec K} {T} `{HT_Storage : @Storage K V T}.

  Inductive Wlog_elem :=
  | wl_write : K -> V -> Wlog_elem
  | wl_delete : K -> Wlog_elem.

  Definition Wlog_elem_apply (s : T) (l : Wlog_elem) : T :=
    match l with
    | wl_write k v => put k v s
    | wl_delete k => delete k s
    end.

  Definition Wlog := list Wlog_elem.

  Definition Wlog_apply (l : Wlog) (s : T) :=
    fold_left Wlog_elem_apply l s.

  Definition Wlog_has_key (k : K) (l : Wlog) : Prop :=
    In k (map (fun x => match x with
                     | wl_write k _ => k
                     | wl_delete k => k
                     end) l).

  (* D'oh! This _should_ be somewhere in the standard library... *)
  Lemma sumbool_dec : forall A, { A } + { ~ A } ->
                           decidable A.
  Proof.
    intros A H.
    destruct H; [left | right]; assumption.
  Qed.

  Lemma Wlog_has_key_dec : forall  k (l : Wlog),
      decidable (Wlog_has_key k l).
  Proof.
    intros k l.
    unfold Wlog_has_key.
    induction l as [|e t IH]; simpl.
    - apply dec_False.
    - apply dec_or.
      + apply sumbool_dec, eq_dec.
      + apply IH.
  Qed.

  Inductive Wlog_nodup : Wlog -> Wlog -> Prop :=
  | wse0 : Wlog_nodup [] []
  | wse1 : forall l l' t k v,
      l = (wl_write k v) :: t ->
      ~Wlog_has_key k t ->
      Wlog_nodup t l' ->
      Wlog_nodup l ((wl_write k v) :: l')
  | wse2 : forall l l' t k,
      l = (wl_delete k) :: t ->
      ~Wlog_has_key k t ->
      Wlog_nodup t l' ->
      Wlog_nodup l ((wl_delete k) :: l').

  Lemma Wlog_has_key_rev : forall (l : Wlog) k,
      Wlog_has_key k l <-> Wlog_has_key k (rev l).
  Proof.
    intros l k.
    unfold Wlog_has_key.
    rewrite map_rev.
    apply in_rev.
  Qed.

  Ltac wlog_app_simpl_ NEQ :=
    simpl; unfold Wlog_apply;
    repeat rewrite fold_left_app;
    simpl;
    subst;
    repeat rewrite keep;
    repeat rewrite <-distinct by NEQ;
    repeat rewrite delete_keep;
    repeat rewrite <-delete_distinct by NEQ.

  Tactic Notation "wlog_app_simpl" "by" tactic2(x) :=
    wlog_app_simpl_ x.

  Tactic Notation "wlog_app_simpl" :=
    wlog_app_simpl_ fail.

  Hint Constructors s_eq : storage.

  Ltac unfold_s_eq k :=
    constructor;
    intros k.

  Ltac unfold_s_eq_in k :=
    destruct k as [k].

  Tactic Notation "unfold_s_eq" "in" ident(k) :=
    unfold_s_eq_in k.

  Tactic Notation "unfold_s_eq" "as" ident(k) :=
    unfold_s_eq k.

  Ltac rev_wlog_induction l k v t IH :=
    rewrite <-(rev_involutive l) in *;
    induction (rev l) as [|[k v|k] t IH]; try easy.

  Tactic Notation "rev_wlog_induction" hyp(l) "as" ident(k) ident(v) ident(t) ident(IH) :=
    rev_wlog_induction l k v t IH.

  Ltac has_key_rev_simpl H :=
    simpl in H;
    rewrite Wlog_has_key_rev, rev_app_distr, rev_involutive in H;
    simpl in H;
    unfold Wlog_has_key in H;
    simpl in H.

  Tactic Notation "has_key_rev_simpl" "in" hyp(H) := has_key_rev_simpl H.

  Hint Unfold Wlog_apply : storage.
  Hint Unfold Wlog_has_key : storage.

  Hint Extern 3 => symm_not : storage.
  Hint Extern 4 => rewrite <-Wlog_has_key_rev : storage.
  Hint Extern 4 => rewrite keep : storage.
  Hint Extern 4 => rewrite delete_keep : storage.
  Hint Extern 4 => destruct (eq_dec _ _ _) : storage.
  Hint Resolve s_eq_self : storage.

  Lemma Wlog_apply_same : forall (l : Wlog) (s1 s2 : T),
      s1 =s= s2 ->
      Wlog_apply l s1 =s= Wlog_apply l s2.
  Proof.
    intros l s1 s2 H.
    rev_wlog_induction l as k v t IH;
      unfold_s_eq in IH;
      unfold_s_eq as k';
      destruct (eq_dec k' k) as [Hkk|Hkk];
      wlog_app_simpl by apply Hkk;
      easy.
  Qed.

  Lemma Wlog_ignore : forall (l : Wlog) s k,
      ~ Wlog_has_key k l ->
      get k s = get k (Wlog_apply l s).
  Proof.
    intros l s k H.
    rev_wlog_induction l as k' _v t IH;
      unfold Wlog_apply in IH;
      wlog_app_simpl;
      has_key_rev_simpl in H;
      [rewrite <-distinct by auto | rewrite <-delete_distinct by auto];
      firstorder;
      rewrite <-IH;
      auto with storage.
  Qed.

  Lemma Wlog_ignore_cons : forall (l : Wlog) s k1 k2 v,
      k1 <> k2 ->
      get k1 (Wlog_apply l (put k2 v s)) = get k1 (Wlog_apply l s).
  Proof with auto with storage.
    intros l s k1 k2 v H.
    rev_wlog_induction l as ak av t IH.
    - simpl. rewrite <-distinct.
      reflexivity.
      assumption.
    - wlog_app_simpl.
      destruct (eq_dec ak k1) as [Hak|Hak].
      + subst...
      + repeat rewrite <-distinct in * by auto...
    - wlog_app_simpl.
      destruct (eq_dec ak k1) as [Hak|Hak].
      + subst...
      + repeat rewrite <-delete_distinct by auto...
  Qed.

  Lemma Wlog_ignore_cons_del : forall (l : Wlog) s k1 k2,
      k1 <> k2 ->
      get k1 (Wlog_apply l (delete k2 s)) = get k1 (Wlog_apply l s).
  Proof with auto with storage.
    intros l s k1 k2 H.
    rev_wlog_induction l as ak av t IH.
    - simpl. rewrite <-delete_distinct.
      reflexivity.
      assumption.
    - wlog_app_simpl.
      destruct (eq_dec ak k1) as [Hak|Hak].
      + subst...
      + repeat rewrite <-distinct in * by auto...
    - wlog_app_simpl.
      destruct (eq_dec ak k1) as [Hak|Hak].
      + subst...
      + repeat rewrite <-delete_distinct by auto...
  Qed.

  Lemma Wlog_nodup_has_key : forall k (l1 l2 : Wlog),
      Wlog_nodup l1 l2 ->
      Wlog_has_key k l1 <-> Wlog_has_key k l2.
  Proof.
    intros k l1 l2 H.
    induction H; split; intros Hinv;
      try easy;
      subst; simpl in *;
      unfold Wlog_has_key; simpl;
      unfold Wlog_has_key in Hinv; simpl in Hinv;
      destruct Hinv;
      try (left; assumption);
      apply IHWlog_nodup in H; right; assumption.
  Qed.

  Theorem Wlog_significant_entries :
    forall  (l l' : Wlog) s,
      Wlog_nodup l l' ->
      Wlog_apply l s =s= Wlog_apply l' s.
  Proof.
    intros l l' s H.
    induction H; subst; auto with storage;
      unfold_s_eq as k';
      unfold_s_eq in IHWlog_nodup;
      apply (Wlog_nodup_has_key k') in H1;
      simpl;
      destruct (eq_dec k k') as [Heq|Hneq]; subst;
        (* [k = k'] *)
      try (rewrite <-Wlog_ignore with (l := t) by auto;
           rewrite <-Wlog_ignore with (l := l') by firstorder;
           auto).
      (* [k <> k'] *)
    - repeat rewrite Wlog_ignore_cons; auto.
    - repeat rewrite Wlog_ignore_cons_del; auto.
  Qed.

  (* Dump a consistent snapshot to a wlog: *)
  Definition snap2ops (s : T) : Wlog :=
    map' (keys s) (fun k Hk => wl_write k (getT k s Hk)).

  Lemma snapshot_replicate_as_wlog : forall (s : T),
      Wlog_apply (snap2ops s) new =s= s.
  Proof.
    intros s.
    unfold snap2ops.
    set (l := keys s).
  Abort.
End WriteLog.

Module ListStorage.
  Section defns.
    Context {K V : Type} `{HKeq_dec : EqDec K}.

    Definition t := list (K * V).

    Fixpoint list_delete (k : K) s : t :=
      match s with
      | [] => []
      | (k', v) :: t =>
        if eq_dec k k'
        then list_delete k t
        else (k', v) :: list_delete k t
      end.

    Definition list_put (k : K) (v : V) s : t :=
      (k, v) :: (list_delete k s).

    Fixpoint list_get (k : K) (s : t) : option V :=
      match s with
      | [] => None
      | (k', v) :: t =>
        if eq_dec k' k
        then Some v
        else list_get k t
      end.

    Fixpoint list_keys (s : t) : list K :=
      match s with
      | [] => []
      | (k, _) :: t => k :: list_keys t
      end.

    Let list_new_empty : forall k,
        list_get k [] = None.
    Proof.
      easy.
    Qed.

    Let list_keep : forall (s : t) (k : K) (v : V),
        list_get k (list_put k v s) = Some v.
    Proof.
      intros.
      simpl. destruct (eq_dec k k); easy.
    Qed.

    Let list_delete_keep : forall (s : t) k,
        list_get k (list_delete k s) = None.
    Proof with try easy.
      intros.
      induction s as [|[k1 v] t IH]...
      simpl.
      destruct (eq_dec k k1)...
      simpl.
      rewrite IH.
      destruct (eq_dec k1 k) as [H|H]; try symmetry in H...
    Qed.

    Let list_delete_distinct : forall (s : t) (k1 k2 : K),
        k1 <> k2 ->
        list_get k1 s = list_get k1 (list_delete k2 s).
    Proof with autorewrite with eq_dec; auto.
      intros.
      induction s...
      destruct a as [k v].
      destruct (eq_dec k k1) as [|Hneq_k_k1]; subst.
      - simpl in *...
        destruct (eq_dec k2 k1) as [Heq12|Hneq12].
        + subst. now contradiction H.
        + simpl...
      - simpl...
        destruct (eq_dec k k1); destruct (eq_dec k2 k); firstorder.
        simpl.
        destruct (eq_dec k k1); firstorder.
    Qed.

    Let list_distinct : forall (s : t) (k1 k2 : K) (v2 : V),
        k1 <> k2 ->
        list_get k1 s = list_get k1 (list_put k2 v2 s).
    Proof.
      intros. simpl.
      destruct (eq_dec k2 k1) as [He|He].
      - symmetry in He. easy.
      - rewrite <-list_delete_distinct; easy.
    Qed.

    Let list_keys_some : forall (s : t) k,
        In k (list_keys s) <-> exists v, list_get k s = Some v.
    Proof with autorewrite with eq_dec; auto.
      intros.
      split; intros H.
      { induction s; firstorder.
        destruct a as [k' v].
        destruct (eq_dec k k'); subst.
        - exists v. simpl...
        - destruct IHs.
          + simpl in H. destruct H as [H|H]...
            symmetry in H.
            now contradiction n.
          + exists x.
            simpl.
            destruct (eq_dec k' k)...
            symmetry in e. firstorder.
      }
      { destruct H.
        induction s.
        - unfold list_get. simpl in *. inversion H.
        - destruct a as [k' v].
          simpl in *.
          destruct (eq_dec k' k); auto.
      }
    Qed.

    Global Instance listStorage : @Storage K V (list (K * V)) :=
      {| new := [];
         put := list_put;
         get := list_get;
         keys := list_keys;
         delete := list_delete;
         new_empty := list_new_empty;
         keep := list_keep;
         distinct := list_distinct;
         delete_keep := list_delete_keep;
         delete_distinct := list_delete_distinct;
         keys_some := list_keys_some;
      |}.
  End defns.
End ListStorage.
