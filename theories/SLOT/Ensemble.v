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

(** * Ensembles of traces

    Trace ensembles play one of central roles in SLOT, because from
    SLOT point of view any system is nothing but a collection of event
    traces that it can produce.

 *)
From Coq Require
     Program.Basics
     List
     Relations.

Import List ListNotations Basics Relations.

From Hammer Require Import
     Tactics.

From LibTx Require Import
     FoldIn
     Misc
     EventTrace
     Permutation
     SLOT.Hoare.

Open Scope hoare_scope.

Global Arguments Vec.nil {_}.
Global Arguments Vec.cons {_}.

Section defn.
  Context {S TE} `{StateSpace S TE}.

  Definition TraceEnsemble := list TE -> Prop.

  (** Hoare logic of trace ensembles consists of a single rule: *)
  Definition EHoareTriple (pre : S -> Prop) (g : TraceEnsemble) (post : S -> Prop) :=
    forall t, g t ->
         {{ pre }} t {{ post}}.

  (** Concatenation of trace ensembles represents systems that run
  sequentially: *)
  Inductive TraceEnsembleConcat (e1 e2 : TraceEnsemble) : TraceEnsemble :=
  | et_concat : forall t1 t2, e1 t1 -> e2 t2 -> TraceEnsembleConcat e1 e2 (t1 ++ t2).

  (** Set of all possible interleaving of two traces is a trace
  ensemble. As we later prove in [interleaving_to_permutation], this
  definition is dual to [Permutation]. *)
  Inductive Interleaving : list TE -> list TE -> TraceEnsemble :=
  | ilv_cons_l : forall te t1 t2 t,
      Interleaving t1 t2 t ->
      Interleaving (te :: t1) t2 (te :: t)
  | ilv_cons_r : forall te t1 t2 t,
      Interleaving t1 t2 t ->
      Interleaving t1 (te :: t2) (te :: t)
  | ilv_nil : Interleaving [] [] [].

  Section tests.
    (** Let's briefly check that our definition of [Interleaving] has
    desired properties: *)
    Variables (a b c d : TE).
    Goal Interleaving [a;b] [c;d] [a;b;c;d].
    Proof. repeat constructor. Qed.

    Goal Interleaving [a;b] [c;d] [a;c;b;d].
    Proof. repeat constructor. Qed.

    Goal Interleaving [a;b] [c;d] [a;c;d;b].
    Proof. repeat constructor. Qed.

    Goal Interleaving [a;b] [c;d] [c;a;b;d].
    Proof. repeat constructor. Qed.

    Goal Interleaving [a;b] [c;d] [c;a;d;b].
    Proof. repeat constructor. Qed.

    Goal Interleaving [a;b] [c;d] [c;d;a;b].
    Proof. repeat constructor. Qed.

    Goal a<>b -> b<>c -> not(Interleaving [a;b] [c;d] [b;a;c;d]).
    Proof.
      intros Hab Hac Hint.
      inversion_ Hint.
    Qed.
  End tests.

  Definition vec_modify {N} {A} (v : Vec.t A N) i (f : A -> A) :=
    Vec.replace v i (f (Vec.nth v i)).

  (* Left-biased version of [Interleaving] that doesn't make
  distinction between schedulings of commuting elements: *)
  Inductive UniqueInterleaving : list TE -> list TE -> TraceEnsemble :=
  | uilv_cons_l : forall l t1 t2 t,
      UniqueInterleaving t1 t2 t ->
      UniqueInterleaving (l :: t1) t2 (l :: t)
  | uilv_cons_r1 : forall l r t1 t2 t,
      ~trace_elems_commute l r ->
      UniqueInterleaving (l :: t1) t2 (l :: t) ->
      UniqueInterleaving (l :: t1) (r :: t2) (r :: l :: t)
  | uilv_cons_r2 : forall r1 r2 t1 t2 t,
      UniqueInterleaving t1 (r1 :: t2) (r1 :: t) ->
      UniqueInterleaving t1 (r2 :: r1 :: t2) (r2 :: r1 :: t)
  | uilv_nil : forall t, UniqueInterleaving [] t t.

  (** Two systems running in parallel are represented by interleaving
  of all possible traces that could be produced by these systems: *)
  Inductive Parallel (e1 e2 : TraceEnsemble) : TraceEnsemble :=
  | ilv_par : forall t1 t2 t,
      e1 t1 -> e2 t2 ->
      Interleaving t1 t2 t ->
      Parallel e1 e2 t.

  Definition EnsembleInvariant (prop : S -> Prop) (E : TraceEnsemble) : Prop :=
    forall (t : list TE), E t -> TraceInvariant prop t.

End defn.

Hint Constructors Interleaving Parallel TraceEnsembleConcat : slot.

Delimit Scope hoare_scope with hoare.
Notation "'-{{' a '}}' e '{{' b '}}'" := (EHoareTriple a e b)(at level 40) : hoare_scope.
Notation "'-{{}}' e '{{' b '}}'" := (EHoareTriple (const True) e b)(at level 40) : hoare_scope.
Notation "'-{{}}' e '{{}}'" := (forall t, e t -> exists s s', ReachableByTrace s t s')(at level 38) : hoare_scope.
Infix "->>" := (TraceEnsembleConcat) (at level 100) : hoare_scope.
Infix "-||" := (Parallel) (at level 101) : hoare_scope.

Section props.
  Context {S TE} `{HsspS : StateSpace S TE}.
  Let T := list TE.

  (* Lemma ensemble_invariant_sublist : forall prop E a b c, *)
  (*     a ++ b = c -> *)
  (*     E c -> *)
  (*     EnsembleInvariant prop E -> *)
  (*     EnsembleInvariant prop E a. *)

  Lemma e_hoare_concat : forall pre mid post e1 e2,
      -{{pre}} e1 {{mid}} ->
      -{{mid}} e2 {{post}} ->
      -{{pre}} e1 ->> e2 {{post}}.
  Proof.
    intros *. intros H1 H2 t Ht.
    destruct Ht.
    apply hoare_concat with (mid0 := mid); auto.
  Qed.

  Section perm_props.
    Lemma interleaving_symm : forall {TE} (t1 t2 t : list TE),
      Interleaving t1 t2 t ->
      Interleaving t2 t1 t.
    Proof.
      intros.
      induction H; constructor; auto.
    Qed.

    Lemma interleaving_nil : forall {ctx} t1 t2,
        @Interleaving ctx [] t1 t2 ->
        t1 = t2.
    Proof.
      intros.
      remember [] as t.
      induction H; subst; try easy.
      rewrite IHInterleaving; auto.
    Qed.

    Lemma interleaving_par_head : forall (t1 t2 t : list TE),
        Interleaving t1 t2 t ->
        exists t' t1_hd t1_tl,
          t = t1_hd ++ t' /\ t1 = t1_hd ++ t1_tl /\ Interleaving t1_tl t2 t'.
    Proof with auto with slot; firstorder.
      intros *. intros Hint.
      induction Hint.
      - destruct IHHint as [t' [t1_hd [t1_tl IH]]].
        exists t'. exists (te :: t1_hd). exists (t1_tl).
        firstorder; subst; reflexivity.
      - exists (te :: t). exists []. exists t1...
      - exists []. exists []. exists []...
    Qed.

    Lemma e_hoare_par_ergo_seq : forall e1 e2 P Q,
      -{{P}} e1 -|| e2 {{Q}} ->
      -{{P}} e1 ->> e2 {{Q}}.
    Proof.
      intros. intros t Hseq.
      eapply H. clear H.
      destruct Hseq as [t1 t2].
      eapply ilv_par; eauto with slot.
      clear H H0.
      induction t1; induction t2; simpl; auto with slot.
    Qed.

    Lemma e_hoare_par_symm : forall e1 e2 P Q,
        -{{P}} e1 -|| e2 {{Q}} ->
        -{{P}} e2 -|| e1 {{Q}}.
    Proof.
      intros. intros t Hpar.
      eapply H. clear H.
      destruct Hpar as [t1 t2 t H1 H2 Hint].
      apply interleaving_symm in Hint.
      eapply ilv_par; eauto.
    Qed.

    Lemma interl_app_tl : forall (b c__hd c__tl t : list TE),
        Interleaving b c__tl t ->
        Interleaving b (c__hd ++ c__tl) (c__hd ++ t).
    Proof.
      intros.
      induction c__hd; simpl; auto with slot.
    Qed.

    Lemma interl_app_hd : forall (a c__hd c__tl t : list TE),
        Interleaving a c__hd t ->
        Interleaving a (c__hd ++ c__tl) (t ++ c__tl).
    Proof with simpl; auto with slot.
      intros.
      induction H...
      induction c__tl...
    Qed.

    Example no_swapping_heads_is_not_always_impossible : forall (a b c : TE),
        a <> b -> b <> c -> a <> c ->
        exists t,
          Interleaving [a; b] [c] t ->
          ~Interleaving [b] [a; c] t.
    Proof.
      intros a b c Hab Hbc Hac.
      exists [c; a; b]. intros H H'.
      repeat match goal with
             | [H : Interleaving _ _ _ |- _] => inversion H; clear H
             end; subst; contradiction.
    Qed.

    Lemma interleaving_nil_r : forall (a b : list TE),
        Interleaving a b [] ->
        a = [] /\ b = [].
    Proof.
      intros.
      remember [] as t.
      destruct H; try discriminate; firstorder.
    Qed.

    Theorem e_hoare_inv_par : forall e1 e2 prop,
        EnsembleInvariant prop e1 ->
        EnsembleInvariant prop e2 ->
        EnsembleInvariant prop (e1 -|| e2).
    Proof with constructor; auto.
      intros e1 e2 prop He1 He2.
      intros t [t1 t2 t12 Ht1 Ht2 Hint].
      specialize (He1 t1 Ht1). clear Ht1.
      specialize (He2 t2 Ht2). clear Ht2.
      induction Hint; try assumption.
      - inversion_ He1...
      - inversion_ He2...
    Qed.

    Lemma e_hoare_inv_seq : forall e1 e2 prop,
        EnsembleInvariant prop e1 ->
        EnsembleInvariant prop e2 ->
        EnsembleInvariant prop (e1 ->> e2).
    Proof.
      intros e1 e2 prop He1 He2.
      intros t [t1 t2 Ht1 Ht2].
      specialize (He1 t1 Ht1). clear Ht1.
      specialize (He2 t2 Ht2). clear Ht2.
      induction t1.
      - easy.
      - inversion He1.
        constructor; auto.
    Qed.

    Lemma interleaving_par_seq : forall (a b c t : list TE),
        Interleaving (a ++ b) c t ->
        exists c1 c2 t1 t2,
          t1 ++ t2 = t /\ c1 ++ c2 = c /\
          Interleaving a c1 t1 /\ Interleaving b c2 t2.
    Proof with auto with slot; firstorder.
      intros.
      remember (a ++ b) as ab.
      generalize dependent b.
      generalize dependent a.
      induction H as [te ab c t H IH| te ab c t H IH| ]; intros.
      - destruct a; [destruct b; inversion_ Heqab | idtac]; simpl in *.
        + exists []. exists c. exists []. exists (t0 :: t)...
        + inversion Heqab. subst.
          specialize (IH a b eq_refl).
          destruct IH as [c1 [c2 [t1 [t2 [Ht [Ht2 [Hint1 Hint2]]]]]]]; subst.
          exists c1. exists c2. exists (t0 :: t1). exists t2...
      - specialize (IH a b Heqab).
        destruct IH as [c1 [c2 [t1 [t2 [Ht [Ht2 [Hint1 Hint2]]]]]]]; subst.
        exists (te :: c1). exists c2. exists (te :: t1). exists t2...
      - symmetry in Heqab. apply app_eq_nil in Heqab.
        destruct Heqab. subst.
        exists []. exists []. exists []. exists []...
    Qed.

    Lemma e_hoare_par_seq1 : forall e1 e2 e P Q,
        (* -{{P}} e1 -|| e {{Q}} -> *)
        (* -{{Q}} e2 -|| e {{Q}} -> *)
        (* -{{P}} e1 ->> e2 {{Q}} -> *)
        -{{P}} e1 ->> e2 -|| e {{Q}}.
    Proof.
      intros *. (* intros Hpar1 Hpar2 Hseq. *)
      intros t Ht.
      destruct Ht as [t12 t_ t H12 Ht_ Hint].
      destruct H12 as [t1 t2 H1 H2].
      (*   t_, t, t1, t2 : list TE
           H1 : e1 t1
           H2 : e2 t2
           Ht_ : e t_
           Hint : Interleaving (t1 ++ t2) t_ t
       *)
    Abort.

    Lemma e_hoare_par_seq : forall e1 e2 e P Q R,
        -{{P}} e1 -|| e {{Q}} ->
        -{{Q}} e2 -|| e {{R}} ->
        -{{P}} e1 ->> e2 -|| e {{R}}.
    Proof.
      intros *. intros H1 H2 t Ht s s' Hss' Hpre.
      destruct Ht as [t1 t2 t Ht1 Ht2 Hint].
    Abort. (* This is wrong? *)
  End perm_props.

  Section ensemble_equiv.
    Context (e1 e2 : @TraceEnsemble TE).

    Definition sufficient_replacement :=
      forall t s s', e1 t ->
                ReachableByTrace s t s' ->
                exists t', e2 t' /\ ReachableByTrace s t' s'.

    Definition sufficient_replacement_p :=
      forall t, e1 t ->
           exists t', e2 t' /\ Permutation trace_elems_commute t t'.

    Theorem ht_sufficient_replacement P Q :
      sufficient_replacement ->
      -{{P}} e2 {{Q}} -> -{{P}} e1 {{Q}}.
    Proof.
      intros He2 H t Ht s s' Hls Hpre.
      destruct (He2 t s s' Ht Hls) as [t' [Ht' Hls']].
      eapply H; eauto.
    Qed.

    Lemma comm_perm_sufficient_replacement :
      sufficient_replacement_p ->
      sufficient_replacement.
    Proof.
      intros H t s s' Ht Hls.
      destruct (H t Ht) as [t' [Ht' Hperm]].
      eapply ht_comm_perm in Hperm; eauto.
    Qed.
  End ensemble_equiv.

  Lemma sufficient_replacement_p_trans :
    transitive (@TraceEnsemble TE) sufficient_replacement_p.
  Proof.
    intros e1 e2 e3 H12 H23. intros t Ht.
    apply H12 in Ht. destruct Ht as [t' [Ht' Hperm']].
    apply H23 in Ht'. destruct Ht' as [t'' [Ht'' Hperm'']].
    exists t''. split.
    - assumption.
    - eapply permut_trans; eauto.
  Qed.

  Section uniq_correct.
    Context (Hcomm_dec : forall a b, trace_elems_commute a b \/ not (trace_elems_commute a b)).

    Lemma uniq_ilv_ergo_ilv t1 t2 t :
      UniqueInterleaving t1 t2 t ->
      Interleaving t1 t2 t.
    Proof.
      intros.
      induction H; try constructor; auto.
      induction t; constructor.
      easy.
    Qed.

    Lemma uilv_nil_l : forall t, UniqueInterleaving t [] t.
    Proof.
      now induction t; constructor.
    Qed.

    Fixpoint uilv_append_r te (t1 t2 t : list TE)
             (Ht : UniqueInterleaving t1 t2 t)
             (s s' s'' : S) (Hls : ReachableByTrace s' t s'')
             (Hte : s ~[te]~> s')
             {struct Ht} :
      exists t', UniqueInterleaving t1 (te :: t2) t' /\ ReachableByTrace s t' s''.
    Proof with repeat (try assumption ; constructor); auto.
      destruct Ht.
      - long_step Hls.
        destruct (Hcomm_dec l te) as [Hcomm|Hcomm].
        + assert (Hx : ReachableByTrace s [te; l] s0).
          { forward s'...
            forward s0...
          }
          eapply Hcomm in Hx.
          repeat long_step Hx. subst.
          eapply uilv_append_r in Hcr1; eauto.
          destruct Hcr1 as [t' [Ht' Hls']].
          exists (l :: t').
          split...
          forward s1...
        + exists (te :: l :: t).
          split...
          forward s'...
          forward s0...
      - exists (te :: r :: l :: t).
        split...
        forward s'...
      - exists (te :: r2 :: r1 :: t).
        split...
        forward s'...
      - exists (te :: t).
        split...
        forward s'...
    Qed.

    Fixpoint canonicalize_ilv (t1 t2 t : list TE) (Ht : Interleaving t1 t2 t)
                              (s s' : S) (Hls : ReachableByTrace s t s')
                              {struct Ht} :
      exists t', UniqueInterleaving t1 t2 t' /\ ReachableByTrace s t' s'.
    Proof with repeat constructor; auto.
      destruct Ht; try long_step Hls.
      - destruct (canonicalize_ilv t1 t2 t Ht s0 s' Hls) as [t' [Ht' Hls']].
        exists (te :: t').
        split...
        forward s0...
      - destruct (canonicalize_ilv t1 t2 t Ht s0 s' Hls) as [t' [Ht' Hls']].
        apply (uilv_append_r te t1 t2 t' Ht' s s0 s' Hls' Hcr).
      - exists []...
    Defined.

    Lemma uniq_ilv_correct P Q t1 t2 :
      -{{P}} UniqueInterleaving t1 t2 {{Q}} ->
      -{{P}} Interleaving t1 t2 {{Q}}.
    Proof.
      intros Huilv t Ht. unfold_ht.
      destruct (canonicalize_ilv t1 t2 t Ht s_begin s_end Hls) as [t' [Ht' Hls']].
      eapply Huilv; eauto.
    Qed.
  End uniq_correct.
End props.

Ltac clear_equations :=
  repeat match goal with
           [H: ?a = ?a |- _] => clear H
         end.

Ltac destruct_interleaving H :=
  match type of H with
    Interleaving ?a ?b ?c =>
    let a0 := fresh in
    let b0 := fresh in
    let Ha := fresh in
    let Hb := fresh in
    remember a as a0 eqn:Ha; remember b as b0 eqn:Hb;
    destruct H; inversion Ha; inversion Hb; subst; try discriminate;
    clear_equations
  end.

Ltac destruct_uinterleaving H :=
  match type of H with
    UniqueInterleaving ?a ?b ?c =>
    let a0 := fresh in
    let b0 := fresh in
    let Ha := fresh in
    let Hb := fresh in
    remember a as a0 eqn:Ha; remember b as b0 eqn:Hb;
    destruct H; inversion Ha; inversion Hb; subst; try discriminate;
    clear_equations
  end.

Ltac interleaving_nil :=
  repeat match goal with
         | [H: Interleaving [] ?t1 ?t |- _] => apply interleaving_nil in H; try subst t
         | [H: Interleaving ?t1 [] ?t |- _] => apply interleaving_symm, interleaving_nil in H; try subst t
         end.

Hint Extern 4 => interleaving_nil : slot.

Ltac unfold_interleaving H tac :=
  simpl in H;
  lazymatch type of H with
  | Interleaving [] _ _ =>
    apply interleaving_nil in H;
    try (rewrite <-H in *; clear H);
    repeat tac
  | Interleaving _ [] _ =>
    apply interleaving_symm, interleaving_nil in H;
    try (rewrite <-H in *; clear H);
    repeat tac
  | Interleaving ?tl ?tr ?t =>
    let te := fresh "te" in
    let tl' := fresh "tl" in
    let tr' := fresh "tr" in
    let t := fresh "t" in
    (* stuff that we need in order to eliminate wrong hypotheses *)
    let tl0 := fresh "tl" in let Htl0 := fresh "Heql" in remember tl as tl0 eqn:Htl0;
    let tr0 := fresh "tr" in let Htr0 := fresh "Heqr" in remember tr as tr0 eqn:Htr0;
    destruct H as [te tl' tr' t H | te tl' tr' t H |];
    repeat (match goal with
            | [H : _ :: _ = _ |- _] =>
              inversion H; subst; clear H
            end);
    try discriminate;
    subst;
    tac;
    unfold_interleaving H tac
  | ?err =>
    fail "Not an unfoldable interleaving" err
  end.

Tactic Notation "unfold_interleaving" ident(H) "with" tactic(tac) :=
  unfold_interleaving H tac.

Tactic Notation "unfold_interleaving" ident(H) :=
  unfold_interleaving H with idtac.

Section permutation.
  Context {S PID Req : Type} {Ret : Req -> Type}.
  Let TE := @TraceElem PID Req Ret.
  Context `{HsspS : StateSpace S TE}.

  Definition can_swap (a b : TE) : Prop :=
    te_pid a <> te_pid b.

  Definition DoubleForall {X} (f : X -> X -> Prop) (l1 l2 : list X) : Prop :=
    Forall (fun a => (Forall (f a) l1)) l2.

  Lemma DoubleForall_drop {X} f (a : X) l1 l2 :
    Forall (fun a0 : X => Forall (f a0) (a :: l1)) l2 ->
    Forall (fun a0 : X => Forall (f a0) l1) l2.
  Proof.
    intros H.
    induction l2; sauto.
  Qed.

  Lemma DoubleForall_symm {X} f (l1 l2 : list X) :
    DoubleForall f l1 l2 -> DoubleForall f l2 l1.
  Admitted. (* TODO *)

  Lemma interleaving_to_permutation t1 t2 t :
    DoubleForall can_swap t2 t1 ->
    Interleaving t1 t2 t ->
    @Permutation _ can_swap (t1 ++ t2) t.
  Proof.
    intros Hdisjoint H.
    induction H.
    3:{ simpl. constructor. }
    { apply Forall_inv_tail in Hdisjoint.
      now apply permut_cons, IHInterleaving.
    }
    { specialize (DoubleForall_drop can_swap te t2 t1 Hdisjoint) as Htail.
      specialize (IHInterleaving Htail). clear Htail. clear H.
      apply DoubleForall_symm, Forall_inv in Hdisjoint.
      apply permut_cons with (a := te) in IHInterleaving.
      induction IHInterleaving; try now constructor.
      induction t1.
      - constructor.
      - specialize (perm_shuf can_swap ((a :: t1) ++ te :: t2) [] (t1 ++ t2) a te) as Hs.
        simpl in *.
        apply Hs.
        + apply permut_cons, IHt1.
          now apply Forall_inv_tail in Hdisjoint.
        + apply Forall_inv in Hdisjoint.
          symm_not. apply Hdisjoint.
    }
  Qed.
End permutation.

Ltac resolve_forall :=
  match goal with
  | [H : Forall (trace_elems_commute ?a) (?x :: ?t) |- Forall (trace_elems_commute ?a) ?t] =>
    apply Forall_inv_tail in H; assumption
  | [H : Forall (trace_elems_commute ?a) (?x :: ?t) |- trace_elems_commute ?a ?x] =>
    apply Forall_inv in H; assumption
  end.

Hint Extern 1 (Forall (trace_elems_commute _) _) => resolve_forall : slot.
Hint Extern 3 (trace_elems_commute _ _) => resolve_forall : slot.

Section properties.
  Context `{HSSp : StateSpace}.

  Fixpoint num_interleavings (a b : nat) : nat :=
    match a, b with
    | 0, _   => 1
    | _, 0   => 1
    | _, S b => fold_left (fun acc i => acc + (num_interleavings i b)) (seq 0 (S a)) 0
    end.

  Goal forall (a b c d e f g h i j k : TE) s s' t,
      trace_elems_commute a d ->
      trace_elems_commute a c ->
      ReachableByTrace s t s' ->
      Interleaving [a; b; e; f; g] [c; d; i] t ->
      False.
  Proof.
    intros.
    Compute num_interleavings 5 3. (* 56 *)
    repeat (match goal with
            | [H : Interleaving (?a :: ?t1) ?t2 ?t |- _ ] =>
              destruct_interleaving H
            | [H : Interleaving ?t2 (?a :: ?t1) ?t |- _ ] =>
              inversion_ H; clear H
            | [H : Interleaving [] [] ?t |- _ ] =>
              inversion H; clear H
            end; try contradiction);
    let n := numgoals in guard n = 56.
  Abort.

  Let comm_diff a b := num_interleavings a b - (num_interleavings (a - 1) (b - 1)).

  Lemma comm_ilv_ls s s' a t t' :
    Forall (trace_elems_commute a) t ->
    Interleaving [a] t t' ->
    ReachableByTrace s t' s' ->
    ReachableByTrace s (a :: t) s'.
  Proof with auto with slot.
    intros Hcomm Ht Ht'.
    generalize dependent s'.
    generalize dependent s.
    remember [a] as t1.
    induction Ht; intros; inversion_ Heqt1...
    apply trace_elems_commute_head...
    inversion_ Ht'.
    forward s'0...
  Qed.

  Lemma ilv_singleton_comm_all a t2 P Q :
    Forall (trace_elems_commute a) t2 ->
    {{P}} [a] {{P}} ->
    {{P}} t2 {{Q}} ->
    -{{P}} Interleaving [a] t2 {{Q}}.
  Proof with auto with slot.
    intros Hcomm Ha Ht2 t Ht.
    remember [a] as t1.
    destruct Ht; inversion_ Heqt1.
    - interleaving_nil.
      apply hoare_cons with (mid := P)...
    - unfold_ht.
      inversion_ Hls.
      assert (Ha' : {{P}} a :: te :: t2 {{Q}}).
      { apply hoare_cons with (mid := P)... }
      apply trace_elems_commute_head_ht in Ha'...
      specialize (comm_ilv_ls s' s_end a t2 t) as Ht'.
      refine (Ha' s_begin s_end _ _)...
      forward s'...
  Qed.

  Lemma ilv_singleton_vs_app x a b (P Q : S0 -> Prop) :
    -{{P}} Interleaving a [x] ->> eq b {{Q}} ->
    -{{P}} eq a ->> Interleaving b [x] {{Q}} ->
    -{{P}} Interleaving (a ++ b) [x] {{Q}}.
  Proof with auto with slot.
    intros H1 H2 t Ht.
    remember [x] as t1.
    apply interleaving_par_seq in Ht.
    destruct Ht as [c1 [c2 [t2 [t3 [Ht [Hc [Hint1 Hint2]]]]]]].
    subst.
    destruct c1; destruct c2; try discriminate;
      autorewrite with list in *; simpl in *;
      inversion_ Hc.
    exfalso.
    destruct c1; inversion H3.
  Qed.
End properties.
