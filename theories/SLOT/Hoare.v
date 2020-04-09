From Coq Require Import
     List
     String
     Tactics
     Sets.Ensembles
     Program.Basics.

Import ListNotations.

From LibTx Require Import
     Permutation
     FoldIn.

Reserved Notation "'{{' a '}}' t '{{' b '}}'" (at level 40).

Global Arguments In {_}.
Global Arguments Complement {_}.
Global Arguments Disjoint {_}.

Ltac inversion_ a := inversion a; subst; auto.

Class StateSpace (S TE : Type) :=
  { chain_rule : S -> S -> TE -> Prop;
  }.

Notation "a '~' b '~>' c" := (chain_rule a c b)(at level 40).

Section defn.
  Context {S : Type} {TE : Type} `{HSSp : StateSpace S TE}.

  Let T := list TE.

  Inductive LongStep : S -> T -> S -> Prop :=
  | ls_nil : forall s,
      LongStep s [] s
  | ls_cons : forall s s' s'' te trace,
      chain_rule s s' te ->
      LongStep s' trace  s'' ->
      LongStep s (te :: trace) s''.

  Hint Constructors LongStep.

  Definition HoareTriple (pre : S -> Prop) (trace : T) (post : S -> Prop) :=
    forall s s',
      LongStep s trace s' ->
      pre s -> post s'.

  Notation "'{{' a '}}' t '{{' b '}}'" := (HoareTriple a t b).

  Lemma hoare_nil : forall p, {{p}} [] {{p}}.
  Proof.
    intros p s s' Hs.
    inversion_clear Hs. auto.
  Qed.

  Lemma ls_split : forall s s'' t1 t2,
      LongStep s (t1 ++ t2) s'' ->
      exists s', LongStep s t1 s' /\ LongStep s' t2 s''.
  Proof.
    intros.
    generalize dependent s.
    induction t1; intros.
    - exists s.
      split; auto.
    - inversion_clear H.
      specialize (IHt1 s' H1).
      destruct IHt1.
      exists x.
      split.
      + apply ls_cons with (s' := s'); firstorder.
      + firstorder.
  Qed.

  Lemma ls_concat : forall s s' s'' t1 t2,
      LongStep s t1 s' ->
      LongStep s' t2 s'' ->
      LongStep s (t1 ++ t2) s''.
  Proof.
    intros.
    generalize dependent s.
    induction t1; intros; simpl; auto.
    - inversion_ H.
    - inversion_ H.
      apply ls_cons with (s' := s'0); auto.
  Qed.

  Theorem hoare_concat : forall pre mid post t1 t2,
      HoareTriple pre t1 mid ->
      HoareTriple mid t2 post ->
      HoareTriple pre (t1 ++ t2) post.
  Proof.
    intros.
    intros s s' Hs Hpre.
    apply ls_split in Hs. destruct Hs.
    firstorder.
  Qed.

  Lemma hoare_cons : forall (pre mid post : S -> Prop) (te : TE) (trace : T),
      {{pre}} [te] {{mid}} ->
      {{mid}} trace {{post}} ->
      {{pre}} (te :: trace) {{post}}.
  Proof.
    intros.
    specialize (hoare_concat pre mid post [te] trace).
    auto.
  Qed.

  Lemma hoare_and : forall (A B C D : S -> Prop) (t : T),
      {{ A }} t {{ B }} ->
      {{ C }} t {{ D }} ->
      {{ fun s => A s /\ C s }} t {{ fun s => B s /\ D s }}.
  Proof. firstorder. Qed.

  Definition trace_elems_commute (te1 te2 : TE) :=
    forall s s',
      LongStep s [te1; te2] s' <-> LongStep s [te2; te1] s'.

  Lemma trace_elems_commute_ht : forall pre post te1 te2,
      trace_elems_commute te1 te2 ->
      {{pre}} [te1; te2] {{post}} <-> {{pre}} [te2; te1] {{post}}.
  Proof.
    unfold trace_elems_commute.
    split; intros;
    intros s s' Hss' Hpre;
    specialize (H s s');
    apply H in Hss';
    apply H0 in Hss';
    apply Hss' in Hpre;
    assumption.
  Qed.

  Lemma trace_elems_commute_symm : forall te1 te2,
      trace_elems_commute te1 te2 ->
      trace_elems_commute te2 te1.
  Proof. firstorder. Qed.

  Hint Resolve trace_elems_commute_symm.

  Lemma trace_elems_commute_head : forall s s'' b a trace,
      trace_elems_commute a b ->
      LongStep s (b :: a :: trace) s'' ->
      LongStep s (a :: b :: trace) s''.
  Proof.
    intros.
    inversion_ H0.
    inversion_ H6.
    specialize (H s s'0).
    replace (a :: b :: trace) with ([a; b] ++ trace) by auto.
    apply ls_concat with (s' := s'0); auto.
    apply H.
    apply ls_cons with (s' := s'); auto.
    apply ls_cons with (s' := s'0); auto.
  Qed.

  Section ExpandTrace.
    Variable te_subset : Ensemble TE.

    Definition Local (prop : S -> Prop) :=
      forall te,
        ~In te_subset te ->
        {{prop}} [te] {{prop}}.

    Definition ChainRuleLocality :=
      forall te te',
        In te_subset te ->
        ~In te_subset te' ->
        trace_elems_commute te te'.

    Example True_is_local : Local (fun s => True).
    Proof. easy. Qed.

    Let can_swap a b := In te_subset a /\ Complement te_subset b.

    Inductive ExpandedTrace (trace trace' : T) : Prop :=
      expanded_trace_ : forall expansion,
        Forall (Complement te_subset) expansion ->
        Permutation can_swap (expansion ++ trace) trace' ->
        ExpandedTrace trace trace'.

    Hint Transparent Ensembles.In Ensembles.Complement.

    Theorem expand_trace : forall pre post trace trace',
        ChainRuleLocality ->
        Local pre ->
        ExpandedTrace trace trace' ->
        {{pre}} trace {{post}} ->
        {{pre}} trace' {{post}}.
    Proof.
      (* Human-readable proof: using [ChainRuleLocality] hypothesis,
      we can "pop up" all non-matching trace elements and get from a
      trace that looks like this:

      {---+---++---+--}

      to a one that looks like this:

      {-----------++++}

      Since our definition of commutativity gives us evidence that
      state transition between the commuting trace elements exists,
      we can conclude that there is a state transition from {----}
      part of trace to {++++}.
      *)
      intros pre post trace trace' Hcr Hl_pre [expansion Hcomp Hexp] Htrace.
      induction Hexp; intros; auto.
      2:{ intros s s'' Hss'' Hpre.
          apply ls_split in Hss''.
          destruct Hss'' as [s' [Hss' Hss'']].
          specialize (IHHexp s s'').
          specialize (Hcr a b).
          assert (Hls : LongStep s (l' ++ a :: b :: r') s'').
          { apply ls_concat with (s' := s'); auto.
            apply trace_elems_commute_head; auto.
            destruct H.
            apply Hcr; auto.
          }
          apply IHHexp; auto.
      }
      1:{ induction expansion.
          - easy.
          - simpl.
            inversion_ Hcomp.
            apply hoare_cons with (mid := pre).
            apply Hl_pre; auto.
            firstorder.
      }
    Qed.
  End ExpandTrace.

  Theorem frame_rule : forall (e1 e2 : Ensemble TE) (P Q R : S -> Prop) (te : TE),
      Disjoint e1 e2 ->
      Local e2 R ->
      In e1 te ->
      {{ P }} [te] {{ Q }} ->
      {{ fun s => P s /\ R s }} [te] {{ fun s => Q s /\ R s }}.
  Proof.
    intros e1 e2 P Q R te He HlR Hin Hh.
    apply hoare_and.
    - assumption.
    - apply HlR.
      destruct He as [He].
      specialize (He te).
      unfold not, In in He.
      intros Hinte.
      apply He.
      constructor; auto.
  Qed.

  Definition PossibleTrace t :=
    exists s s', LongStep s t s'.
End defn.

Notation "'{{' a '}}' t '{{' b '}}'" := (HoareTriple a t b) : hoare_scope.
