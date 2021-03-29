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
(** * Definitions for reasoning about a single execution history

This module defines an abstraction called trace, that can be used to
represent history of all syscalls executed by the running system. In
this module we don't introduce any notion or semantics of syscall yet,
to keep our definitions and theorems more generic. A more neutral term
"trace element" is used here instead, but for simplicity one can think
that trace element is roughly equivalent to a syscall.

*)

From Coq Require Import
     List
     String
     Tactics
     Sets.Ensembles
     Program.Basics.

Export ListNotations.

From LibTx Require Import
     Permutation
     FoldIn.

Reserved Notation "'{{' a '}}' t '{{' b '}}'" (at level 40).
Reserved Notation "'{{}}' t '{{' b '}}'" (at level 39).

Global Arguments In {_}.
Global Arguments Complement {_}.
Global Arguments Disjoint {_}.

Ltac inversion_ a := inversion a; subst; auto with slot.

(** ** State space

[StateSpace] class is an abstraction used to describe side effects of
syscalls.

*** Parameters:

 - <<S>> — set of points of the state space

 - <<TE>> — set of trace elements

*** Methods:

[state_transition s s' te] is a type of statements that read as "trace
element [te] can transition system from state [s] to state [s']" *)
Class StateSpace (S TE : Type) :=
  { state_transition : S -> S -> TE -> Prop;
  }.

Notation "a '~[' b ']~>' c" := (state_transition a c b)(at level 40) : hoare_scope.
Infix "/\'" := (fun a b x => a x /\ b x)(at level 80) : hoare_scope.

Open Scope hoare_scope.

(** For example suppose <<S>> is [nat] and <<TE>> is [Inductive TE := increment.]

Then the state transition method for the side effects of <<TE>> can be defined like this:

[[
state_transition s s' te =
  match te with
  | increment => s' = s + 1
  end.
]]

Note that side effects can be nondeterminisic. Let's extend our definition
of TE with "Russian roulette" operation that either leaves the state unchanged
or sets it to zero:

[[
Inductive TE := increment
              | rr.
]]

Chain rule for this operation will look like this:

[[
state_transition s s' te =
  match te with
  | increment => s' = s + 1
  | rr        => s' = s \/ s' = 0
  end.
]]

*)

(** ** Paths through the state space

[ReachableByTrace] is a datatype describing paths through the state space. Its
first constructor [rbt_nil] states the fact that the empty trace
doesn't change the state of the system. In other words, state of the
system doesn't drift by itself.

The second constructor [rbt_cons] declares that performing a syscall
[te] transitioning the system from [s] to [s'] followed by execution
of all syscalls in [trace], transitioning the system from [s'] to
[s''], is equivalent to executing a path [te :: trace] from [s] to
[s''] *)

Section defn.
  Context {S : Type} {TE : Type} `{HSSp : StateSpace S TE}.

  Let T := list TE.

  Inductive ReachableByTrace : S -> T -> S -> Prop :=
  | rbt_nil : forall s,
      ReachableByTrace s [] s
  | rbt_cons : forall s s' s'' te trace,
      state_transition s s' te ->
      ReachableByTrace s' trace  s'' ->
      ReachableByTrace s (te :: trace) s''.

  Hint Constructors ReachableByTrace : slot.

  (** [ls_split] is an important observation that there is a point in
  the state space for each intermediate step of the trace
  execution: *)
  Lemma ls_split : forall s s'' t1 t2,
      ReachableByTrace s (t1 ++ t2) s'' ->
      exists s', ReachableByTrace s t1 s' /\ ReachableByTrace s' t2 s''.
  Proof.
    intros.
    generalize dependent s.
    induction t1; intros.
    - exists s.
      split; auto with slot.
    - inversion_clear H.
      specialize (IHt1 s' H1).
      destruct IHt1.
      exists x.
      split.
      + apply rbt_cons with (s' := s'); firstorder.
      + firstorder.
  Qed.

  (** [ls_concat] lemma demonstrates that traces can be composed: *)
  Lemma ls_concat : forall s s' s'' t1 t2,
      ReachableByTrace s t1 s' ->
      ReachableByTrace s' t2 s'' ->
      ReachableByTrace s (t1 ++ t2) s''.
  Proof.
    intros.
    generalize dependent s.
    induction t1; intros; simpl; auto.
    - inversion_ H.
    - inversion_ H.
      apply rbt_cons with (s' := s'0); auto.
  Qed.

  (** ** Hoare logic of traces

      [HoareTriple] is a type of judgments about trace execution,
      stating that if precondition [pre] holds for the initial state
      [s], and there is path [trace] through the state space leading
      to a point [s'], then postcondition [post] must hold for
      [s']. *)
  Definition HoareTriple (pre : S -> Prop) (trace : T) (post : S -> Prop) :=
    forall s s',
      ReachableByTrace s trace s' ->
      pre s -> post s'.

  Notation "'{{' a '}}' t '{{' b '}}'" := (HoareTriple a t b).

  (** Executing an empty trace doesn't change any properties: *)
  Lemma hoare_nil : forall p, {{p}} [] {{p}}.
  Proof.
    intros p s s' Hs.
    inversion_clear Hs. auto.
  Qed.

  (** Hoare triples of traces can be composed: *)
  Theorem hoare_concat : forall pre mid post t1 t2,
      {{pre}} t1 {{mid}} ->
      {{mid}} t2 {{post}} ->
      {{pre}} (t1 ++ t2) {{post}}.
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

  (** ** Invariants

   [TraceInvariant] is a type of judgments stating that if execution
   of a trace starts in a state where property [prop] holds, then the
   same property will hold for each intermediate state during
   execution of the trace. In other words: [prop] is a subset of the
   state space, and if the system starts off in this subset, it always
   stays in it. *)
  Inductive TraceInvariant (prop : S -> Prop) : T -> Prop :=
  | inv_nil : TraceInvariant prop []
  | inv_cons : forall te t,
      {{prop}} [te] {{prop}} ->
      TraceInvariant prop t ->
      TraceInvariant prop (te :: t).

  Hint Constructors TraceInvariant : slot.

  Lemma trace_inv_split : forall prop t1 t2,
      TraceInvariant prop (t1 ++ t2) ->
      TraceInvariant prop t1 /\ TraceInvariant prop t2.
  Proof.
    intros.
    induction t1; split; auto with slot;
    inversion_ H; specialize (IHt1 H3);
    try constructor; firstorder.
  Qed.

  Lemma trace_inv_app : forall prop t1 t2,
      TraceInvariant prop t1 ->
      TraceInvariant prop t2 ->
      TraceInvariant prop (t1 ++ t2).
  Proof.
    intros.
    induction t1; simpl in *; auto with slot.
    inversion_ H.
  Qed.

  (** ** Commutativity of trace elements
   *)
  Definition trace_elems_commute (te1 te2 : TE) :=
    forall s s',
      ReachableByTrace s [te1; te2] s' <-> ReachableByTrace s [te2; te1] s'.

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

  Hint Resolve trace_elems_commute_symm : slot.

  Lemma trace_elems_commute_head : forall s s'' b a trace,
      trace_elems_commute a b ->
      ReachableByTrace s (b :: a :: trace) s'' ->
      ReachableByTrace s (a :: b :: trace) s''.
  Proof with auto with slot.
    intros.
    inversion_ H0.
    inversion_ H6.
    specialize (H s s'0).
    replace (a :: b :: trace) with ([a; b] ++ trace) by auto.
    apply ls_concat with (s' := s'0)...
    apply H.
    apply rbt_cons with (s' := s')...
    apply rbt_cons with (s' := s'0)...
  Qed.

  Lemma trace_elems_commute_head_ht : forall P Q b a trace,
      trace_elems_commute a b ->
      {{P}} b :: a :: trace {{Q}} ->
      {{P}} a :: b :: trace {{Q}}.
  Proof.
    intros. intros s s' Hls Hpre.
    apply trace_elems_commute_head in Hls.
    - apply (H0 s s' Hls Hpre).
    - now apply trace_elems_commute_symm.
  Qed.

  Definition trace_elems_commute_s te1 te2 s s' s'' :
    s ~[te1]~> s' ->
    s' ~[te2]~> s'' ->
    trace_elems_commute te1 te2 ->
    exists s'_, s ~[te2]~> s'_ /\ s'_ ~[te1]~> s''.
  Proof with auto.
    intros H1 H2 H.
    assert (Hls : ReachableByTrace s [te1; te2] s'').
    { apply rbt_cons with (s' := s')...
      apply rbt_cons with (s' := s'')...
      constructor.
    }
    apply H in Hls.
    inversion_ Hls.
    inversion_ H7.
    inversion_ H9.
    exists s'0.
    split...
  Qed.

  Lemma ht_comm_perm s s' t t' :
    ReachableByTrace s t s' ->
    Permutation trace_elems_commute t t' ->
    ReachableByTrace s t' s'.
  Proof with eauto with slot.
    intros Hls Hperm.
    induction Hperm.
    - trivial.
    - apply ls_split in IHHperm.
      destruct IHHperm as [s0 [Hss0 Hs0s']].
      apply trace_elems_commute_head in Hs0s'...
      eapply ls_concat...
  Qed.

  (** ** Trace extensions
   *)
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

    Theorem expand_trace : forall pre post trace trace',
        ChainRuleLocality ->
        Local pre ->
        ExpandedTrace trace trace' ->
        {{pre}} trace {{post}} ->
        {{pre}} trace' {{post}}.
    Proof with auto with slot.
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
          assert (Hls : ReachableByTrace s (l' ++ a :: b :: r') s'').
          { apply ls_concat with (s' := s')...
            apply trace_elems_commute_head...
            destruct H.
            apply Hcr...
          }
          apply IHHexp...
      }
      1:{ induction expansion.
          - easy.
          - simpl.
            inversion_ Hcomp.
            apply hoare_cons with (mid := pre).
            apply Hl_pre...
            firstorder.
      }
    Qed.
  End ExpandTrace.

  Theorem frame_rule : forall (e1 e2 : Ensemble TE) (P Q R : S -> Prop) (te : TE),
      Disjoint e1 e2 ->
      Local e2 R ->
      In e1 te ->
      {{ P }} [te] {{ Q }} ->
      {{ P /\' R }} [te] {{ Q /\' R }}.
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
    exists s s', ReachableByTrace s t s'.
End defn.

Notation "'{{' a '}}' t '{{' b '}}'" := (HoareTriple a t b) : hoare_scope.
Notation "'{{}}' t '{{' b '}}'" := (HoareTriple (const True) t b) : hoare_scope.

Check rbt_cons.

Ltac forward s' :=
  apply (rbt_cons _ s' _ _ _).

Ltac resolve_concat :=
  match goal with
    [ H1 : ReachableByTrace ?s1 ?t1 ?s2, H2 : ReachableByTrace ?s2 ?t2 ?s3 |- ReachableByTrace ?s1 (?t1 ++ ?t2) ?s3] =>
    apply (ls_concat s1 s2 s3 t1 t2); assumption
  end.

Hint Extern 3 (ReachableByTrace _ (_ ++ _) _) => resolve_concat : slot.

Ltac long_step f tac :=
  cbn in f;
  lazymatch type of f with
  | ReachableByTrace _ [] _ =>
    let s := fresh "s" in
    let Hx := fresh "Hx" in
    let Hy := fresh "Hy" in
    let Hz := fresh "Hz" in
    inversion f as [s Hx Hy Hz|];
    subst s; clear f; clear Hy
  | ReachableByTrace _ (_ :: _) _ =>
    let s' := fresh "s" in
    let te := fresh "te" in
    let tail := fresh "tail" in
    let Hcr := fresh "Hcr" in
    let Htl := fresh "Htl" in
    inversion_clear f as [|? s' ? te tail Hcr Htl];
    rename Htl into f;
    cbn in Hcr;
    tac Hcr
  end.

Tactic Notation "long_step" ident(f) tactic3(tac) := long_step f tac.
Tactic Notation "long_step" ident(f) := long_step f (fun _ => idtac).

Ltac unfold_trace f tac :=
  repeat (long_step f tac).

Tactic Notation "unfold_trace" ident(f) tactic3(tac) := unfold_trace f tac.
Tactic Notation "unfold_trace" ident(f) := unfold_trace f (fun _ => idtac).

Ltac ls_advance tac :=
  match goal with
  | [H : ReachableByTrace ?s ?t ?s' |- ?Q ?s'] =>
    long_step H tac
  end.

Tactic Notation "ls_advance" tactic3(tac) := ls_advance tac.
Tactic Notation "ls_advance" := ls_advance (fun _ => idtac).

Hint Transparent Ensembles.In Ensembles.Complement : slot.
Hint Constructors ReachableByTrace : slot.
Hint Resolve trace_elems_commute_symm : slot.

Ltac unfold_ht :=
  match goal with
  | [ |- {{?pre}} ?t {{?post}}] =>
    let s := fresh "s_begin" in
    let s' := fresh "s_end" in
    let Hls := fresh "Hls" in
    let Hpre := fresh "Hpre" in
    intros s s' Hls Hpre;
    match eval cbn in Hpre with
    | [fun _ => True] => clear Hpre (* TODO: Fixme *)
    | _ => idtac
    end
  | _ =>
    fail "Goal does not look like a Hoare triple"
  end.

Section tests.
  Generalizable Variables ST TE.

  Goal forall `{StateSpace ST TE} s s' (te : TE), ReachableByTrace s [te; te; te] s' -> True.
    intros.
    unfold_trace H0.
  Abort.

  Goal forall `{StateSpace ST TE} s s' (te : TE), ReachableByTrace s [te] s' -> True.
    intros.
    unfold_trace H0 (fun x => try inversion x).
  Abort.

  Goal forall `{StateSpace ST TE} s s' (te : TE), ReachableByTrace s [] s' -> True.
    intros.
    unfold_trace H0.
  Abort.

  Goal forall `{StateSpace ST TE} pre post l, {{pre}} (l: list TE) {{post}}.
    intros.
    unfold_ht.
  Abort.
End tests.
