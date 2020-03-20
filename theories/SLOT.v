(*** Minimalistic implementation of concurrent separation logic with implicit state *)
(** This module defines the model of distributed system used in the
rest of the project. Whether you trust the LibTx depends on whether
you trust the below definitions.

* Motivation

Before diving into lengthy description of the model, let me first
motivate a sceptical reader:

** Q: Why not TLA+?

A: ToySep allows to describe nondeterministic parts of the model in a
way very similar to TLA+. But its deterministic part enjoys from using
a full-fledged functional language

- I want to write inductive proofs

- I want to use a more or less traditional functional language

- I want to extract verified programs

- While TLA+ model checker is top notch, its proof checker isn't, by
  far

** Q: Why not %model checker%?

A: Model checkers show why the code _fails_, which is good for
verifying algorithms, but formal proofs show why the code _works_ (via
tree of assumptions), which is good for reasoning about algorithms
and, in particular, predicting the outcome of optimisations. Also
model checkers can't explore the entire state space of a typical
real-life system with unbounded number of actors.

** Q: Why not Verdi?

- Verdi models are low level: think UDP packets and disk IO. ToySep is
  meant to model systems on a much higher level: think Kafka client
  API.

- Nondeterminisic part of Verdi is hardcoded, while ToySep allows user
  to define custom nondeterministic IO handlers.

** Q: Why not disel?

A: disel models are closer to what I need, but implementation itself
is an incomprehensible, undocumetned burp of ssreflect. Proofs are as
useful as their premises: "garbage in - garbage out". Good model
should be well documented and well understood.

** Q: Why not iris/aneris?

A: iris allows user to define semantics of their very own programming
language. ToySep is focused on proving properties of _regular pure
functinal programs_ that do IO from time to time. Hence it defines
actors in regular Gallina language, rather than some DSL, and frees
the user from reinventing basic control flow constructions.

*)
From Coq Require Import
     List
     Tactics
     Sets.Ensembles.

Import ListNotations.

From QuickChick Require Import
     QuickChick.

From LibTx Require Import
     InterleaveLists
     FoldIn.

Reserved Notation "pid '@' req '<~' ret" (at level 30).
Reserved Notation "'{{' a '}}' t '{{' b '}}'" (at level 40).
Reserved Notation "'{{' a '&' b '}}' t '{{' c '&' d '}}'" (at level 10).

Global Arguments In {_}.
Global Arguments Complement {_}.
Global Arguments Disjoint {_}.

Ltac inversion_ a := inversion a; subst; auto.

Module Hoare.
  Class StateSpace (S TE : Type) :=
    { chain_rule : S -> S -> TE -> Prop;
    }.

  Section defn.
    (* Context {S : Type} {TE : Type} {chain_rule : S -> S -> TE -> Prop}. *)
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

    Notation "'{{' A '&' B '}}' t '{{' C '&' D '}}'" :=
        ({{ fun s => A s /\ B s }} t {{ fun s => C s /\ D s }}).

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

      (* This theorem is weaker than [expand_trace_elem], as it
      requires an additional assumption [ChainRuleLocality]. But
      on the other hand, it doesn't require [Local post] *)
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

    Definition Invariant inv :=
      forall (te : TE),
        {{ inv }} [te] {{ inv }}.
  End defn.

  Notation "'{{' a '}}' t '{{' b '}}'" :=
        (HoareTriple a t b).
End Hoare.

Module EventTrace.
  Record Ctx : Type :=
    mkCtx { ctx_pid_t : Set;
            ctx_req_t : Set;
            ctx_ret_t : ctx_req_t -> Set;
          }.

  Record TraceElem {ctx : Ctx} : Set :=
    trace_elem { te_pid : ctx_pid_t ctx;
                 te_req : ctx_req_t ctx;
                 te_ret : (ctx_ret_t ctx) te_req;
               }.

  Definition Trace {ctx : Ctx} := list (@TraceElem ctx).
End EventTrace.

Module Handler.
  Export Hoare.
  Export EventTrace.

  Section IOHandler.
    Context {PID : Set}.

    Local Notation "'Nondeterministic' a" := ((a) -> Prop) (at level 200).

    Record t : Type :=
      {
        h_state         : Set;
        h_req           : Set;
        h_ret           : h_req -> Set;
        h_initial_state : Nondeterministic h_state;
        h_chain_rule    : h_state -> h_state -> @TraceElem (mkCtx PID h_req h_ret) -> Prop
      }.

    Definition hToCtx (h : t) := mkCtx PID h.(h_req) h.(h_ret).

  End IOHandler.

  Section Hoare.
    (* Here we specialize definitions from Hoare module *)
    Context {PID : Set} {H : @t PID}.

    Let S := h_state H.
    Let ctx := hToCtx H.
    Let TE := @TraceElem ctx.

    Instance handlerStateSpace : StateSpace S TE :=
      {| chain_rule := h_chain_rule H |}.

    Definition HoareTripleH (pre : S -> Prop) (trace : @Trace ctx) (post : S -> Prop) :=
      @HoareTriple S TraceElem _ pre trace post.

    Definition Local := @Local S TE _.

    Definition ChainRuleLocality := @ChainRuleLocality S TE _.

    Definition PossibleTrace := @PossibleTrace S TE _.
  End Hoare.

  Notation "'{{' a '}}' t '{{' b '}}'" := (HoareTripleH a t b) : handler_scope.

  Section ComposeHandlers.
    Context {PID : Set} (h_l h_r : @t PID).

    Let S_l := h_state h_l.
    Let S_r := h_state h_r.
    Let Q_l := h_req h_l.
    Let Q_r := h_req h_r.

    Definition compose_state : Set := S_l * S_r.
    Let S := compose_state.

    Definition compose_req : Set := Q_l + Q_r.
    Let Q := compose_req.

    Hint Transparent compose_state.

    Definition compose_initial_state state :=
      h_l.(h_initial_state) (fst state) /\ h_r.(h_initial_state) (snd state).

    Hint Transparent compose_initial_state.

    Definition compose_ret (req : Q) : Set :=
      match req with
      | inl l => h_l.(h_ret) l
      | inr r => h_r.(h_ret) r
      end.

    Let ctx := mkCtx PID Q compose_ret.
    Let TE := @TraceElem ctx.


    Inductive compose_chain_rule_i : S -> S -> TE -> Prop :=
    | cmpe_left :
        forall (l l' : S_l) (r : S_r) pid req ret,
          h_chain_rule h_l l l' (trace_elem _ pid req ret) ->
          compose_chain_rule_i (l, r) (l', r) (trace_elem ctx pid (inl req) ret)
    | cmpe_right :
        forall (r r' : S_r) (l : S_l) pid req ret,
          h_chain_rule h_r r r' (trace_elem _ pid req ret) ->
          compose_chain_rule_i (l, r) (l, r') (trace_elem ctx pid (inr req) ret).

    Definition compose_chain_rule (s s' : S) (te : TE) : Prop.
      destruct te as [pid req ret].
      destruct s as [l r].
      destruct s' as [l' r'].
      remember req as req0.
      destruct req;
        [ refine (r = r' /\ (h_chain_rule h_l) l l' _)
        | refine (l = l' /\ (h_chain_rule h_r) r r' _)
        ];
        apply trace_elem with (te_req := q);
        try apply pid;
        subst;
        unfold compose_ret in ret; easy.
    Defined.

    Definition compose : t :=
      {| h_state         := compose_state;
         h_req           := compose_req;
         h_ret           := compose_ret;
         h_initial_state := compose_initial_state;
         h_chain_rule    := compose_chain_rule;
      |}.

    Definition te_subset_l (te : TE) :=
      match te_req te with
      | inl _ => True
      | inr _ => False
      end.

    Definition te_subset_r (te : TE) :=
      match te_req te with
      | inl _ => False
      | inr _ => True
      end.

    Definition lift_l (prop : S_l -> Prop) : compose_state -> Prop :=
      fun s => match s with
              (s_l, _) => prop s_l
            end.

    Definition lift_r (prop : S_r -> Prop) : compose_state -> Prop :=
      fun s => match s with
              (_, s_r) => prop s_r
            end.

    Lemma lift_l_local : forall (prop : S_l -> Prop),
        @Local PID compose te_subset_l (lift_l prop).
    Proof.
      unfold Local, HoareTriple.
      intros prop te Hin s s' Hte Hpre.
      unfold te_subset_l in Hin.
      destruct te as [pid req ret].
      unfold In in *.
      destruct req as [req|req]; simpl in *.
      - easy.
      - inversion_ Hte.
        unfold compose_chain_rule in H2.
        destruct s, s', s'0.
        firstorder.
        unfold eq_rec_r in *. simpl in *.
        subst.
        inversion_ H4.
    Qed.

    Lemma lift_r_local : forall (prop : S_r -> Prop),
        @Local PID compose te_subset_r (lift_r prop).
    Proof.
      unfold Local, HoareTriple.
      intros prop te Hin s s' Hte Hpre.
      unfold te_subset_r in Hin.
      destruct te as [pid req ret].
      unfold In in *.
      destruct req as [req|req]; simpl in *.
      - inversion_ Hte.
        unfold compose_chain_rule in H2.
        destruct s, s', s'0.
        firstorder.
        unfold eq_rec_r in *. simpl in *.
        subst.
        inversion_ H4.
      - easy.
    Qed.

    Lemma local_l_chain_rule : @ChainRuleLocality PID compose te_subset_l.
    Proof.
      intros te1 te2 Hte1 Hte2 [l r] [l' r'].
      split; intros Hs';
      destruct te1 as [pid1 req1 ret1];
      destruct te2 as [pid2 req2 ret2];
      destruct req1, req2; unfold Ensembles.In, te_subset_l in *; try easy;
        clear Hte1; clear Hte2;
        inversion Hs' as [|[l1 r1] [l2 r2]]; subst; clear Hs';
        inversion H0 as [|[l3 r3] [l4 r4]]; subst; clear H0;
        inversion H2; subst; clear H2;
        unfold compose_chain_rule in *;
        firstorder; subst;
        unfold eq_rec_r in *; simpl in *.
      - apply ls_cons with (s' := (l, r')); firstorder.
        apply ls_cons with (s' := (l', r')); firstorder.
        constructor.
      - apply ls_cons with (s' := (l', r)); firstorder.
        apply ls_cons with (s' := (l', r')); firstorder.
        constructor.
    Qed.

    Lemma local_r_chain_rule : @ChainRuleLocality PID compose te_subset_r.
    Proof.
      intros te1 te2 Hte1 Hte2 [l r] [l' r'].
      split; intros Hs';
      destruct te1 as [pid1 req1 ret1];
      destruct te2 as [pid2 req2 ret2];
      destruct req1, req2; unfold Ensembles.In, te_subset_r in *; try easy;
        clear Hte1; clear Hte2;
        inversion Hs' as [|[l1 r1] [l2 r2]]; subst; clear Hs';
        inversion H0 as [|[l3 r3] [l4 r4]]; subst; clear H0;
        inversion H2; subst; clear H2;
        unfold compose_chain_rule in *;
        firstorder; subst;
        unfold eq_rec_r in *; simpl in *.
      - apply ls_cons with (s' := (l', r)); firstorder.
        apply ls_cons with (s' := (l', r')); firstorder.
        constructor.
      - apply ls_cons with (s' := (l, r')); firstorder.
        apply ls_cons with (s' := (l', r')); firstorder.
        constructor.
    Qed.
  End ComposeHandlers.
End Handler.

Module Mutable.
  Import Handler.

  Inductive req_t {T : Set} :=
  | get : req_t
  | put : T -> req_t.

  Section defs.
  Context (PID T : Set) (initial_state : T -> Prop).

  Local Definition ret_t (req : @req_t T) : Set :=
    match req with
    | get => T
    | _   => True
    end.

  Let ctx := mkCtx PID req_t ret_t.
  Let TE := @TraceElem ctx.

  Inductive mut_chain_rule : T -> T -> TE -> Prop :=
  | mut_get : forall s pid,
      mut_chain_rule s s (trace_elem ctx pid get s)
  | mut_put : forall s val pid,
      mut_chain_rule s val (trace_elem ctx pid (put val) I).

  Definition t : t :=
    {|
      h_state := T;
      h_req := req_t;
      h_initial_state := initial_state;
      h_chain_rule := mut_chain_rule;
    |}.
  End defs.
End Mutable.

Module Mutex.
  Import Handler.

  Section defs.
    Open Scope handler_scope.
    Inductive req_t : Set :=
    | grab    : req_t
    | release : req_t.

    Local Definition ret_t (req : req_t) : Set :=
      match req with
      | grab => True
      | release => bool
      end.

    Variable PID : Set.

    Definition state_t : Set := option PID.

    Let ctx := mkCtx PID req_t ret_t.
    Let TE := @TraceElem ctx.

    Inductive mutex_chain_rule : state_t -> state_t -> TE -> Prop :=
    | mutex_grab : forall pid,
        mutex_chain_rule None (Some pid) (trace_elem ctx pid grab I)
    | mutex_release_ok : forall pid,
        mutex_chain_rule (Some pid) None (trace_elem ctx pid release true)
    | mutex_release_fail : forall pid,
        mutex_chain_rule (Some pid) None (trace_elem ctx pid release false).

    Definition t : t :=
      {|
        h_state         := state_t;
        h_req           := req_t;
        h_initial_state := fun s0 => s0 = None;
        h_chain_rule    := mutex_chain_rule
      |}.

    Notation "pid '@' ret '<~' req" := (@trace_elem ctx pid req ret).

    Theorem no_double_grab_0 : forall (a1 a2 : PID),
        ~(@PossibleTrace PID t [a1 @ I <~ grab;
                                a2 @ I <~ grab]).
    Proof.
      intros a1 a2 H.
      destruct H as [s [s' H]].
      inversion_ H.
      inversion_ H3.
      inversion_ H5.
      inversion_ H4.
    Qed.

    Let state_space := state_t. Let trace_elem := req_t.

    Theorem no_double_grab : forall (a1 a2 : PID),
        {{ fun (_ : h_state t) => True }}
          [a1 @ I <~ grab;
           a2 @ I <~ grab]
        {{ fun _ => False}}.
    Proof.
      intros a1 a2 s s' Hss' Hpre.
      inversion_ Hss'.
      inversion_ H2.
      inversion_ H4.
      inversion_ H3.
    Qed.
  End defs.
End Mutex.

Module SUT.
  Export Hoare EventTrace.

  Section defn.
    Context {ctx : Ctx}.

    Let PID := ctx_pid_t ctx.
    Let Req := ctx_req_t ctx.
    Let Ret := ctx_ret_t ctx.

    Let TE := @TraceElem ctx.
    Let T := @Trace ctx.

    Class Runnable A : Type :=
      { unfolds_to : A -> A -> T -> Prop;
      }.

    CoInductive Thread {pid : PID} : Type :=
    | t_dead : Thread
    | t_cont :
        forall (pending_req : Req)
          (continuation : Ret pending_req -> Thread)
        , Thread.

    Definition throw {pid} (_ : string) := @t_dead pid.

    Inductive UnfoldThread (pid : PID) (t0 : @Thread pid) : @Thread pid -> T -> Prop :=
    | uft_nil : UnfoldThread pid t0 t0 []
    | uft_cons : forall req ret cont t,
        UnfoldThread pid t0 (t_cont req cont) t ->
        UnfoldThread pid t0 (cont ret) (trace_elem _ pid req ret :: t).

    Instance runnableThread (pid : PID) : Runnable Thread :=
      {| unfolds_to thread0 thread trace := UnfoldThread pid thread0 thread (rev trace);
      |}.

    Section ComposeSystems.
      Context (sys1 sys2 : Type) `{Runnable sys1} `{Runnable sys2}.

      Let S : Type := sys1 * sys2.

      Let can_swap (te1 te2 : TE) := te_pid te1 <> te_pid te2.

      Instance composeRunnable : Runnable S :=
        {| unfolds_to s s' trace :=
             match s, s' with
             | (s1, s2), (s1', s2') => forall t1 t2,
                 unfolds_to s1 s1' t1 /\
                 unfolds_to s2 s2' t2 /\
                 Permutation can_swap (t1 ++ t2) trace
             end;
        |}.
    End ComposeSystems.
  End defn.
End SUT.

Module ExampleModelDefn.
  Import Handler.
  Import SUT.

  Let PID := nat.

  Definition Handler := compose (Mutable.t PID nat (fun a => a = 0))
                                (Mutex.t PID).

  Let ctx := hToCtx Handler.

  Let TE := @TraceElem ctx.

  Notation "'do' V '<-' I ; C" := (@t_cont ctx _ (I) (fun V => C))
                                    (at level 100, C at next level, V ident, right associativity).

  Notation "'done' I" := (@t_cont ctx _ (I) (fun _ => t_dead))
                           (at level 100, right associativity).

  Notation "pid '@' ret '<~' req" := (@trace_elem ctx pid req ret).

  Local Definition put (val : nat) : Handler.(h_req) :=
    inl (Mutable.put val).

  Local Definition get : h_req Handler :=
    inl (Mutable.get).

  Local Definition grab : h_req Handler :=
    inr (Mutex.grab).

  Local Definition release : h_req Handler :=
    inr (Mutex.release).

  (* Just a demonstration how to define a program that loops
  indefinitely, as long as it does IO: *)
  Local CoFixpoint infinite_loop (self : PID) : @Thread ctx self :=
    do _ <- put 0;
    infinite_loop self.

  (* Data race example: *)
  Local Definition counter_race (self : PID) : @Thread ctx self :=
    do v <- get;
    done put (v + 1).

  (* Fixed example: *)
  Local Definition counter_correct (self : PID) : @Thread ctx self :=
    do _ <- grab;
    do v <- get;
    do _ <- put (v + 1);
    done release.

  Let SUT := (counter_correct 1, counter_correct 2).

  Fail Example empty_trace := unfolds_to SUT SUT [].
End ExampleModelDefn.
