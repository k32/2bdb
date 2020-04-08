(*** Separation Logic of Traces *)
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

- While TLA+ model checker is top notch, its proof checker isn't

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

From LibTx Require Export
     SLOT.EventTrace
     SLOT.Hoare
     SLOT.Handler
     SLOT.Process.

From Coq Require Import
     List.

Import ListNotations.

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

    Fail Lemma mut_get_comm : forall v pid1 pid2, (*TODO*)
        trace_elems_commute (trace_elem ctx pid1 get v) (trace_elem ctx pid2 get v).
  End defs.
End Mutable.

Module Mutex.
  Import Handler.

  Section defs.
    Open Scope hoare_scope.
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


Module Model.
  Section defn.
    Context {PID} {SUT : Type} {Handler : @Handler.t PID}.
    Let ctx := hToCtx Handler.

    Record t : Type :=
      mkModel
        { model_sut : SUT;
          model_handler : h_state Handler;
        }.


    Context `{Runnable ctx SUT}.

    Definition model_chain_rule m m' te : Prop :=
      match m, m' with
      | mkModel s h, mkModel s' h' => (h_chain_rule Handler) h h' te /\
                                     runnable_step s s' te
      end.

    Global Instance modelHoare : StateSpace t (@TraceElem ctx) :=
      {| chain_rule := model_chain_rule; |}.

    Definition initial_state (sut0 : SUT) :=
      fun m =>
        let init_state_p := h_initial_state Handler in
        model_sut m = sut0 /\
        init_state_p (model_handler m).
  End defn.

  Section commute.
    Open Scope hoare_scope.
    Context {PID} {SUT : Type} (Handler : @Handler.t PID).
    Let ctx := hToCtx Handler.
    Context {sys_t1 sys_t2 : Type} `{Runnable ctx sys_t1} `{Runnable ctx sys_t2}.
    Let S := @t PID (sys_t1 * sys_t2) Handler.
    Let T := @Trace ctx.

    (* Definition systems_commute (sys1 : sys_t1) (sys2 : sys_t2) : *)
    (*   forall (tr : T) (P Q : S -> Prop), *)
    (*     unfolds_to (sys1, sys2) tr -> *)
    (*     {{ P }} tr {{ Q }}. *)
  End commute.
End Model.

Module ExampleModelDefn.
  Section defns.
    Let PID := nat.

    Let Handler := compose (Mutable.t PID nat (fun a => a = 0))
                           (Mutex.t PID).

    Let ctx := hToCtx Handler.
    Let TE := @TraceElem ctx.

    Notation "'do' V '<-' I ; C" := (@t_cont ctx _ (I) (fun V => C))
                                      (at level 100, C at next level, V ident, right associativity).

    Notation "'done' I" := (@t_cont ctx _ (I) (fun _ => t_dead))
                             (at level 100, right associativity).

    Notation "pid '@' ret '<~' req" := (@trace_elem ctx pid req ret).

    Let put (val : nat) : Handler.(h_req) :=
      inl (Mutable.put val).

    Let get : h_req Handler :=
      inl (Mutable.get).

    Let grab : h_req Handler :=
      inr (Mutex.grab).

    Let release : h_req Handler :=
      inr (Mutex.release).

    (* Just a demonstration how to define a program that loops
    indefinitely, as long as it does IO: *)
    Local CoFixpoint infinite_loop (self : PID) : @Thread ctx self :=
      do _ <- put 0;
      infinite_loop self.

    (* Data race example: *)
    Let counter_race (self : PID) : @Thread ctx self :=
      do v <- get;
      done put (v + 1).

    (* Fixed example: *)
    Let counter_correct (self : PID) : @Thread ctx self :=
      do _ <- grab;
      do v <- get;
      let v' := v + 1 in
      do _ <- put v';
      done release.

    Let SUT := (counter_correct 1, counter_correct 2).
  End defns.
End ExampleModelDefn.
