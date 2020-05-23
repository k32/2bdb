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
     SLOT.Process
     SLOT.Ensemble.

From Coq Require Import
     List.

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

    Global Instance modelStateSpace : StateSpace t (@TraceElem ctx) :=
      {| chain_rule := model_chain_rule; |}.

    Definition initial_state (sut0 : SUT) :=
      fun m =>
        let init_state_p := h_initial_state Handler in
        model_sut m = sut0 /\
        init_state_p (model_handler m).
  End defn.

  (* Helper function for infering type of model: *)
  Definition model_t {SUT} {PID} (sut : SUT) (h : @Handler.t PID) : Type :=
    @t PID SUT h.
End Model.

Module ExampleModelDefn.
  Require Import
          Handlers.Mutex
          Handlers.Mutable.

  Import Model.

  Section defns.
    Context {PID : Set}.

    Definition Handler := compose (Mutable.t PID nat (fun a => a = 0))
                                  (Mutex.t PID).

    Definition ctx := hToCtx Handler.
    Definition TE := @TraceElem ctx.

    Notation "'do' V '<-' I ; C" := (@t_cont ctx (I) (fun V => C))
                                      (at level 100, C at next level, V ident, right associativity).

    Notation "'done' I" := (@t_cont ctx (I) (fun _ => t_dead))
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
    Local CoFixpoint infinite_loop (self : PID) : @Thread ctx :=
      do _ <- put 0;
      infinite_loop self.

    (* Data race example: *)
    Definition counter_race (self : PID) : @Thread ctx :=
      do v <- get;
      done put (v + 1).

    (* Fixed example: *)
    Definition counter_correct (self : PID) : @Thread ctx :=
      do _ <- grab;
      do v <- get;
      let v' := v + 1 in
      do _ <- put v';
      done release.

  End defns.

  Section simple.
    Let PID := True.
    Let ctx := @ctx PID.

    Let SUT := counter_correct I.
    Let Handler := @Handler PID.

    Let Model := model_t SUT Handler.

    Let counter_invariant (sys : Model) : Prop :=
      match sys with
        {| model_sut := sut; model_handler := (M, l) |} =>
        match l with
        | Some _ => True
        | None =>
          let n_alive := match sut with
                         | t_dead => 0
                         | t_cont _ _ => 1
                         end
          in n_alive + M = 1
        end
      end.

    Goal forall h0, h_initial_state Handler h0 ->
               @PointInvariant Model TE modelStateSpace counter_invariant
                               (mkModel (counter_correct I) h0).
    Proof.
      intros.
      destruct h0 as [val0 mtx0].
      firstorder. simpl in H, H0. subst.



  End simple.

    Let n_alive_plus_m (sys : Model) : Prop :=
      match sys with
        {| model_sut := sut; model_handler := (M, l) |} =>
        match l with
        | Some _ => True
        | None =>
          let n_alive := Vector.fold_left (fun x t => match t with
                                                   | t_dead => x
                                                   | _ => S x
                                                   end) 0 sut
          in n_alive + M = N
        end
      end.

    Lemma counter_invariant : @Invariant Model TE modelStateSpace n_alive_plus_m.
    Proof.
      unfold Invariant.
      intros.
      unfold n_alive_plus_m in H.
      destruct s as [sut [num mutex]].
      destruct s' as [sut' [num' mutex']].
      simpl in H0.
      intuition.
      inversion_ H2.
      destruct mutex.
      2: {
  End defns.
End ExampleModelDefn.
