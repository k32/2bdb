(** * Separation Logic of Traces *)
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
     String
     List.

(*Module Model.
  Section defn.
    Context {PID} {SUT : Type} {Handler : @Handler.t PID}.
    Let ctx := hToCtx Handler.

    Record t : Type :=
      mkModel
        { model_sut : SUT;
          model_handler : h_state Handler;
        }.

   Context `{Runnable  SUT}.

    Definition model_chain_rule m m' te : Prop :=
      match m, m' with
      | mkModel s h, mkModel s' h' => (h_chain_rule Handler) h h' te /\
                                     runnable_step s s' te
      end.

    Global Instance modelStateSpace : StateSpace t (@TraceElem ctx) :=
      {| chain_rule := model_chain_rule; |}.
  End defn.

  (* Helper function for infering type of model: *)
  Definition model_t {SUT} {PID} (sut : SUT) (h : @Handler.t PID) : Type :=
    @t PID SUT h.
End Model. *)

Ltac bruteforce Ht Hls :=
  let Ht' := type of Ht in
  match eval lazy in Ht' with
  | ThreadGenerator _ _ _ =>
    unfold_thread Ht
  | Parallel ?e1 ?e2 ?t =>
    let t1 := fresh "t_l" in
    let t2 := fresh "t_r" in
    let H1 := fresh "H" t1 in
    let H2 := fresh "H" t2 in
    let t := fresh "t" in
    let Hint := fresh "Hint_" t in
    destruct Ht as [t1 t2 t H1 H2 Hint];
    bruteforce H1 Hls; subst; bruteforce H2 Hls;
    unfold_interleaving Hint with trace_step Hls
  end.

Require Import
        Handlers.Mutex
        Handlers.Deterministic.

Module ExampleModelDefn.
  Section defns.
    Context {PID : Set}.

    Definition Handler := @AtomicVar.t PID nat _ <+> Mutex.t PID.

    Definition TE := @TraceElem PID (h_req Handler) (h_ret Handler).

    Let Thread := @Thread (h_req Handler) (h_ret Handler).

    Definition put (val : nat) : Handler.(h_req) :=
      inl (AtomicVar.write val).

    Definition get : h_req Handler :=
      inl (AtomicVar.read).

    Definition grab : h_req Handler :=
      inr (Mutex.grab).

    Definition release : h_req Handler :=
      inr (Mutex.release).

    (* Just a demonstration how to define a program that loops
    indefinitely, as long as it does IO: *)
    Local CoFixpoint infinite_loop (self : PID) : Thread :=
      do _ <- put 0;
      infinite_loop self.

    (* Data race example: *)
    Definition inc (n : nat) cont : Thread :=
      do v <- get;
      do _ <- put (v + n);
      cont (v + n).

    (* Fixed example: *)
    Definition counter_correct (self : PID) :=
      do _ <- grab;
      call x <- inc 1;
      done release.

    (* Definition nop (self : PID) : Thread := *)
    (*   @throw ctx "Exception".  TODO *)
  End defns.

  Section simple.
    Let PID := bool.

    Let SUT := counter_correct I.
    Let Handler := @Handler PID.

    Let mk_counter (pid : PID) := ThreadGenerator pid (counter_correct pid).
    Let SingletonEnsemble := mk_counter true.
    Let PairEnsemble := (mk_counter true) -|| (mk_counter false).
    Let InfLoopEnsemble := ThreadGenerator true (infinite_loop true).

    Goal EnsembleInvariant (fun _ => True) SingletonEnsemble.
    Proof.
      intros t Ht.
      unfold_thread Ht. subst.
      now repeat constructor.
    Qed.

    Goal EnsembleInvariant (fun _ => True) SingletonEnsemble.
    Proof.
      intros t Ht.
      unfold_thread Ht. subst.
      now repeat constructor.
    Qed.

    Goal forall v1 v2,
      {{ fun s => True }}
        [true @ v1 <~ get;
         true @ I <~ grab;
         true @ v2 <~ get;
         false @ I <~ grab;
         true @ I <~ grab]
      {{ fun s => False }}.
    Proof.
      intros v1 v2.
      unfold_ht.
      repeat trace_step Hls.
    Qed.

    Goal -{{ fun (s : h_state Handler)  => fst s = 0 }} PairEnsemble {{ fun s => fst s = 2 }}.
    Proof.
      intros t Ht.
      unfold_ht.
      cbn in Hpre.
      bruteforce Ht Hls;
        firstorder;
        cbn in *; now subst.
    Qed.

    (*Let counter_invariant (sys : Model) : Prop :=
      match sys with
        mkModel sut (M, l) =>
        match l with
        | Some _ => True
        | None =>
          let n_alive := match sut with
                         | t_dead => 0
                         | t_cont _ _ => 1
                         end
          in n_alive + M = 1
        end
      end.*)
  End simple.
End ExampleModelDefn.
