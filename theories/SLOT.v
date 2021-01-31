(** * SLOT: a formally verified model checker *)

(** SLOT is a collection of definitions and tactics for verification
of safety properties of concurrent and distributed functional programs
doing I/O, based on Hoare logic. SLOT models have the following
properties:

- Verified systems are written in a shallow-embedded DSL, and take
  advantage of most Gallina features. They can be extracted to CPS
  programs in Ocaml or Haskell via Coq's extraction feature

- Users can define their own I/O operations (called syscalls from now
  on)

- Syscall definitions can be composed together, and all theorems about
  the individual syscall types hold for the combined system

- Syscalls can be nondeterminisic

- Current version of SLOT doesn't support verification of liveness
  properties

Some notes on the naming: originally SLOT stood for Separation Logic
Of Traces, but the current implementation has nothing to do with
separation logic. However this name was catchy, so it stuck.

* Motivation

Before diving into lengthy description of the model, let me first
motivate a skeptical reader:

** Q: Why not TLA+?

A: In SLOT the verified system is clearly separated from the I/O
model, and therefore its definition looks much like conventional
functional program. It makes extraction of the verified code easier
(at least in theory). Model of the non-deterministic I/O is
separated. This leads to much more structured definitions and proofs.

Another obvious difference is that SLOT is entirely based on Coq and
makes heavy use of inductive datatypes and symbolic evaluation under
the hood. This has both advantages and disadvantages:

- SLOT is much less automated, but it can work with inductive
  definitions and anything that can be expressed in Coq

- SLOT model checker outputs Coq proofs, ultimately it means that it
  needs to store all execution histories. Given that the number of
  histories grows exponentially, solving large proofs by pure
  bruteforce is impossible. Although this disadvantage is partially
  mitigated by several formally-verified branch-pruning algorithms, it
  means proofs about large systems should be split to lemmas

- Verified program can be extracted

- While TLA+ model checker is top notch, its proof language is not

** Q: Why not (insert model checker name)?

A: Model checkers show why the code _fails_, which is suitable for
verifying algorithms, but structured formal proofs show why the code
_works_ (via tree of assumptions). It allows to reason about
algorithms and, in particular, to predict the outcome of
optimizations. Also model checkers typically can't work with infinite
state space, while SLOT can do it to some extend via magic of Coq.

** Q: Why not Verdi?

https://github.com/uwplse/verdi

- Nondeterminisic part of Verdi is hardcoded, while SLOT allows user
  to define custom IO handlers

- Verdi models are low level: think UDP packets and disk iops. SLOT
  can work with higher-level I/O handlers: think databases and pubsub
  services.

** Q: Why not disel?

https://github.com/DistributedComponents/disel

A: disel models are closer to what I need, but implementation itself
is an incomprehensible, impenetrable wall of ssreflect. Proofs are
only as useful as their premises: "garbage in - garbage out". Good
model should be well documented and well understood.

** Q: Why not iris/aneris?

https://gitlab.mpi-sws.org/iris/iris

A: iris allows user to define semantics of their very own programming
language. SLOT is focused on proving properties of _regular pure
functinal programs_ that do IO from time to time. Hence it defines
actors in regular Gallina language, rather than some DSL, and frees
the user from reinventing basic control flow constructions.

* Navigating the code

** Core definitions

 - [LibTx.SLOT.Hoare] module contains definitions used to describe a
   single execution history

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

    Record t : Type :=
      mkModel
        { model_sut : SUT;
          model_handler : h_state Handler;
        }.

   Context `{Runnable  SUT}.

    Definition model_state_transition m m' te : Prop :=
      match m, m' with
      | mkModel s h, mkModel s' h' => (h_state_transition Handler) h h' te /\
                                     runnable_step s s' te
      end.

    Global Instance modelStateSpace : StateSpace t (@TraceElem ctx) :=
      {| state_transition := model_state_transition; |}.
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

(*
Module ExampleModelDefn.
  Section handler.
    Context {PID : Type}.

    Definition Handler := AtomicVar.t nat <+> mutexHandler PID.
  End handler.

  Let req := get_handler_req (@Handler).
  Let ret := get_handler_ret (@Handler).

  Section defs.
    (* Let req : Type := (@avar_req_t nat + req_t).     *)
    Context {PID : Type}.

    Definition put (val : nat) : req :=
      inl (AtomicVar.write val).

    Definition get : req :=
      inl (AtomicVar.read).

    Definition grab : req :=
      inr (Mutex.grab).

    Definition release : req :=
      inr (Mutex.release).

    Let Thread := @Thread req ret.

    (* Just a demonstration how to define a program that loops
    indefinitely, as long as it does IO: *)

    CoFixpoint infinite_loop (self : PID) : Thread :=
      do _ <- put 0;
      infinite_loop self.

    (* Data race example: *)
    Definition inc (n : nat) ret : Thread :=
      do v <- get;
      do _ <- put (v + n);
      ret (v + n).

    (* Fixed example: *)
    Definition counter_correct (self : PID) :=
      do _ <- grab;
      call x <- inc 1;
      done release.

    (* Definition nop (self : PID) : Thread := *)
    (*   @throw ctx "Exception".  TODO *)
  End defs.

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
      {{ fun s  => True }}
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

    Goal -{{ fun (s : h_state Handler) => fst s = 0 }} PairEnsemble {{ fun s => fst s = 2 }}.
    Proof.
      intros t Ht.
      unfold_ht.
      cbn in Hpre.
      bruteforce Ht Hls;
      cbn in *; repeat match goal with
                         [ H : _ /\ _ |- _] => destruct H
                       end; subst; auto.
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
*)
