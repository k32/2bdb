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
     String
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
        match m with
        | {| model_sut := sut; model_handler := h |} =>
          sut = sut0 /\ h_initial_state Handler h
        end.

    Definition SystemInvariant (prop : t -> Prop) (sut : SUT) :=
      @SystemInvariant t _ modelStateSpace prop (initial_state sut).

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

    Definition put (val : nat) : Handler.(h_req) :=
      inl (Mutable.put val).

    Definition get : h_req Handler :=
      inl (Mutable.get).

    Definition grab : h_req Handler :=
      inr (Mutex.grab).

    Definition release : h_req Handler :=
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

    Definition nop (self : PID) :=
      @throw ctx "Exception".
  End defns.

  Notation "pid '@' ret '<~' req" := (@trace_elem ctx pid req ret).

  Section simple.
    Let PID := bool.
    Let ctx := @ctx PID.

    Let SUT := counter_correct I.
    Let Handler := @Handler PID.

    Let Model := model_t SUT Handler.

    Let mk_counter pid := @ThreadGenerator ctx pid (counter_correct pid).
    Let SingletonEnsemble := mk_counter true.
    Let PairEnsemble := (mk_counter true) -|| (mk_counter false).
    Let NopEnsemble := @ThreadGenerator ctx true (nop true).

    Goal forall t, NopEnsemble t -> True.
      intros t Ht.
      unfold_thread Ht.
      easy.
    Qed.

    Goal EnsembleInvariant (fun _ => True) SingletonEnsemble.
    Proof.
      intros t Ht.
      unfold_thread Ht. subst.
      repeat (constructor; try easy).
    Qed.

    Goal EnsembleInvariant (fun _ => True) SingletonEnsemble.
    Proof.
      intros t Ht.
      unfold_thread Ht. subst.
      repeat (constructor; try easy).
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

    Ltac destruct_tuple tup a b :=
      let t0 := fresh "t" in
      let eq := fresh "Heq" in
      remember tup as t0 eqn:eq;
      destruct tup as [a b];
      subst t0;
      repeat match goal with
             | [H : (a,b) = (_,_) |- _] => inversion_clear H
             | [H : (_,_) = (a,b) |- _] => inversion_clear H
             end.

    Goal forall {A} (a b : A * A), a = b -> fst a = fst b.
      intros.
      destruct_tuple a al ar.
      destruct_tuple b bl br.
      easy.
    Qed.

    Ltac unfold_compose_handler H s s' :=
      let l := fresh "s__l" in
      let r := fresh "s__r" in
      let l' := fresh "s__l" in
      let r' := fresh "s__r" in
      let Hcr_l := fresh H "_l" in
      let Hcr_r := fresh H "_r" in
      match s with
      | (_, _) => idtac
      | _ => destruct_tuple s l r
      end;
      destruct_tuple s' l' r';
      destruct H as [H];
      simpl in H;
      destruct H as [Hcr_l Hcr_r];
      match type of Hcr_l with
      | ?x = l' => subst l'; rename Hcr_r into H
      | _       => subst r'; rename Hcr_l into H
      end;
      idtac.

    Ltac handler_step' Hcr :=
      simpl in Hcr;
      match type of Hcr with
      | ComposeChainRule ?Hl ?Hr ?s ?s' ?te =>
        unfold_compose_handler Hcr s s'
      end.

    Ltac trace_step f :=
      simpl in f;
      match type of f with
      | LongStep _ [] _ =>
        let s := fresh "s" in
        let Hx := fresh "Hx" in
        let Hy := fresh "Hy" in
        let Hz := fresh "Hz" in
        inversion f as [s Hx Hy Hz|];
        subst s; clear f; clear Hy
      | LongStep _ (_ :: _) _ =>
        let s' := fresh "s" in
        let te := fresh "te" in
        let tail := fresh "tail" in
        let Hcr := fresh "Hcr" in
        let Htl := fresh "Htl" in
        inversion_clear f as [|? s' ? te tail Hcr Htl];
        rename Htl into f;
        repeat handler_step' Hcr;
        auto with handlers
      end.

    Goal {{ h_initial_state Handler }}
           [true @ I <~ grab; false @ I <~ grab; true @ I <~ grab]
         {{ fun s => False }}.
    Proof.
      unfold_ht.
      trace_step Hls.
      trace_step Hls.
    Qed.

    Ltac unfold_interleaving H Hls :=
      simpl in H;
      match type of H with
      | Interleaving [] _ _ =>
        apply interleaving_nil in H;
        rewrite <-H in *; clear H;
        repeat trace_step Hls
      | Interleaving _ [] _ =>
        apply interleaving_symm, interleaving_nil in H;
        rewrite <-H in *; clear H
      | Interleaving ?tl ?tr ?t =>
        let tl0 := fresh "tl" in
        let Htl0 := fresh "Heql"  in
        let tr0 := fresh "tr" in
        let Htr0 := fresh "Heqr" in
        let te := fresh "te" in
        let tl' := fresh "tl" in
        let tr' := fresh "tr" in
        let t := fresh "t" in
        remember tl as tl0 eqn:Htl0;
        remember tr as tr0 eqn:Htr0;
        destruct H as [te tl' tr' t H | te tl' tr' t H | tr' | tl'];
        repeat (match goal with
                | [H : _ :: _ = _ |- _] =>
                  inversion H; subst; clear H
                end);
        discriminate || (try subst te;
                        trace_step Hls;
                        unfold_interleaving H Hls)
      end.

    Ltac bruteforce Ht Hls :=
      try lazy in Ht;
      match type of Ht with
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
        unfold_interleaving Hint Hls
      end.

    Goal -{{ h_initial_state Handler }} PairEnsemble {{ fun s => fst s = 2 }}.
    Proof.
      intros t Ht.
      unfold_ht.
      bruteforce Ht Hls.
    Abort.

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
  End simple.

End ExampleModelDefn.
