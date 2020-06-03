From Coq Require
     List
     String
     Vector.

Import String.
Import List.
Import List.ListNotations.

From Containers Require
     OrderedType
     MapInterface
     MapFacts
     MapAVLInstance.

Module Map := MapInterface.

From LibTx Require Import
     FoldIn
     SLOT.Hoare
     SLOT.Ensemble
     SLOT.EventTrace.

Open Scope hoare_scope.

Section defn.
  Context {ctx : Ctx}.

  Let PID := ctx_pid_t ctx.
  Let Req := ctx_req_t ctx.
  Let Ret := ctx_ret_t ctx.

  Context `{Hord : OrderedType.OrderedType PID}.

  Let TE := @TraceElem ctx.
  Let T := @Trace ctx.

  Class Runnable A : Type :=
    { runnable_step : A -> A -> TE -> Prop;
    }.

  CoInductive Thread : Type :=
  | t_dead : Thread
  | t_cont :
      forall (pending_req : Req)
        (continuation : Ret pending_req -> Thread)
      , Thread.

  Definition throw (_ : string) := t_dead.

  Definition threadStep (s s' : Thread) (te : TE) : Prop.
    destruct te as [pid req ret].
    destruct s as [|req' cont].
    - exact False. (* Dead threads can't run *)
    - refine ({Hreq : req = req' | s' = cont _}).
      subst.
      exact ret.
  Defined.

  Inductive ThreadGenerator pid : Thread -> TraceEnsemble :=
  | tg_nil : ThreadGenerator pid t_dead []
  | tg_cons : forall req ret t t' trace,
      let te := trace_elem _ pid req ret in
      threadStep t t' te ->
      ThreadGenerator pid t' trace ->
      ThreadGenerator pid t (te :: trace).

  Global Instance threadGen pid : Generator Thread :=
    { unfolds_to := ThreadGenerator pid;
    }.

  Global Instance runnableThread : Runnable Thread :=
    {| runnable_step := threadStep |}.

  Global Instance runnableHoare {A} `{Runnable A} : StateSpace A TE :=
    {| chain_rule := runnable_step |}.

  Global Instance runnableGenerator {A} `{Runnable A} : Generator A :=
    {| unfolds_to g t := exists g', LongStep g t g' |}.

  (* Inductive ThreadsStep : Threads -> Threads -> TE -> Prop := *)
  (* | threads_step : forall pid te threads thread' (HIn : MapInterface.In pid threads), *)
  (*     ThreadStep pid (find' pid threads HIn) thread' te -> *)
  (*     ThreadsStep threads (Map.add pid thread' threads) te. *)
End defn.

Lemma dead_thread : forall ctx t pid,
    @ThreadGenerator ctx pid t_dead t -> t = [].
Proof.
  intros _ctx t pid Ht.
  remember t_dead as thread.
  destruct Ht.
  - reflexivity.
  - simpl in t0. subst. contradiction.
Qed.

Ltac thread_step Ht Hstep :=
  let s0 := fresh "s" in
  let Heq := fresh "Heq" in
  let req := fresh "req" in
  let ret := fresh "ret" in
  let t := fresh "t" in
  let t' := fresh "t" in
  let trace := fresh "trace" in
  let te := fresh "te" in
  match type of Ht with
  | ThreadGenerator _ ?thread _ =>
    destruct Ht as [|req ret t t' trace te Hstep Ht];
    [idtac
    |simpl in te;
     subst te;
     simpl in req, ret, Hstep, Ht
    ]
  end.

Ltac unfold_thread Ht :=
  try lazy in Ht;
  match type of Ht with
    ThreadGenerator ?pid ?thread ?trace =>
    match eval lazy in thread with
    | t_dead =>
      apply dead_thread in Ht;
      try (rewrite Ht in *; clear Ht)
    | (t_cont ?req ?cont) =>
      let t := fresh "t" in
      let eq := fresh "Heq" t in
      let Hstep := fresh "Hstep" in
      let Hreq := fresh "Hreq" in
      let Ht' := fresh "Ht" in
      remember thread as t eqn:eq;
      thread_step Ht Hstep;
      [inversion eq
      |rewrite eq in Hstep;
       destruct Hstep as [Hreq Ht'];
       rewrite Ht' in Ht; clear Ht';
       (* rewrite Hreq in *; clear Hreq *)
       unfold_thread Ht
      ]
    end
  end.
