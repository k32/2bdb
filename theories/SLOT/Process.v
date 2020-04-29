From Coq Require
     String
     Vector.

Import String.
Module Vec := Vector.

From LibTx Require Import
     SLOT.Hoare
     SLOT.Ensemble
     SLOT.EventTrace.

Open Scope hoare_scope.

Section defn.
  Context {ctx : Ctx}.

  Let PID := ctx_pid_t ctx.
  Let Req := ctx_req_t ctx.
  Let Ret := ctx_ret_t ctx.

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

  Inductive ThreadStep (pid : PID) : Thread -> Thread -> TE -> Prop :=
  | thread_step : forall req ret cont,
      ThreadStep pid
                 (t_cont req cont) (cont ret)
                 (trace_elem _ pid req ret).

  Hint Constructors ThreadStep.

  Global Instance runnableThread (pid : PID) : Runnable Thread :=
    {| runnable_step := ThreadStep pid |}.

  Global Instance runnableHoare {A} `{Runnable A} : StateSpace A TE :=
    {| chain_rule := runnable_step; |}.

  Global Instance runnableGenerator {A} `{Runnable A} : Generator A :=
    {| unfolds_to g t := exists g', LongStep g t g';
    |}.
End defn.

Section ComposeSystems.
  Context {ctx : Ctx} {sys1 sys2 : Type} `{@Runnable ctx sys1} `{@Runnable ctx sys2}.

  Let S : Type := sys1 * sys2.

  Inductive composeRunnableStep : S -> S -> _ -> Prop :=
  | cr_step_l : forall s_l s_l' s_r te,
      runnable_step s_l s_l' te ->
      composeRunnableStep (s_l, s_r) (s_l', s_r) te
  | cr_step_r : forall s_r s_r' s_l te,
      runnable_step s_r s_r' te ->
      composeRunnableStep (s_l, s_r) (s_l, s_r') te.

  Global Instance composeRunnable  :
    @Runnable ctx (sys1 * sys2) :=
    {| runnable_step := composeRunnableStep |}.
End ComposeSystems.

Section ReplicateSystem.
  Context {ctx : Ctx} {sys : Type} `{Runnable ctx sys}.

  Definition replicated {t} (N : nat) create : Vec.t t N :=
    Vec.map create (FoldIn.seq_vec N).

  Inductive replRunnableStep {N : nat} : Vec.t sys N -> Vec.t sys N -> _ -> Prop :=
  | repl_run_step : forall i vec s s' te,
      Vec.nth vec i = s ->
      runnable_step s s' te ->
      replRunnableStep vec (Vec.replace vec i s') te.

  Global Instance replicatedRunnable `{@Runnable ctx sys} {N} :
    @Runnable ctx (Vec.t sys N) :=
    {| runnable_step := replRunnableStep;
    |}.
End ReplicateSystem.
