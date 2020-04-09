From Coq Require Import
     String.

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

  CoInductive Thread {pid : PID} : Type :=
  | t_dead : Thread
  | t_cont :
      forall (pending_req : Req)
        (continuation : Ret pending_req -> Thread)
      , Thread.

  Definition throw {pid} (_ : string) := @t_dead pid.

  Inductive ThreadStep (pid : PID) : @Thread pid -> @Thread pid -> TE -> Prop :=
  | thread_step : forall req ret cont,
      ThreadStep pid
                 (t_cont req cont) (cont ret)
                 (trace_elem _ pid req ret).

  Hint Constructors ThreadStep.

  Global Instance runnableThread (pid : PID) : Runnable (@Thread pid) :=
    {| runnable_step := ThreadStep pid |}.

  Global Instance runnableHoare {A} `{Runnable A} : StateSpace A TE :=
    {| chain_rule := runnable_step; |}.

  Global Instance runnableGenerator {A} `{Runnable A} : Generator A :=
    {| unfolds_to g t := exists g', LongStep g t g';
    |}.
End defn.

Section ComposeSystems.
  Context {ctx : Ctx} {sys1 sys2 : Type}.

  Global Instance composeRunnable `{@Runnable ctx sys1} `{@Runnable ctx sys2} :
    @Runnable ctx (sys1 * sys2) :=
    {| runnable_step s s' te :=
         match s, s' with
         | (s1, s2), (s1', s2') => (runnable_step s1 s1' te /\ s2 = s2') \/
                                  (runnable_step s2 s2' te /\ s1 = s1')
         end;
    |}.
End ComposeSystems.
