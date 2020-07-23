From Coq Require
     List
     String
     Vector.

Import String.
Import List.
Import List.ListNotations.

From LibTx Require Import
     FoldIn
     SLOT.Hoare
     SLOT.Ensemble
     SLOT.EventTrace.

Open Scope hoare_scope.

Section defn.
  Context {PID Req : Type} {Ret : Req -> Type}.

  Let TE := @TraceElem PID Req Ret.
  Let T := @Trace PID Req Ret.

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
      let te := trace_elem pid req ret in
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

  Definition finale {T : Type} (_ : T) := t_dead.

  (* Inductive ThreadsStep : Threads -> Threads -> TE -> Prop := *)
  (* | threads_step : forall pid te threads thread' (HIn : MapInterface.In pid threads), *)
  (*     ThreadStep pid (find' pid threads HIn) thread' te -> *)
  (*     ThreadsStep threads (Map.add pid thread' threads) te. *)
End defn.

Notation "'do' V '<-' I ; C" := (t_cont (I) (fun V => C))
                                  (at level 100, C at next level, V ident, right associativity).

Notation "'done' I" := (t_cont (I) (fun _ => t_dead))
                         (at level 100, right associativity).

Notation "'call' V '<-' I ; C" := (I (fun V => C))
                                   (at level 100, C at next level, V ident,
                                    right associativity,
                                    only parsing).

Section props.
  (* Context `{ctx : EvtContext}. *)
  Context {PID Req : Type} {Ret : Req -> Type}.

  Lemma dead_thread : forall t (pid : PID),
      @ThreadGenerator PID Req Ret pid t_dead t -> t = [].
  Proof.
    intros t pid Ht.
    remember t_dead as thread.
    destruct Ht.
    - reflexivity.
    - simpl in *. subst. contradiction.
  Qed.
End props.

Ltac unfold_cont Ht Hstep :=
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

Ltac thread_step Ht :=
  lazy in Ht;
  match type of Ht with
  | ThreadGenerator _ (match ?var with _ => _ end) _ =>
    destruct var;
    thread_step Ht
  | ThreadGenerator ?pid ?thread ?trace =>
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
      unfold_cont Ht Hstep;
      [inversion eq
      |rewrite eq in Hstep;
       destruct Hstep as [Hreq Ht'];
       rewrite Ht' in Ht; clear Ht';
       match type of Hreq with
       | ?req = ?val => subst req
       end
      ]
    end
  | ?wut =>
    fail 1 "I don't know how to unfold" wut
  end.

Ltac unfold_thread Ht stop_tac :=
  thread_step Ht;
  try first [ stop_tac Ht | unfold_thread Ht stop_tac].

Tactic Notation "unfold_thread" ident(Ht) "until" tactic3(stop_tac) :=
  unfold_thread Ht stop_tac.

Tactic Notation "unfold_thread" ident(Ht) :=
  let Ht_t0 := type of Ht in
  let Ht_t := eval compute in Ht_t0 in
  unfold_thread Ht until
                (fun Ht' =>
                   let Ht'_t := type of Ht' in
                   match eval compute in (Ht'_t = Ht_t) with
                         | ?a = ?a => idtac "Loop detected: " Ht_t "Stopping."
                         end).

Module tests.
  Inductive req_t :=
  | foo : req_t
  | bar : nat -> req_t.

  Let ret_t := fun x => match x with
                     | foo => bool
                     | bar _ => nat
                     end.
  Let pid_t := nat.

  (* Regular linear code: *)
  Let regular : @Thread req_t ret_t :=
    do x <- bar 1;
    done bar x.

  Goal forall t,
      (ThreadGenerator 1 regular) t ->
      exists x y, t = [1 @ x <~ bar 1;
                  1 @ y <~ bar x].
  Proof.
    intros.
    unfold_thread H.
    exists ret. exists ret0.
    reflexivity.
  Qed.

  (* Branching: *)
  Let branching1 : @Thread req_t ret_t :=
    do x <- bar 1;
    match x with
    | 0 =>
      do _ <- bar (x + 1);
      done foo
    | _ =>
      done foo
    end.

  Goal forall t,
      (ThreadGenerator 1 branching1) t ->
      (exists x y, t = [1 @ 0 <~ bar 1;
                   1 @ x <~ bar 1;
                   1 @ y <~ foo]) \/
      (exists x y, t = [1 @ S x <~ bar 1;
                   1 @ y <~ foo]).
  Proof.
    intros.
    now unfold_thread H; [left|right]; exists ret; exists ret0.
  Qed.

  (* Loops: *)
  Local CoFixpoint infinite_loop (self : pid_t) : @Thread req_t ret_t :=
    do _ <- foo;
    do _ <- bar 1;
    infinite_loop self.

  Let InfLoopEnsemble := ThreadGenerator 1 (infinite_loop 1).

End tests.
