From Coq Require Import
     List.

From Equations Require Import
     Equations.

Import ListNotations.

From LibTx Require Import
     SLOT.EventTrace
     SLOT.Handler.

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

  Definition ctx := mkCtx PID req_t ret_t.
  Let TE := @TraceElem ctx.

  Notation "pid '@' ret '<~' req" := (@trace_elem ctx pid req ret).

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

  Lemma mut_get_rewr : forall s s' pid ret,
      mut_chain_rule s s' (pid @ ret <~ get) ->
      s = s' /\ ret = s.
  Proof.
    intros.
    remember (pid @ ret <~ get) as te.
    inversion H.
    - subst te.
      inversion H2. subst pid.
      apply te_ret_eq in H2.
      firstorder.
    - now subst.
  Qed.

  Lemma mut_put_rewr : forall s s' pid v,
      mut_chain_rule s s' (pid @ I <~ put v) ->
      v = s'.
  Proof.
    intros.
    remember (pid @ I <~ put v) as te.
    inversion H.
    - now subst.
    - subst.
      now inversion H2.
  Qed.

  Fail Lemma mut_get_comm : forall v pid1 pid2, (*TODO*)
      trace_elems_commute (trace_elem ctx pid1 get v) (trace_elem ctx pid2 get v).
End defs.

Ltac elim_mut :=
  match goal with
  | [H: mut_chain_rule ?PID ?T ?s ?s' ?te |- _] =>
    lazymatch eval cbn in te with
    | trace_elem _ ?pid get ?ret =>
      apply mut_get_rewr in H;
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      destruct H as [H1 H2];
      subst s';
      subst ret
    | trace_elem _ ?pid (put ?v) ?ret =>
      try destruct ret;
      apply (mut_put_rewr PID T s s' pid) in H;
      subst s'
    end
  end.

Hint Extern 4 => elim_mut : handlers.

Section tests.
  Let PID := True.
  Let handler := t PID nat (fun s => s = 0).
  Let ctx := ctx PID nat.
  Notation "pid '@' ret '<~' req" := (trace_elem ctx pid req ret).

  Goal forall s s' pid ret,
      mut_chain_rule _ _ s s' (pid @ ret <~ get) -> s = ret.
  Proof.
    intros.
    auto with handlers.
  Qed.

  Goal forall s s' pid v,
      mut_chain_rule _ _ s s' (pid @ I <~ put v) -> s' = v.
  Proof.
    intros.
    auto with handlers.
  Qed.
End tests.
