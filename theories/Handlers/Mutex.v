From Coq Require Import
     List.

Import ListNotations.

From LibTx Require Import
     SLOT.EventTrace
     SLOT.Hoare
     SLOT.Handler.

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

  Let TE := @TraceElem PID req_t ret_t.

  Inductive mutex_chain_rule : state_t -> state_t -> TE -> Prop :=
  | mutex_grab : forall pid,
      mutex_chain_rule None (Some pid) (trace_elem pid grab I)
  | mutex_release_ok : forall pid,
      mutex_chain_rule (Some pid) None (trace_elem pid release true)
  | mutex_release_fail : forall pid,
      mutex_chain_rule None None (trace_elem pid release false).

  Global Instance mutexHandler : @Handler PID req_t ret_t :=
    { h_state := state_t;
      h_chain_rule := mutex_chain_rule;
    }.

  Theorem no_double_grab_0 : forall (a1 a2 : PID),
      ~(PossibleTrace [a1 @ I <~ grab;
                       a2 @ I <~ grab]).
  Proof.
    intros a1 a2 H.
    destruct H as [s [s' H]].
    unfold_trace_deep H.
    discriminate.
  Qed.

  Theorem no_double_grab : forall (a1 a2 : PID),
      {{ fun _  => True }}
        [a1 @ I <~ grab;
         a2 @ I <~ grab]
      {{ fun _ => False}}.
  Proof.
    intros a1 a2 s s' Hss' Hpre.
    unfold_trace_deep Hss'.
    discriminate.
  Qed.
End defs.

Ltac mutex_contradiction :=
  match goal with
    [H1 : mutex_chain_rule _ ?s1 ?s2 _, H2 : mutex_chain_rule _ ?s2 ?s3 _ |- _] =>
      inversion H1; inversion H2; subst; discriminate
  end.

Hint Extern 4 => mutex_contradiction : handlers.

Ltac clear_mutex :=
  repeat match goal with
           [H: mutex_chain_rule _ _ _ _ |- _] => clear H
         end.
