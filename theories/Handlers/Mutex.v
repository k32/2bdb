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

  Let ctx := mkCtx PID req_t ret_t.
  Let TE := @TraceElem ctx.

  Inductive mutex_chain_rule : state_t -> state_t -> TE -> Prop :=
  | mutex_grab : forall pid,
      mutex_chain_rule None (Some pid) (trace_elem ctx pid grab I)
  | mutex_release_ok : forall pid,
      mutex_chain_rule (Some pid) None (trace_elem ctx pid release true)
  | mutex_release_fail : forall pid,
      mutex_chain_rule None None (trace_elem ctx pid release false).

  Definition t : t :=
    {|
      h_state         := state_t;
      h_req           := req_t;
      h_initial_state := fun s0 => s0 = None;
      h_chain_rule    := mutex_chain_rule
    |}.

  Notation "pid '@' ret '<~' req" := (@trace_elem ctx pid req ret).

  Theorem no_double_grab_0 : forall (a1 a2 : PID),
      ~(@PossibleTrace PID t [a1 @ I <~ grab;
                              a2 @ I <~ grab]).
  Proof.
    intros a1 a2 H.
    destruct H as [s [s' H]].
    unfold_trace_deep H.
    discriminate.
  Qed.

  Let state_space := state_t. Let trace_elem := req_t.

  Theorem no_double_grab : forall (a1 a2 : PID),
      {{ fun (_ : h_state t) => True }}
        [a1 @ I <~ grab;
         a2 @ I <~ grab]
      {{ fun _ => False}}.
  Proof.
    intros a1 a2 s s' Hss' Hpre.
    unfold_trace_deep Hss'.
    discriminate.
  Qed.
End defs.
