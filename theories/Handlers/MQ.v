From Coq Require Import
     List.

Import ListNotations.

From LibTx Require Import
     SLOT.EventTrace
     SLOT.Handler.

Section defs.
  Context (PID T : Set) (initial_state : T -> Prop).

  Definition Offset := nat.

  Inductive req_t :=
  | fetch : Offset -> req_t
  | produce : T -> req_t.

  Local Definition ret_t (req : req_t) : Set :=
    match req with
    | fetch _ => option T
    | produce _ => option Offset
    end.

  Definition ctx := mkCtx PID req_t ret_t.
  Let TE := @TraceElem ctx.
  Let S := list T.

  Notation "pid '@' ret '<~' req" := (@trace_elem ctx pid req ret).

  Inductive mq_chain_rule : S -> S -> TE -> Prop :=
  | mq_fetch : forall s pid offset,
      mq_chain_rule s s (pid @ nth_error s offset <~ fetch offset)
  | mq_produce : forall s pid val,
      mq_chain_rule s (val :: s) (pid @ Some (length s) <~ produce val)
  | mq_produce_lost_resp : forall s pid val, (* Response is lost *)
      mq_chain_rule s (val :: s) (pid @ None <~ produce val)
  | mq_produce_lost_msg : forall s pid val, (* Message is lost *)
      mq_chain_rule s s (pid @ None <~ produce val).

  Definition t : t :=
    {|
      h_state := S;
      h_req := req_t;
      h_initial_state := fun s => s = [];
      h_chain_rule := mq_chain_rule;
    |}.
End defs.
