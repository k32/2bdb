(** * Generic total deterministic IO handler *)
From LibTx Require Import
     SLOT.EventTrace
     SLOT.Handler.

Section defs.
  Context (PID S req_t : Set)
          (ret_t : req_t -> Set)
          (initial_state : S -> Prop).

  Definition ctx := mkCtx PID req_t ret_t.
  Let TE := @TraceElem ctx.

  Variable chain_rule : forall (s : S) (req : req_t), S * ret_t req.

  Inductive det_chain_rule : S -> S -> TE -> Prop :=
  | det_step : forall s s' pid req ret,
      (s', ret) = chain_rule s req ->
      det_chain_rule s s' (trace_elem ctx pid req ret).

  Definition t : t :=
    {|
      h_state := S;
      h_req := req_t;
      h_initial_state := initial_state;
      h_chain_rule := det_chain_rule;
    |}.
End defs.
