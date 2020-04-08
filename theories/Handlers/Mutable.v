From Coq Require Import
     List.

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

  Let ctx := mkCtx PID req_t ret_t.
  Let TE := @TraceElem ctx.

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

  Fail Lemma mut_get_comm : forall v pid1 pid2, (*TODO*)
      trace_elems_commute (trace_elem ctx pid1 get v) (trace_elem ctx pid2 get v).
End defs.
