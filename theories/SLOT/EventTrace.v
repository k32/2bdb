From Coq Require Import
     List.

Reserved Notation "pid '@' req '<~' ret" (at level 30).

Record Ctx : Type :=
  mkCtx { ctx_pid_t : Set;
          ctx_req_t : Set;
          ctx_ret_t : ctx_req_t -> Set;
        }.

Record TraceElem {ctx : Ctx} : Set :=
  trace_elem { te_pid : ctx_pid_t ctx;
               te_req : ctx_req_t ctx;
               te_ret : (ctx_ret_t ctx) te_req;
             }.

Definition Trace {ctx : Ctx} := list (@TraceElem ctx).

Notation "pid '@' ret '<~' req" := (trace_elem _ pid req ret).

Require Import ssreflect ssrfun.

Section props.
  Context {ctx : Ctx}.
  Let ret_t := ctx_ret_t ctx.

  Lemma te_ret_dual_elim pid (P : forall req, ret_t req -> Prop) req1 (ret1 : ret_t req1) req2 (ret2 : ret_t req2) :
      trace_elem ctx pid req1 ret1 = trace_elem ctx pid req2 ret2 ->
      P req1 ret1 ->
      P req2 ret2.
  Proof.
    by rewrite -[ret2]/(te_ret (trace_elem ctx pid req2 ret2))
               -[req2]/(te_req (trace_elem ctx pid req2 ret2));
      case: _ /.
  Qed.

  (* Lemma te_ret_eq pid req ret1 ret2 : *)
  (*     trace_elem ctx pid req ret1 = trace_elem ctx pid req ret2 -> *)
  (*     ret1 = ret2. *)
  (* Admitted. *)
End props.
