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
