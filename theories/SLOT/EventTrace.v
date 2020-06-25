From Coq Require Import
     List.

Section defs.
  Context {PID Req : Type} {Ret : Req -> Type}.

  Record TraceElem :=
    trace_elem { te_pid : PID;
                 te_req : Req;
                 te_ret : Ret te_req;
               }.

  Definition Trace := list TraceElem.
End defs.

Global Notation "pid '@' ret '<~' req" := (trace_elem pid req ret)(at level 30).

(* Require Import ssreflect ssrfun. *)

(* Section props. *)
(*   Context {ctx : Ctx}. *)
(*   Let ret_t := ctx_ret_t ctx. *)

  (* Lemma te_ret_dual_elim pid (P : forall req, ret_t req -> Prop) req1 (ret1 : ret_t req1) req2 (ret2 : ret_t req2) : *)
  (*     trace_elem ctx pid req1 ret1 = trace_elem ctx pid req2 ret2 -> *)
  (*     P req1 ret1 -> *)
  (*     P req2 ret2. *)
  (* Proof. *)
  (*   by rewrite -[ret2]/(te_ret (trace_elem ctx pid req2 ret2)) *)
  (*              -[req2]/(te_req (trace_elem ctx pid req2 ret2)); *)
  (*     case: _ /. *)
  (* Qed. *)

  (* Lemma te_ret_eq pid req ret1 ret2 : *)
  (*     trace_elem ctx pid req ret1 = trace_elem ctx pid req ret2 -> *)
  (*     ret1 = ret2. *)
  (* Admitted. *)
(* End props. *)
