From Coq Require Import
     List
     Logic.EqdepFacts.

From Equations Require Import
     Equations.

Let transp {A} {B : A -> Type} {x y : A} (e : x = y) : B x -> B y :=
  fun bx => eq_rect x B bx y e.

Let ap {A B} (f : A -> B) {x y : A} : x = y -> f x = f y.
Proof. now intros ->. Defined.

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
Derive NoConfusionHom for TraceElem.

Definition Trace {ctx : Ctx} := list (@TraceElem ctx).

Notation "pid '@' req '<~' ret" := (trace_elem _ pid req ret).

Lemma te_ret_eq : forall ctx pid req ret1 ret2,
    trace_elem ctx pid req ret1 = trace_elem ctx pid req ret2 ->
    ret1 = ret2.
Admitted. (* TODO *)
