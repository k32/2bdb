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

Notation "pid '@' ret '<~' req" := (trace_elem pid req ret)(at level 30) : hoare_scope.

Hint Constructors TraceElem : slot.
