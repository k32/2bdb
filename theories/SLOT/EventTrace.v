(* LibTx, proofs about distributed systems design
   Copyright (C) 2019-2021  k32

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, version 3 of the License.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *)
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
