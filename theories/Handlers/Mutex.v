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

  Variable PID : Type.

  Definition state_t := option PID.

  Let TE := @TraceElem PID req_t ret_t.

  Inductive mutex_state_transition : state_t -> state_t -> TE -> Prop :=
  | mutex_grab : forall pid,
      mutex_state_transition None (Some pid) (trace_elem pid grab I)
  | mutex_release_ok : forall pid,
      mutex_state_transition (Some pid) None (trace_elem pid release true)
  | mutex_release_fail : forall pid,
      mutex_state_transition None None (trace_elem pid release false).

  Global Instance mutexHandler : @Handler PID req_t ret_t :=
    { h_state := state_t;
      h_state_transition := mutex_state_transition;
    }.

  Theorem no_double_grab_0 : forall (a1 a2 : PID),
      ~(PossibleTrace [a1 @ I <~ grab;
                       a2 @ I <~ grab]).
  Proof.
    intros a1 a2 H.
    destruct H as [s [s' H]].
    unfold_trace_deep H.
    discriminate.
  Qed.

  Theorem no_double_grab : forall (a1 a2 : PID),
      {{ fun _  => True }}
        [a1 @ I <~ grab;
         a2 @ I <~ grab]
      {{ fun _ => False}}.
  Proof.
    intros a1 a2 s s' Hss' Hpre.
    unfold_trace_deep Hss'.
    discriminate.
  Qed.
End defs.

Ltac mutex_contradiction :=
  match goal with
    [H1 : mutex_state_transition _ ?s1 ?s2 _, H2 : mutex_state_transition _ ?s2 ?s3 _ |- _] =>
      inversion H1; inversion H2; subst; discriminate
  end.

Hint Extern 4 => mutex_contradiction : handlers.

Ltac clear_mutex :=
  repeat match goal with
           [H: mutex_state_transition _ _ _ _ |- _] => clear H
         end.
