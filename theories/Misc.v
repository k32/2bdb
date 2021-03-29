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
     List
     Logic.Decidable
     Relations.

Ltac symm_not :=
  let H := fresh
  in unfold not;
     intros H;
     symmetry in H;
     generalize dependent H.

Open Scope list_scope.

Section forall_dec.
  Context {A} (P : A -> Prop).

  Definition Forall_dec l :
    (forall a, decidable (P a)) ->
    decidable (Forall P l).
  Proof.
    intros Hdec.
    induction l.
    { left. constructor. }
    { destruct IHl as [Hl|Hl].
      - destruct (Hdec a).
        + left. constructor; auto.
        + right. intros H'.
          inversion H'. auto.
      - right. intros H.
        inversion H. auto.
    }
  Defined.
End forall_dec.
