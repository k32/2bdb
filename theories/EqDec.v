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
Class EqDec T : Type :=
  { eq_dec : forall (a b : T), {a = b} + {a <> b};
  }.

Lemma eq_dec_same : forall A B `{EqDec A} (a : A) (b c : B),
    (if eq_dec a a then b else c) = b.
Proof with firstorder.
  intros. destruct (eq_dec a a)...
Qed.

Hint Rewrite eq_dec_same : eq_dec.
Hint Extern 3 ((if eq_dec ?X ?Y then _ else _) = _) => destruct (eq_dec ?X ?Y); subst; firstorder : eq_dec.
Hint Extern 3 (_ = (if eq_dec ?X ?Y then _ else _)) => destruct (eq_dec ?X ?Y); subst; firstorder : eq_dec.

(* Global Instance eqDecNat : EqDec nat := *)
(* Proof. *)

(*   decide equality. *)
(* Qed. *)

(* Global Instance eqDecBool : EqDec bool := {}. *)
(* Proof. *)
(*   decide equality. *)
(* Qed. *)
