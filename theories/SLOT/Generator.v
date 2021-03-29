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

(** * Tactics for deconstructing trace ensembles one element at a time
 *)

From Coq Require Import
     List.

Import ListNotations.

From LibTx Require Import
     Hoare
     Ensemble.

Inductive Generator {TE} (Ensemble : @TraceEnsemble TE) (t : list TE) : Prop :=
  generated_by : Ensemble t -> Generator Ensemble t.

(** ** Contradiction *)

Ltac gen_eq_contradiction := discriminate.

(* Try to prove the goal by contradiction, based on a fact that one of
the generators is unable to generate the supplied trace: *)
Ltac gen_contradiction :=
  match goal with
    [H : Generator ?ens ?t |- _] =>
    destruct H as [H];
    now lazymatch ens with
        | (eq _) => gen_eq_contradiction
        | _ => fail 0 "I don't know how to solve contradiction in " ens
        end
  end.

Section tests.
  Context {A} (a b c d : A).

  Goal Generator (eq [a; b; c]) [] -> False.
    intros H.
    gen_contradiction.
  Qed.
End tests.

(** ** Consume *)

Ltac gen_consume_eq Ht te rest :=
  match type of Ht with
  | eq (?hd :: ?tl) ?t =>
    replace te with hd in * by congruence;
    replace rest with tl in * by congruence;
    clear Ht;
    assert (Ht : Generator (eq tl) tl); [constructor; reflexivity|idtac..]
  end.

Ltac gen_consume t te rest :=
  lazymatch goal with
  | [Ht : Generator ?ens t |- _] =>
    destruct Ht as [Ht];
    lazymatch ens with
    | (eq _) => gen_consume_eq Ht te rest
    | _ => fail 1 "I don't know how to consume from " ens
    end
  end.

Section tests.
  Context {A} (a b c d : A).

  Goal forall P Q t te rest,
      Generator (eq [a; b; c]) t ->
      t = te :: rest ->
      P te ->
      Q rest ->
      False.
    intros * Ht Ht' Hte Hrest.
    gen_consume t te rest.
  Abort.
End tests.
