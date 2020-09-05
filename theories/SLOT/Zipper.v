From Coq Require Import
     List.

Import ListNotations.

Section defn.
  Context {V : Type}.

  Definition t: Type := list V * V * list V.

  Definition movl (z : t) : t :=
    match z with
    | ([], e, r) => ([], e, r)
    | (l :: rest, e, r) => (rest, l, e :: r)
    end.

  Definition movr (z : t) : t :=
    match z with
    | (l, e, []) => (l, e, [])
    | (l, e, r :: rest) => (l, r, rest)
    end.

  Definition get (z : t) : V :=
    match z with
    | (_, v, _) => v
    end.

  Inductive left_of : t -> t -> Prop :=
  | left_of0 : forall v v' l r,
      left_of (l, v', (v :: r)) ((v' :: l), v, r)
  | left_of1 : forall v v' l r z,
      left_of z (l, v', (v :: r)) ->
      left_of z ((v' :: l), v, r).

  Definition right_of (z1 z2 : t) : Prop :=
    left_of z2 z1.

  Definition Forall (P : V -> Prop) (z : t) : Prop :=
    match z with
    | (l, v, r) => P v /\ List.Forall P l /\ List.Forall P r
    end.
End defn.

Global Arguments t : clear implicits.

Section tests.
  Let foo := ([2; 1], 3, [4]).

  Goal left_of ([], 1, [2; 3; 4]) foo.
    repeat constructor.
  Qed.

  Goal left_of ([1], 2, [3; 4]) foo.
    repeat constructor.
  Qed.

  Goal not(left_of ([3; 2; 1], 4, []) foo).
    intros H. subst foo.
    inversion H; subst. inversion H2; subst. inversion H3.
  Qed.

  Goal right_of foo ([], 1, [2; 3; 4]).
    repeat constructor.
  Qed.

  Goal right_of foo ([1], 2, [3; 4]).
    repeat constructor.
  Qed.
End tests.
