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

  Definition filter (P : V -> bool) (z : t) : t :=
    match z with
    | (l, v, r) => (List.filter P l, v, List.filter P r)
    end.

  Definition zipper_of (z : t) (l : list V) : Prop :=
    match l with
    | a :: t =>
      let z0 := ([], a, t) in
      z = z0 \/ left_of z0 z
    | [] => False
    end.
End defn.

Infix "<-" := (left_of)(at level 30).

Global Arguments t : clear implicits.
Hint Constructors left_of : slot.

Section tests.
  Let foo := ([2; 1], 3, [4]).

  Goal ([], 1, [2; 3; 4]) <- foo.
    repeat constructor.
  Qed.

  Goal ([1], 2, [3; 4]) <- foo.
    repeat constructor.
  Qed.

  Goal not(([3; 2; 1], 4, []) <- foo).
    intros H. subst foo.
    inversion H; subst. inversion H2; subst. inversion H3.
  Qed.

  Goal zipper_of ([], 1, [2; 3]) [1; 2; 3].
    firstorder.
  Qed.

  Goal zipper_of ([1], 2, [3]) [1; 2; 3].
    right. constructor.
  Qed.

  Goal zipper_of ([2; 1], 3, []) [1; 2; 3].
    right. repeat constructor.
  Qed.
End tests.
