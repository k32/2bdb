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

  Definition rewind (z : t) : t :=
    match z with
    | (l, e, r) =>
      match rev l with
      | [] => ([], e, r)
      | e' :: l' => ([], e', l' ++ e :: r)
      end
    end.

  Definition to_list (z : t) : list V :=
    match z with
    | (l, e, r) => rev l ++ (e :: r)
    end.

  Definition of_list (l : list V) (default : V) : t :=
    match l with
    | [] => ([], default, [])
    | e :: rest => ([], e, rest)
    end.
End defn.

Delimit Scope zipper_scope with zipper.
Infix "<-" := (left_of)(at level 30) : zipper_scope.

Global Arguments t : clear implicits.
Hint Constructors left_of : slot.

Section tests.
  Open Scope zipper_scope.

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

Section zipper_of_lists.
  Context {V : Type}.

  Let Z := t (list V).

  Definition is_nonempty (l : list V) :=
    match l with
    | [] => false
    | _ :: _ => true
    end.

  Definition nonempty (z : Z) := filter is_nonempty z.
End zipper_of_lists.
