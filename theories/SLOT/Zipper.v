From Coq Require Import
     List
     Program.

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
    | (l, e, r :: rest) => (e :: l, r, rest)
    end.

  Definition get (z : t) : V :=
    match z with
    | (_, v, _) => v
    end.

  Definition get_l (z : t) : list V :=
    match z with
    | (l, _, _) => l
    end.

  Definition get_r (z : t) : list V :=
    match z with
    | (_, _, r) => r
    end.

  Inductive left_of : t -> t -> Prop :=
  | left_of0 : forall v v' l r,
      left_of (l, v', (v :: r)) ((v' :: l), v, r)
  | left_of1 : forall v v' l r z,
      left_of z (l, v', (v :: r)) ->
      left_of z ((v' :: l), v, r).

  Section tests.
    Goal forall l1 l2 m r, let z := ([l1; l2], m, r) in left_of (movl z) z.
    Proof. intros. simpl. repeat constructor. Qed.

    Goal forall l1 l2 m r, let z := ([l1; l2], m, r) in left_of (movl (movl z)) z.
    Proof. intros. simpl. repeat constructor. Qed.

    Goal forall l1 m r, let z := ([l1], m, r) in ~left_of z z.
    Proof.
      intros. intros H. subst z. inversion H. subst. inversion H2.
    Qed.

    Goal forall a b c z, left_of z ([a; b], c, []) -> get z = a \/ get z = b.
    Proof.
      intros. inversion H; subst.
      - simpl. now left.
      - inversion H2; subst; simpl.
        + now right.
        + inversion H3.
    Qed.
  End tests.

  Lemma left_of_length z z' :
    left_of z z' ->
    length (get_l z) < length (get_l z').
  Proof.
    intros H.
    induction H; simpl.
    - constructor.
    - eapply PeanoNat.Nat.lt_trans; eauto.
  Qed.

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

  Lemma left_of_to_list z1 z2 :
    left_of z1 z2 ->
    to_list z1 = to_list z2.
  Proof with auto.
    intros H.
    induction H.
    - cbn. induction (rev l)...
      cbn in *. rewrite IHl0...
    - rewrite IHleft_of. cbn. rewrite <-app_assoc...
  Qed.

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

Module OfLists.
  (** * Zipper of nonempty lists *)
  Section defns.
    Context {V : Type}.

    Definition t := t (list V).

    Definition movl (z : t) : t :=
      match z with
      | ([], e, r) => ([], e, r)
      | (l :: rest, [], r) => (rest, l, r)
      | (l :: rest, e, r) => (rest, l, e :: r)
      end.

    Definition movr (z : t) : t :=
      match z with
      | (l, e, []) => (l, e, [])
      | (l, [], r :: rest) => (l, r, rest)
      | (l, e, r :: rest) => (e :: l, r, rest)
      end.

    Definition get (z : t) : list V :=
      match z with
      | (_, v, _) => v
      end.

    Let rewind_ (z : t) : t :=
      (* equivalent to repeating movl many times: *)
      let fix go l m r :=
          match l, m with
          | [],     _  => ([], m, r)
          | e :: l', [] => go l' e r
          | e :: l', _  => go l' e (m :: r)
          end in
      match z with
      | (l, m, r) => go l m r
      end.

    Definition nonempty (l : list V) : bool :=
      match l with
      | [] => false
      | _ :: _ => true
      end.

    Definition of_list (l : list (list V)) : t :=
      match l with
      | [] => ([], [], [])
      | e :: rest => ([], e, List.filter nonempty rest)
      end.

    Definition rewind (z : t) : t :=
      of_list (to_list z).

    Goal forall a b l r, rewind ([a :: l], [], [b :: r]) = ([], a :: l, [b :: r]).
      intros. reflexivity.
    Qed.

    Goal forall a b c l m r, rewind ([a :: l], c :: m, [b :: r]) = ([], a :: l, [c :: m; b :: r]).
      intros. reflexivity.
    Qed.
  End defns.
End OfLists.
