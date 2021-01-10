From Coq Require Import
     List
     Program
     Decidable
     Classical_Prop.

Import ListNotations.

From Hammer Require Import
     Tactics.

Section defn.
  Context {V : Type}.

  Definition t: Type := list V * option V * list V.

  Definition to_list (z : t) : list V :=
    match z with
    | (l, None, r) => rev l ++ r
    | (l, Some e, r) => rev l ++ (e :: r)
    end.

  Definition mov_l (z : t) : t :=
    match z with
    | ([], Some e, r)       => ([], None, e :: r)
    | ([], None, r)         => ([], None, r)
    | (l :: rest, Some e, r) => (rest, Some l, e :: r)
    | (l :: rest, None, r)   => (rest, Some l, r)
    end.

  Definition mov_r (z : t) : t :=
    match z with
    | (l, Some e, [])       => (e :: l, None, [])
    | (l, None, [])         => (l, None, [])
    | (l, Some e, r :: rest) => (e :: l, Some r, rest)
    | (l, None, r :: rest)   => (l, Some r, rest)
    end.

  Lemma mov_l_r l m r :
    let z := (l, Some m, r) in
    mov_r (mov_l z) = z.
  Proof.
    intros z. subst z.
    now destruct l as [|e l].
  Qed.

  Lemma mov_r_l l m r :
    let z := (l, Some m, r) in
    mov_l (mov_r z) = z.
  Proof.
    intros z. subst z.
    now destruct r as [|e r].
  Qed.

  Lemma mov_l_to_list (z : t) : to_list (mov_l z) = to_list z.
  Proof.
    destruct z as [[[|e_l l] [e|]] [|e_r r]];
      simpl;
      try rewrite <- app_assoc;
      reflexivity.
  Qed.

  Lemma mov_r_to_list (z : t) : to_list (mov_r z) = to_list z.
  Proof.
    destruct z as [[[|e_l l] [e|]] [|e_r r]];
      simpl;
      try rewrite <- app_assoc;
      reflexivity.
  Qed.

  Definition get (z : t) : option V :=
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

  Definition del (z : t) : t :=
    match z with
    | (l, _, r) => (l, None, r)
    end.

  Inductive left_eq : t -> t -> Prop :=
  | left_eq0 : forall z,
      left_eq z z
  | left_eq1 : forall z e l' m' r',
      left_eq z (l', Some m', e :: r') ->
      left_eq z (m' :: l', Some e, r').

  Definition left_of (a b : t) : Prop :=
    left_eq a (mov_l b).

  Section tests.
    Goal forall l1 l2 m r, let z := ([l1; l2], Some m, r) in left_eq (mov_l (mov_l z)) z.
    Proof. intros. simpl. repeat constructor. Qed.

    Goal forall l1 l2 m r, let z := ([l1; l2], Some m, r) in left_of (mov_l z) z.
    Proof. intros. simpl. repeat constructor. Qed.
  End tests.

  Inductive right_eq : t -> t -> Prop :=
  | right_eq0 : forall z,
      right_eq z z
  | right_eq1 : forall z e l' m' r',
      right_eq z (e :: l', Some m', r') ->
      right_eq z (l', Some e, m' :: r').

  Lemma left_eq_mov_l e l m r l' m' r' :
    left_eq (e :: l, Some m, r) (l', Some m', r') ->
    left_eq (l, Some e, m :: r) (l', Some m', r').
  Proof.
    intros H.
    generalize dependent l.
    generalize dependent m.
    generalize dependent r.
    generalize dependent e.
    generalize dependent m'.
    generalize dependent r'.
    induction l'; intros; sauto.
  Qed.

  Lemma right_eq_mov_r e l m r l' m' r' :
    right_eq (l, Some m, e :: r) (l', Some m', r') ->
    right_eq (m :: l, Some e, r) (l', Some m', r').
  Proof.
    intros H.
    generalize dependent l.
    generalize dependent m.
    generalize dependent r.
    generalize dependent e.
    generalize dependent m'.
    generalize dependent l'.
    induction r'; intros; sauto.
  Qed.

  Lemma right_eq_left_eq_equiv z1 z2 :
    right_eq z1 z2 <-> left_eq z2 z1.
  Proof with subst; simpl in *.
    split; intros H.
    - induction H.
      + constructor.
      + inversion IHright_eq; subst.
        * constructor. constructor.
        * apply left_eq_mov_l. now constructor.
    - induction H.
      + constructor.
      + inversion IHleft_eq; subst.
        * constructor. constructor.
        * constructor. now apply right_eq_mov_r.
  Qed.

  Definition right_of (z1 z2 : t) : Prop :=
    right_eq z1 (mov_r z2).

  Definition Forall (P : V -> Prop) (z : t) : Prop :=
    match z with
    | (l, None, r) => List.Forall P l /\ List.Forall P r
    | (l, Some v, r) => P v /\ List.Forall P l /\ List.Forall P r
    end.

  Definition optional_filter (P : V -> bool) (v : option V) : option V :=
    match v with
    | Some v =>
      match P v with
      | true => Some v
      | false => None
      end
    | None => None
    end.

  Definition filter (P : V -> bool) (z : t) : t :=
    match z with
    | (l, v, r) => (List.filter P l, optional_filter P v, List.filter P r)
    end.

  Definition of_list (l : list V) : t :=
    match l with
    | [] => ([], None, [])
    | e :: rest => ([], Some e, rest)
    end.

  Definition zipper_of (z : t) (l : list V) : Prop :=
    left_eq (of_list l) z.

  Lemma left_eq_to_list z1 z2 :
    left_eq z1 z2 ->
    to_list z1 = to_list z2.
  Proof with auto.
    intros H.
    induction H.
    - reflexivity.
    - cbn in *. now rewrite <-app_assoc.
  Qed.

  Lemma left_of_dec z1 z2 :
    to_list z1 = to_list z2 ->
     z1 = z2 \/ left_of z1 z2 \/ left_of z2 z1.
  Proof.
    intros H. unfold to_list in H.
    destruct z1 as [[l1 m1] r1]. destruct z2 as [[l2 m2] r2].
  Admitted.
End defn.

Declare Scope zipper_scope.
Delimit Scope zipper_scope with zipper.
Infix "<z" := (left_of)(at level 90) : zipper_scope.
Infix "<=z" := (left_eq)(at level 90) : zipper_scope.
Infix ">z" := (right_of)(at level 90) : zipper_scope.
Infix ">=z" := (right_eq)(at level 90) : zipper_scope.

Global Arguments t : clear implicits.
Hint Constructors left_eq : slot.

Section tests.
  Open Scope zipper_scope.

  Let foo := ([2; 1], Some 3, [4]).

  Goal ([], Some 1, [2; 3; 4]) <z foo.
    repeat constructor.
  Qed.

  Goal ([1], Some 2, [3; 4]) <=z foo.
    repeat constructor.
  Qed.

  Goal forall z, z <=z foo ->
            get z = Some 3 \/
            get z = Some 2 \/
            get z = Some 1.
  Proof with subst; cbn in *.
    intros z Hz. subst foo.
    inversion Hz...
    - auto.
    - inversion H1...
      + auto.
      + inversion H2...
        auto.
  Qed.

  Goal forall z, z >z foo -> get z = Some 4.
  Proof with subst; cbn in *.
    intros z Hz. subst foo.
    inversion Hz...
    - reflexivity.
  Qed.

  Goal not(([3; 2; 1], Some 4, []) <z foo).
    intros H. subst foo.
    cbv in H.
    inversion H; subst; cbv in *.
    inversion H2.
  Qed.

  Goal zipper_of ([], Some 1, [2; 3]) [1; 2; 3].
    repeat constructor.
  Qed.

  Goal zipper_of ([1], Some 2, [3]) [1; 2; 3].
    repeat constructor.
  Qed.

  Goal zipper_of ([2; 1], Some 3, []) [1; 2; 3].
    repeat constructor.
  Qed.
End tests.
