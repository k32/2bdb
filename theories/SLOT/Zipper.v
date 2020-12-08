From Coq Require Import
     List
     Program
     Decidable
     Classical_Prop.

Import ListNotations.

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
  | left_eq1 : forall l m e r z',
      left_eq (mov_r (l, m, e :: r)) z' ->
      left_eq (l, m, e :: r) z'.

  Definition left_of (a b : t) : Prop :=
    left_eq (mov_r a) b.

  Section tests.
    Goal forall l1 l2 m r, let z := ([l1; l2], Some m, r) in left_eq (mov_l (mov_l z)) z.
    Proof. intros. simpl. repeat constructor. Qed.

    Goal forall l1 l2 m r, let z := ([l1; l2], Some m, r) in left_of (mov_l z) z.
    Proof. intros. simpl. repeat constructor. Qed.
  End tests.

  Definition right_of (z1 z2 : t) : Prop :=
    left_of z2 z1.

  Definition right_eq (z1 z2 : t) : Prop :=
    left_eq z2 z1.

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

  Lemma left_of_to_list z1 z2 :
    left_eq z1 z2 ->
    to_list z1 = to_list z2.
  Proof with auto.
    intros H.
    induction H.
    - reflexivity.
    - now rewrite mov_r_to_list in IHleft_eq.
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

Global Arguments t : clear implicits.
Hint Constructors left_eq : slot.

Section tests.
  Open Scope zipper_scope.

  Let foo := ([2; 1], Some 3, [4]).

  Goal ([], Some 1, [2; 3; 4]) <z foo.
    repeat constructor.
  Qed.

  Goal ([1], Some 2, [3; 4]) <=z foo.
    right. repeat constructor.
  Qed.

  Goal forall z, z <=z foo -> exists v, get z = Some v /\ v < 4.
    intros z Hz.
    subst foo.
    inversion Hz; subst; cbn in *.
    - exists 3. auto.
    - destruct m.
      + inversion H; subst.
        * exists 2. auto.
        * simpl in *. give_up.
      +
      inversion H; subst; cbn in *.
      +


  Goal not(([3; 2; 1], Some 4, []) <z foo).
    intros H. subst foo.
    cbv in H.
    inversion H; subst; cbv in *. inversion H0; subst. simpl
    inversion H; subst. inversion H0; subst. inversion H1.
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
