From Coq Require
     List
     Vector
     VectorSpec
     Logic.Decidable
     Relations.

Import Vector.VectorNotations List ListNotations Decidable.
Module Vec := Vector.

Ltac symm_not :=
  let H := fresh
  in unfold not;
     intros H;
     symmetry in H;
     generalize dependent H.

Open Scope list_scope.

Section vector.
  Lemma vec_replace_nth {A N} i a (vec : Vec.t A N) : (Vec.replace vec i a)[@i] = a.
  Admitted. (* TODO *)

  Lemma vec_replace_forall {A N} P i a (vec : @Vec.t A N) :
    Vec.Forall P (Vec.replace vec i a) ->
    P a.
  Admitted.

  Lemma vec_replace_forall_rev {A N} (P : A -> Prop) i a (vec : @Vec.t A N) :
    P a ->
    Vec.Forall P vec ->
    Vec.Forall P (Vec.replace vec i a).
  Admitted.

  Lemma vec_replace_nth_neq {A N} i j a b (vec : Vec.t A N) :
    j <> i ->
    vec[@i] = a ->
    (Vec.replace vec j b)[@i] = a.
  Admitted.

  Lemma vec_replace_nth_rewr {A N} i j b (vec : Vec.t A N) :
    j <> i ->
    (Vec.replace vec j b)[@i] = vec[@i].
  Admitted.

  Lemma vec_all_cons_false {A N} i hd tl (vec : @Vec.t (list A) N) :
    Vec.Forall (eq []) (Vec.replace vec i (hd :: tl)) -> False.
  Admitted.

  Lemma vec_forall_nth {N A} P i a (vec : Vec.t A N) :
    vec[@i] = a ->
    Vec.Forall P vec ->
    P a.
  Admitted.

  Lemma vec_forall_replace_nth {N A} P i j a (vec : Vec.t A N) :
    i <> j ->
    Vec.Forall P (Vec.replace vec j a) ->
    P vec[@i].
  Admitted.
End vector.

Ltac resolve_vec_eq_replace :=
  match goal with
  | [ Hij : ?j <> ?i, H : ?vec[@?i] = ?x  |- (Vec.replace ?vec ?j _)[@?i] = ?x ] =>
    apply vec_replace_nth_neq; assumption
  | [ Hij : ?i <> ?j, H : ?vec[@?i] = ?x  |- (Vec.replace ?vec ?j _)[@?i] = ?x ] =>
    apply vec_replace_nth_neq; try symm_not; assumption
  end.

Ltac transform_vec_replace_nth :=
  lazymatch goal with
    [Hij : ?i <> ?j |- (Vec.replace ?vec ?j _)[@?i] = ?x] =>
    apply vec_replace_nth_neq with (a := x);
    [now (apply Hij||symm_not)
    |idtac
    ]
  end; autorewrite with vector.

Ltac resolve_vec_forall_replace :=
  lazymatch goal with
  | [Hforall : Vec.Forall ?P (Vec.replace ?vec ?i ?elem) |- ?P ?elem] =>
    apply vec_forall_nth with (i0 := i) (a := elem) in Hforall;
    [assumption|now apply vec_replace_nth]
  (* | [Hforall : Vec.Forall ?P (Vec.replace ?vec ?i _) |- ?P (?vec[@?j])] => *)
  end.


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


Hint Extern 3 => resolve_vec_forall_replace : vector.
Hint Extern 3 => resolve_vec_eq_replace : vector.
Hint Extern 4 => transform_vec_replace_nth : vector.

Hint Rewrite @vec_replace_nth : vector.
Hint Rewrite Vec.replace_id : vector.
Hint Rewrite Vec.replace_replace_eq : vector.
Hint Resolve @vec_replace_nth_neq : vector.
(* Hint Rewrite @vec_replace_nth_rewr : vector. *)
