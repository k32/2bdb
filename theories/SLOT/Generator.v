(** * More efficient definition of parallel ensemble
 *)

From Coq Require Import
     List
     Program
     Logic.Decidable.

From Coq Require
     Vector.

Import ListNotations Vector.VectorNotations.
Module Vec := Vector.

Open Scope list_scope.

From LibTx Require Import
     FoldIn
     Misc
     EventTrace
     Permutation
     SLOT.Hoare
     SLOT.Ensemble.

Section defn.
  Context `{Hssp : StateSpace} (can_switch : TE -> TE -> Prop) {N : nat}.

  Definition Traces := Vec.t (list TE) N.
  Let Idx := Fin.t N.

  Definition push {A N} (vec : Vector.t (list A) N) (a : A) (i : Fin.t N) :=
    let t := Vec.nth vec i in
    Vec.replace vec i (a :: t).

  Program Definition fin2_zero : Fin.t 2 :=
    let H : 0 < 2 := _ in
    Fin.of_nat_lt H.

  Program Definition fin2_one : Fin.t 2 :=
    let H : 1 < 2 := _ in
    Fin.of_nat_lt H.

  Goal forall (a : nat) b, [[a]%list; b]%vector = push [nil; b]%vector a fin2_zero : Set.
  Proof.
    intros.
    cbv.
    reflexivity.
  Qed.

  Definition can_switch' (te1 te2 : TE) (traces : Traces) (pred_n : Idx) : Prop :=
    match Vec.nth traces pred_n with
    | [] => True
    | _ => can_switch te1 te2
    end.

  Inductive MultiEns_ (prev_te : TE) (prev_i : Idx) : Traces -> @TraceEnsemble TE :=
  | mens_nil :
      MultiEns_ prev_te prev_i (vec_same N []) []
  | mens_keep : forall traces te t,
      MultiEns_ te prev_i traces t ->
      let traces' := push traces te prev_i in
      MultiEns_ prev_te prev_i traces' (te :: t)
  | mens_switch : forall traces te t i,
      i <> prev_i ->
      can_switch' prev_te te traces prev_i ->
      MultiEns_ te i traces t ->
      let traces' := push traces te i in
      MultiEns_ prev_te prev_i traces' (te :: t).

  Program Fixpoint find_nonempty_ {M} (traces : Vec.t (list TE) M) (H : M <= N) : option (Idx * TE) :=
    match traces with
    | Vec.nil => None
    | Vec.cons trace M' rest =>
      match trace with
      | te :: _ =>
        let idx : (M' < N) := _ in
        Some (Fin.of_nat_lt idx, te)
      | [] => find_nonempty_ rest _
      end
    end.
  Obligation 2.
    firstorder.
  Defined.

  Definition find_nonempty (traces : Traces) : option (Idx * TE).
    eapply (find_nonempty_ traces). auto.
  Defined.

  Definition MultiEns (traces : Traces) : @TraceEnsemble TE :=
    match find_nonempty traces with
    | Some (i, te) => MultiEns_ te i traces
    | None => eq []
    end.
End defn.

Section props.
  Context `{Hssp : StateSpace}.

  Let can_switch (_ _ : TE) := True.

  Definition MultiEnsOrig {N} := @MultiEns _ _ Hssp can_switch N.

  Lemma push_shiftin {N} t0 traces (te : TE) (i : Fin.t N) :
     (push (Vec.shiftin t0 traces)%vector te (Fin.FS i)) = Vec.shiftin t0 (push traces te i).
  Admitted.

  Lemma can_switch_shiftin {N} te t2 (prev_i : Fin.t N) prev_te traces :
    can_switch' can_switch prev_te te traces prev_i ->
    can_switch' can_switch prev_te te (Vec.shiftin t2 traces) (Fin.FS prev_i).
  Admitted.

  Hint Resolve can_switch_shiftin : slot_gen.

  Lemma fin_eq_fs {N} (a b : Fin.t N) : a <> b -> Fin.FS a <> Fin.FS b.
  Admitted.

  Hint Resolve fin_eq_fs : slot_gen.

  Fixpoint interleaving_to_mult0_fix (t1 t2 t : list TE)
      (H : Interleaving t1 t2 t) prev_te prev_i :
      MultiEns_ can_switch prev_te prev_i [t1; t2]%vector t.
  Proof.
    destruct H.
    - replace [(te :: t1)%list; t2]%vector with (push [t1; t2]%vector te fin2_zero) by reflexivity.
      destruct (Fin.eq_dec prev_i fin2_zero); subst; constructor; eauto.
      unfold can_switch', can_switch.
      now destruct ([t1; t2]%vector)[@prev_i].
    - replace [t1; (te :: t2)%list]%vector with (push [t1; t2]%vector te fin2_one) by reflexivity.
      destruct (Fin.eq_dec prev_i fin2_one); subst; constructor; eauto.
      unfold can_switch', can_switch.
      now destruct ([t1; t2]%vector)[@prev_i].
    - constructor.
  Qed.

  Lemma interleaving_to_mult0 : forall t1 t2 t,
      Interleaving t1 t2 t ->
      MultiEnsOrig [t1; t2]%vector t.
  Proof.
    intros.
    unfold MultiEnsOrig, MultiEns.
    remember (find_nonempty [t1; t2]%vector) as Ne.
    destruct Ne as [[i elem]|].
    - now eapply interleaving_to_mult0_fix.
    - destruct t1; destruct t2; cbv in HeqNe; try discriminate.
      inversion_ H.
  Qed.

  Fixpoint interleaving_to_mult_fix N (traces : Vec.t (list TE) N) (t1 t2 t : list TE)
           prev_te prev_i :
      MultiEnsOrig traces t1 ->
      Interleaving t1 t2 t ->
      MultiEns_ can_switch prev_te prev_i (Vec.shiftin t2 traces) t.
  (*Proof.
    intros Ht1 H.
    destruct H.
    - specialize (Ht1 prev_te prev_i).
      inversion_ Ht1; subst traces'0.
      + replace (Vec.shiftin t2 (push traces0 te prev_i))
          with (push (Vec.shiftin t2 traces0) te (Fin.FS prev_i))
          by apply push_shiftin.
        constructor; eauto with slot_gen.
      + replace (Vec.shiftin t2 (push traces0 te i))
          with (push (Vec.shiftin t2 traces0) te (Fin.FS i))
          by apply push_shiftin.
          constructor; eauto with slot_gen.
    - assert (i : N < S N) by auto.
      apply Fin.of_nat_lt in i.
      replace (Vec.shiftin (te :: t2) traces) with
          (push (Vec.shiftin t2 traces) te i).
      inversion
      { constructor.
        3:{ specialize (interleaving_to_mult N traces t1 t2 t te prev_i Ht1 H). *)
  Admitted.

  Lemma mens_add_nil : forall {N} traces t,
      @MultiEnsOrig (S N) ([]%list :: traces)%vector t ->
      @MultiEnsOrig N traces t.
  Admitted.

  Lemma nonempty_add_nil : forall {N} (traces : Vec.t (list TE) (S N)),
      None = find_nonempty ([]%list :: traces)%vector ->
      None = find_nonempty traces.
  Admitted.

  Lemma interleaving_to_mult N (traces : Vec.t (list TE) N) (t1 t2 t : list TE) :
      MultiEnsOrig traces t1 ->
      Interleaving t1 t2 t ->
      MultiEnsOrig (Vec.shiftin t2 traces) t.
  Proof.
    intros * Ht1 Ht.
    unfold MultiEnsOrig, MultiEns.
    remember (find_nonempty (Vec.shiftin t2 traces)) as Ne.
    destruct Ne as [[i elem]|].
    - eapply interleaving_to_mult_fix.
      + apply Ht1.
      + assumption.
    - induction traces.
      + destruct t2; cbv in HeqNe; try discriminate.
        cbv in Ht1.
        apply interleaving_symm, interleaving_nil in Ht; subst.
        reflexivity.
      + destruct h; simpl in HeqNe; try discriminate.
        apply mens_add_nil in Ht1.
        apply nonempty_add_nil in HeqNe.
        eauto.
  Qed.
End props.

Section uniq_props.
  Context `{Hssp : StateSpace}
          (Hcomm_dec : forall a b, trace_elems_commute a b \/ not (trace_elems_commute a b)).

  Definition MultiEnsUniq {N} := @MultiEns _ _ Hssp trace_elems_commute N.

  Lemma uniq_ilv_correct {N} P Q (traces : Vec.t (list TE) N) :
    -{{P}} MultiEnsOrig traces {{Q}} ->
    -{{P}} MultiEnsUniq traces {{Q}}.
  Admitted.
End uniq_props.

(*Section defn.
  Context `{Hssp : StateSpace}.

  Class Generator (A : Type) :=
    { next : A -> option (TE * A) -> Prop
    }.

  Let some {A B} (a : A) (b : B) := Some (a, b).

  Section unfold.
    Context {G} `{Generator G}.

    Inductive UnfoldsTo (g : G) : list TE -> Prop :=
    | gen_unf_nil :
        (next g) None ->
        UnfoldsTo g []
    | gen_unf_cons : forall te g' l,
        (next g) (some te g') ->
        UnfoldsTo g' l ->
        UnfoldsTo g (te :: l).
  End unfold.

  Global Instance listGenerator : Generator (list TE) :=
    {| next l :=
         match l with
         | [] => eq None
         | a :: l => eq (some a l)
         end
    |}.

  Lemma unfold_list_generator : forall (l l' : list TE),
      UnfoldsTo l l' ->
      l' = l.
  Proof.
    induction l; intros.
    - inversion_ H.
      discriminate.
    - inversion_ H.
      + discriminate.
      + simpl in H0.
        inversion_ H0.
        specialize (IHl l0 H1). subst.
        reflexivity.
  Qed.

  Lemma list_generator_ensemble : forall (l : list TE) P Q,
      -{{P}} eq l {{Q}} ->
      -{{P}} UnfoldsTo l {{Q}}.
  Proof.
    intros. intros t Ht. unfold_ht.
    apply unfold_list_generator in Ht. subst.
    eapply (H l); eauto.
  Qed.

  Section parallel.
    Context {G1 G2} `{Generator G1} `{Generator G2} (can_switch : TE -> TE -> Prop).

    Inductive direction := _1 | _2.

    Inductive ParallelGen (prev_dir : direction) (prev_te : TE) (g1 : G1) (g2 : G2) : @TraceEnsemble TE :=
    | par_gen_nil :
        (next g1) None ->
        (next g2) None ->
        ParallelGen prev_dir prev_te g1 g2 []
    | par_gen_proceed1 : forall te trace g1',
        prev_dir = _1 ->
        (next g1) (some te g1') ->
        ParallelGen prev_dir te g1' g2 trace ->
        ParallelGen prev_dir prev_te g1 g2 (te :: trace)
    | par_gen_proceed2 : forall te trace g2',
        prev_dir = _2 ->
        (next g2) (some te g2') ->
        ParallelGen prev_dir te g1 g2' trace ->
        ParallelGen prev_dir prev_te g1 g2 (te :: trace)
    | par_gen_switch_to1 : forall te trace g1',
        prev_dir = _2 ->
        can_switch prev_te te \/ (next g2) None ->
        (next g1) (some te g1') ->
        ParallelGen _1 te g1' g2 trace ->
        ParallelGen prev_dir prev_te g1 g2 (te :: trace)
    | par_gen_switch_to2 : forall te trace g2',
        prev_dir = _1 ->
        can_switch prev_te te \/ (next g1) None ->
        (next g2) (some te g2') ->
        ParallelGen _2 te g1 g2' trace ->
        ParallelGen prev_dir prev_te g1 g2 (te :: trace).

    Inductive ParallelGenerator (g : ParallelGen) : Cont -> Prop :=
    | gen_l : forall te g1',
        can_proceed g te _1 ->
        (next (pg_g1 g)) (cont_cons te g1') ->
        let g' := mkParallelGen g1' (pg_g2 g) (Some _1) (Some te) in
        ParallelGenerator g (cont_cons te g')
     | gen_r : forall te g2',
        can_proceed g te _2 ->
        (next (pg_g2 g)) (cont_cons te g2') ->
        let g' := mkParallelGen (pg_g1 g) g2' (Some _2) (Some te) in
        ParallelGenerator g (cont_cons te g')
    | gen_par_nil :
        (next (pg_g1 g)) cont_nil ->
        (next (pg_g2 g)) cont_nil ->
        ParallelGenerator g cont_nil.

    Global Instance parallelGenerator : Generator ParallelGen :=
      {| next gen :=
           match gen with
           | gen_parallel g1 g2 => ParallelGenerator g1 g2
           end
      |}.
  End parallel.

  Lemma list_generators_to_inerleaving : forall t1 t2 t,
      UnfoldsTo (gen_parallel t1 t2) t <-> Interleaving t1 t2 t.
  Proof.
    split; generalize dependent t; generalize dependent t2.
    { induction t1; intros.
      2:{ inversion_ H; simpl in H0.
          - inversion_ H0.
            inversion_ H1.
          - inversion_ H0.
            +


    { remember (gen_parallel t1 t2) as g.
      induction H.
      - subst. cbv in H.
        inversion H.
        destruct t1; destruct t2; try discriminate.
        constructor.
      -


End defn.
*)
