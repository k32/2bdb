(** * SLOT model checker *)
From LibTx Require Import
     FoldIn
     Misc
     EventTrace
     Permutation
     SLOT.Hoare
     SLOT.Ensemble.

From Coq Require Import
     List
     Program
     Logic.Classical_Prop.

From Coq Require
     Vector.

Import ListNotations Vector.VectorNotations Vectors.VectorSpec.
Module Vec := Vector.

Open Scope list_scope.
Open Scope hoare_scope.

Section supplementary_definitions.
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
      | Vec.nil _ => None
      | Vec.cons _ trace M' rest =>
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

  Global Arguments Traces {_}.

  Section props.
    Context `{Hssp : StateSpace}.

    Let can_switch (_ _ : TE) := True.

    Definition MultiEnsOrig {N} := @MultiEns _ _ Hssp can_switch N.

    Section boring_lemmas.
      Program Definition maxout N :=
        let H : N < S N := _ in
        Fin.of_nat_lt H.

      Lemma push_shiftin {N} t traces (te : TE) (i : Fin.t N) :
         (push (Vec.shiftin t traces)%vector te (Fin.FS i)) = Vec.shiftin t (push traces te i).
      Admitted.

      Lemma can_switch_shiftin {N} te t (prev_i : Fin.t N) prev_te traces :
        can_switch' can_switch prev_te te traces prev_i ->
        can_switch' can_switch prev_te te (Vec.shiftin t traces) (Fin.FS prev_i).
      Admitted.

      Lemma push_at_maxout N t (traces : Traces N) (te : TE) :
        push (Vec.shiftin t traces) te (maxout N) = Vec.shiftin (te :: t) traces.
      Admitted.

      Lemma mens_add_nil : forall {N} traces t,
          @MultiEnsOrig (S N) ([]%list :: traces)%vector t ->
          @MultiEnsOrig N traces t.
      Admitted.

      Lemma nonempty_add_nil : forall {N} (traces : Vec.t (list TE) (S N)),
          None = find_nonempty ([]%list :: traces)%vector ->
          None = find_nonempty traces.
      Admitted.

      Lemma empty_traces : forall {N} (traces : Traces N),
          None = find_nonempty traces <->
          Vec.Forall (eq []) traces.
      Admitted.

      Lemma vec_forall_shiftin {N} P (t : list TE) (traces : Traces N) :
        Vec.Forall P (Vec.shiftin t traces) ->
        Vec.Forall P traces /\ P t.
      Admitted.

      Lemma vec_shiftin_same : forall {A N} (a : A),
          vec_same (S N) a = Vec.shiftin a (vec_same N a).
      Admitted.

      Lemma shiftin_to_empty {N pe pi} (traces : Traces N) t :
        Vec.Forall (eq []) traces ->
        MultiEns_ can_switch pe pi (Vec.shiftin t traces) t.
      Admitted.

      Lemma fin_eq_fs {N} (a b : Fin.t N) : a <> b -> Fin.FS a <> Fin.FS b.
      Admitted.
    End boring_lemmas.

    Hint Resolve can_switch_shiftin : slot_gen.

    Hint Resolve fin_eq_fs : slot_gen.

    Lemma mens_orig_can_start_anywhere : forall {N} (traces : Traces N) t pte1 pi1 pte2 pi2,
        MultiEns_ can_switch pte1 pi1 traces t ->
        MultiEns_ can_switch pte2 pi2 traces t.
    Proof.
      intros.
      destruct (Fin.eq_dec pi1 pi2).
      - subst.
        inversion_ H; constructor; auto.
      - inversion_ H.
        + constructor.
        + constructor; auto.
          unfold can_switch', can_switch.
          now destruct traces0[@pi2].
        + destruct (Fin.eq_dec i pi2); subst;
          constructor; auto.
          unfold can_switch', can_switch.
          now destruct traces0[@pi2].
    Qed.

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

    Fixpoint interleaving_to_mult_fix N (traces : Traces N) (t1 t2 t : list TE)
             prev_te prev_i
             (Ht1 : MultiEns_ can_switch prev_te prev_i traces t1)
             (H : Interleaving t1 t2 t) :
      MultiEns_ can_switch prev_te (Fin.FS prev_i) (Vec.shiftin t2 traces) t.
    Proof.
      destruct H.
      { inversion_ Ht1; subst traces'0.
        + replace (Vec.shiftin t2 (push traces0 te prev_i))
            with (push (Vec.shiftin t2 traces0) te (Fin.FS prev_i))
            by apply push_shiftin.
          constructor; eauto with slot_gen.
        + replace (Vec.shiftin t2 (push traces0 te i))
            with (push (Vec.shiftin t2 traces0) te (Fin.FS i))
            by apply push_shiftin.
          constructor; eauto with slot_gen.
      }
      { set (i := maxout N).
        apply mens_orig_can_start_anywhere with (pte1 := te) (pi1 := i).
        replace (Vec.shiftin (te :: t2) traces) with (push (Vec.shiftin t2 traces) te i)
          by apply push_at_maxout.
        constructor.
        apply mens_orig_can_start_anywhere with (pte1 := prev_te) (pi1 := Fin.FS prev_i).
        eauto.
      }
      { inversion_ Ht1.
        replace (Vec.shiftin [] (vec_same N [])) with (@vec_same (list TE) (S N) [])
          by apply vec_shiftin_same.
        constructor.
      }
    Defined.

    Lemma interleaving_to_mult N (traces : Vec.t (list TE) N) (t1 t2 t : list TE) :
        MultiEnsOrig traces t1 ->
        Interleaving t1 t2 t ->
        MultiEnsOrig (Vec.shiftin t2 traces) t.
    Proof.
      intros * Ht1 Ht.
      unfold MultiEnsOrig, MultiEns in *.
      remember (find_nonempty (Vec.shiftin t2 traces)) as Ne.
      destruct Ne as [[i elem]|].
      { remember (find_nonempty traces) as Ne'.
        destruct Ne' as [[i' elem']|].
        - apply mens_orig_can_start_anywhere with (pte1 := elem') (pi1 := Fin.FS i').
          apply interleaving_to_mult_fix with (t1 := t1); auto.
        - subst. apply interleaving_nil in Ht. subst.
          apply empty_traces in HeqNe'.
          apply shiftin_to_empty; auto.
      }
      { apply empty_traces,vec_forall_shiftin in HeqNe.
        destruct HeqNe as [Htraces Ht2].
        subst. apply interleaving_symm,interleaving_nil in Ht.
        apply empty_traces in Htraces.
        destruct (find_nonempty traces); try discriminate.
        now subst.
      }
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

  Lemma te_comm_dec : forall `{StateSpace} a b, trace_elems_commute a b \/ not (trace_elems_commute a b).
  Proof.
    intros.
    apply classic.
  Qed.
End supplementary_definitions.

Ltac remove_commuting_interleavings :=
  lazymatch goal with
  | Ht : Interleaving ?t1 ?t2 ?t |- _ =>
    apply interleaving_to_mult0 in Ht
  end.

Ltac transform_ensemble e :=
  lazymatch type of e with
  | (?a = ?b) =>
    subst a || subst b
  | (Parallel ?e1 ?e2) ?t =>
    let t_l := fresh "t_l" in
    let Ht_l := fresh "Ht_l" in
    let t_r := fresh "t_r" in
    let Ht_r := fresh "Ht_r" in
    let t := fresh "t" in
    let Ht := fresh "Ht" in
    destruct e as [t_l t_r t Ht_l Ht_r Ht];
    (* repeat remove_commuting_interleavings; *)
    transform_ensemble Ht_l;
    transform_ensemble Ht_r
  | ?x =>
    fail 1 "I don't know how to deconstruct " x
  end.

Tactic Notation "transform_ensemble" ident(e) := transform_ensemble e.

Ltac bruteforce :=
  lazymatch goal with
    [ |- -{{?P}} ?e {{?Q}} ] =>
    (* Preparations: *)
    let t := fresh "t" in
    let Ht := fresh "Ht" in
    intros t Ht; unfold_ht;
    transform_ensemble Ht
  end.

Section tests.
  Context `{StateSpace}.

  Goal forall (a b c d e f : TE) Q,
      trace_elems_commute a c ->
      trace_elems_commute a d ->
      trace_elems_commute b c ->
      trace_elems_commute b d ->
      -{{const True}} eq [a; b] -|| (eq [c; d] -|| eq [e; f]) {{Q}}.
  Proof.
    intros.
    bruteforce.
    repeat remove_commuting_interleavings.
  Abort.
End tests.
