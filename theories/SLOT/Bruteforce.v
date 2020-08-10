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

Section multi_interleaving.
  Section defn.
    Context `{Hssp : StateSpace} (can_switch : TE -> TE -> Prop) {N : nat}.

    Definition Traces := Vec.t (list TE) N.
    Let Idx := Fin.t N.

    Program Definition fin2_zero : Fin.t 2 :=
      let H : 0 < 2 := _ in
      Fin.of_nat_lt H.

    Program Definition fin2_one : Fin.t 2 :=
      let H : 1 < 2 := _ in
      Fin.of_nat_lt H.

    Inductive MInt_ (i : Idx) : Traces -> @TraceEnsemble TE :=
    | mint_nil : forall traces,
        Vec.Forall (eq []) traces ->
        MInt_ i traces []
    | mint_keep : forall te rest traces t,
        Vec.nth traces i = (te :: rest) ->
        MInt_ i (Vec.replace traces i rest) t ->
        MInt_ i traces (te :: t)
    | mint_switch : forall j te1 te2 rest traces t,
        i <> j -> can_switch te1 te2 ->
        Vec.nth traces i = (te2 :: rest) ->
        MInt_ j (Vec.replace traces i rest) (te1 :: t) ->
        MInt_ i traces (te2 :: te1 :: t).
  End defn.

  Global Arguments Traces {_}.

  Definition always_can_switch {A} (_ _ : A) := True.

  Definition MultiEns `{StateSpace} {N} (tt : Traces N) (t : list TE) :=
    exists i, MInt_ always_can_switch i tt t.
Section multi_interleaving.

Ltac resolve_fin_neq :=
  match goal with
    |- ?a <> ?b => now destruct (Fin.eq_dec a b)
  end.

Ltac resolve_vec_all_nil :=
  match goal with
  | |- Vec.Forall (eq []) ?vec => now repeat constructor
  | [H: Vec.Forall (eq []) ?vec |- _] =>
    repeat (inversion H; clear H; subst); discriminate
  end.

Hint Extern 3 (_ <> _) => resolve_fin_neq : slot_gen.
Hint Extern 3 (Vec.Forall _ _) => resolve_vec_all_nil : slot_gen.

Ltac destruct_mint H :=
  match type of H with
    MInt_ _ ?i ?vec0 ?t =>
    let traces := fresh "traces" in
    let Htraces := fresh "Htraces" in
    let te := fresh "te" in
    let t' := fresh "t'" in
    let rest := fresh "rest" in
    let Hte := fresh "Hte" in
    let te_pred := fresh "te_pred" in
    let Hij := fresh "Hij" in
    let Hswitch := fresh "Hswitch" in
    inversion H as [traces Htraces
                   |te rest traces t' Hte Htraces
                   |j te te_pred rest traces t' Hij Hswitch Hte Htraces];
    [resolve_vec_all_nil
    |repeat dependent destruction i;
     simpl in Hte;
     inversion Hte;
     subst;
     simpl in Htraces..
    ]
  end.


Section tests.
  Context `{Hssp : StateSpace} (a b c d e f : TE).

  Eval cbv in Vec.nth [a;b]%vector (fin2_zero).

  Let fin1_zero : Fin.t 1 := Fin.F1.

  Ltac mint2_helper :=
     simpl; unfold always_can_switch; auto with slot_gen.

  Ltac mint2_keep :=
    lazymatch goal with
    | |- MInt_ _ fin2_zero [(?a :: ?tail)%list; _]%vector (?a :: _) =>
      apply mint_keep with (rest := tail)
    | |- MInt_ _ fin2_one [_; (?a :: ?tail)%list]%vector (?a :: _) =>
      apply mint_keep with (rest := tail)
    end; mint2_helper.

  Ltac mint2_switch :=
    lazymatch goal with
    | |- MInt_ _ fin2_zero [(?a :: ?tail)%list; _]%vector (?a :: _) =>
      apply mint_switch with (rest := tail) (j := fin2_one)
    | |- MInt_ _ fin2_one [_; (?a :: ?tail)%list]%vector (?a :: _) =>
      apply mint_switch with (rest := tail) (j := fin2_zero)
    end; mint2_helper.

  Ltac mint2 :=
      (apply mint_nil; now resolve_vec_all_nil)
    || (mint2_keep; mint2)
    || (mint2_switch; mint2).

  Goal MultiEns [[a;b]%list; [c;d]%list]%vector [a; b; c; d].
  Proof. exists fin2_zero. mint2. Qed.

  Goal MultiEns [[a;b]%list; [c;d]%list]%vector [a; c; b; d].
  Proof. exists fin2_zero. mint2. Qed.

  Goal MultiEns [[a;b]%list; [c;d]%list]%vector [a; c; d; b].
  Proof. exists fin2_zero. mint2. Qed.

  Goal MultiEns [[a;b]%list; [c;d]%list]%vector [c; a; b; d].
  Proof. exists fin2_one. mint2. Qed.

  Goal MultiEns [[a;b]%list; [c;d]%list]%vector [c; a; d; b].
  Proof. exists fin2_one. mint2. Qed.

  Goal MultiEns [[a;b]%list; [c;d]%list]%vector [c; d; a; b].
  Proof. exists fin2_one. mint2. Qed.

  Goal forall t,
      let t1 := [a; b] in
      let t2 := [c; d] in
      MultiEns [t1; t2]%vector t ->
      False.
  Proof.
    intros * H. subst t1; subst t2.
    destruct H as [i0 H].
    destruct_mint H.
    2:{

    destruct_mint
    inversion H as [traces Htraces
                   |te rest traces t' Hte Hcont
                   |j te1 te2 rewt traces t' Hij Hswitch Hte Hcont];
      [resolve_vec_all_nil|repeat dependent destruction i0..].
    - resolve_vec_all_nil.

  Goal forall t,
      let t1 := [a; b] in
      let t2 := [c; d] in
      let t3 := [e; f] in
      MultiEns [t1; t2; t3]%vector t ->
      False.
  Proof.
    intros * H. subst t1; subst t2; subst t3.
    destruct H as [i0 H].
    inversion H as [traces Htraces
                   |te rest traces t' Hte Hcont
                   |j te1 te2 rewt traces t' Hij Hswitch Hte Hcont].
    - resolve_vec_all_nil.
    - repeat dependent destruction i0;
        simpl in Hte; inversion Hte; subst; simpl in Hcont.
      give_up.
      give_up.
      give_up.
    - repeat dependent destruction i0;
        simpl in Hte; inversion Hte; subst; simpl in Hcont.
  Abort.
End tests.

  Section props.
    Context `{Hssp : StateSpace}.

    Definition MultiEnsOrig {N} := @MultiEns_ _ always_can_switch N.

    Section boring_lemmas.
      Program Definition maxout N :=
        let H : N < S N := _ in
        Fin.of_nat_lt H.

      Lemma push_shiftin {N} t traces (te : TE) (i : Fin.t N) :
         (push (Vec.shiftin t traces)%vector te (Fin.FS i)) = Vec.shiftin t (push traces te i).
      Admitted.

      Lemma can_switch_shiftin {N} te t (prev_i : Fin.t N) prev_te traces :
        can_switch' always_can_switch prev_te te traces prev_i ->
        can_switch' always_can_switch prev_te te (Vec.shiftin t traces) (Fin.FS prev_i).
      Admitted.

      Lemma push_at_maxout N t (traces : Traces N) (te : TE) :
        push (Vec.shiftin t traces) te (maxout N) = Vec.shiftin (te :: t) traces.
      Admitted.

      Lemma mens_add_nil : forall {N} traces t,
          @MultiEnsOrig (S N) ([]%list :: traces)%vector t ->
          @MultiEnsOrig N traces t.
      Admitted.

      Lemma vec_forall_shiftin {N} P (t : list TE) (traces : Traces N) :
        Vec.Forall P (Vec.shiftin t traces) ->
        Vec.Forall P traces /\ P t.
      Admitted.

      Lemma vec_shiftin_same : forall {A N} (a : A),
          vec_same (S N) a = Vec.shiftin a (vec_same N a).
      Admitted.

      Lemma fin_eq_fs {N} (a b : Fin.t N) : a <> b -> Fin.FS a <> Fin.FS b.
      Admitted.
    End boring_lemmas.

    Let zero_two := fin2_zero.

    Hint Resolve can_switch_shiftin : slot_gen.
    Hint Constructors MultiEns_ : slot_gen.
    Hint Resolve fin_eq_fs : slot_gen.

    Open Scope list_scope.
    Fixpoint interleaving_to_mult0_fix (t1 t2 t : list TE)
             (H : Interleaving t1 t2 t) :
      MultiEnsOrig [t1; t2]%vector t.
    Proof with subst; unfold MultiEnsOrig; auto with slot_gen.
      destruct H as [te2 t1' t2' t' Ht'|te2 t1' t2' t' Ht'|]...
      3:{ constructor. }
      { eapply interleaving_to_mult0_fix in Ht'.
        inversion Ht' as [|te1 t1'' t2'' Ht''| ]...
        - replace ([[te2]; []]%vector) with ([cons te2 !! zero_two] [[]; []]%vector).

      - exists fin2_zero.
        eapply interleaving_to_mult0_fix in Ht'.
        destruct Ht' as [i Ht'].
        remember Ht' as Ht'0.
        destruct (Fin.eq_dec fin2_zero i) as [Heq|Hneq];
          destruct Ht' as [|te1 t1'' t2'' Ht''| ]...
        3:{
        .
        + subst.


        replace [(te :: t1)%list; t2]%vector with (push [t1; t2]%vector te fin2_zero) by reflexivity.
        destruct (Fin.eq_dec prev_i fin2_zero); subst; constructor; eauto.
        unfold can_switch', always_can_switch.
        now destruct ([t1; t2]%vector)[@prev_i].
      - replace [t1; (te :: t2)%list]%vector with (push [t1; t2]%vector te fin2_one) by reflexivity.
        destruct (Fin.eq_dec prev_i fin2_one); subst; constructor; eauto.
        unfold can_switch', always_can_switch.
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
             (Ht1 : MultiEns_ always_can_switch prev_te prev_i traces t1)
             (H : Interleaving t1 t2 t) :
      MultiEns_ always_can_switch prev_te (Fin.FS prev_i) (Vec.shiftin t2 traces) t.
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
        rewrite <-Htraces in Ht1.
        now subst.
      }
    Qed.
  End props.

  Section uniq_props.
    Context `{Hssp : StateSpace}
            (Hcomm_dec : forall a b, trace_elems_commute a b \/ not (trace_elems_commute a b)).

    Lemma te_comm_dec : forall `{StateSpace} a b, trace_elems_commute a b \/ not (trace_elems_commute a b).
    Proof.
      intros. apply classic.
    Qed.

    Definition can_switch_comm a b := not (trace_elems_commute a b).

    Definition MultiEnsUniq {N} := @MultiEns _ _ Hssp can_switch_comm N.

    Fixpoint canonicalize_mens_ {N} (t : list TE) (traces : Traces N)
             s s' pe pi
             (Ht : MultiEns_ always_can_switch pe pi traces t)
             (Hls : LongStep s t s') :
      exists t', MultiEns_ can_switch_comm pe pi traces t' /\ LongStep s t' s'.
    Proof with eauto.
      destruct Ht.
      { exists [].
        split; auto.
        constructor.
      }
      { long_step Hls.
        eapply canonicalize_mens_ in Hls...
        destruct Hls as [t' [Huniq Ht']].
        exists (te :: t').
        split.
        - constructor...
        - forward s0...
      }
      { long_step Hls.
        destruct (Hcomm_dec pe te) as [Hcomm|Hcomm].
        2:{ (* Solve case when trace elems don't commute, we can do it
        simply by definition: *)
          eapply canonicalize_mens_ in Hls...
            destruct Hls as [t' [Huniq Ht']].
            exists (te :: t').
            split.
            - constructor...
              unfold can_switch', can_switch_comm.
              destruct (traces[@pi]); auto.
            - forward s0...
        }
        {
          eapply Hcomm in Hls0.
          long_step Hls0. long_step Hls0. inversion_ Hls0.
          eapply canonicalize_mens_ in Hls; eauto.

          give_up.
    Admitted.

    Lemma canonicalize_mens {N} (t : list TE) (traces : Traces N)
          (Ht : MultiEnsOrig traces t)
          s s' (Hls : LongStep s t s') :
      exists t', MultiEnsUniq traces t' /\ LongStep s t' s'.
    Proof.
      unfold MultiEnsOrig,MultiEns in *.
      remember (find_nonempty traces) as Ne.
      destruct Ne as [[pi pe]|];
        unfold MultiEnsUniq,MultiEns;
        rewrite <- HeqNe.
      2:{ exists []. now subst. }
      eapply canonicalize_mens_ in Hls; eauto.

    Qed.

    Lemma uniq_ilv_correct {N} P Q (traces : Vec.t (list TE) N) :
      -{{P}} MultiEnsUniq traces {{Q}} ->
      -{{P}} MultiEnsOrig traces {{Q}}.
    Proof.
      intros * Horig t Ht. unfold_ht.
      eapply canonicalize_mens in Ht; eauto.
      destruct Ht as [t' [Huniq Ht']].
      eapply Horig; eauto.
    Qed.
  End uniq_props.
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
