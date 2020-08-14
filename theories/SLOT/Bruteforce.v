(** * SLOT model checker *)
From LibTx Require Import
     FoldIn
     Misc
     EventTrace
     Permutation
     SLOT.Hoare
     SLOT.Ensemble
     SLOT.Generator.

From Coq Require Import
     List
     Program
     Logic.Classical_Prop.

From Coq Require
     Vector.

Import ListNotations Vector.VectorNotations.

Module Vec := Vector.

Open Scope list_scope.
Open Scope hoare_scope.
Print Module Coq.Vectors.VectorSpec.
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
        i <> j ->
        can_switch te1 te2 ->
        Vec.nth traces i = (te2 :: rest) ->
        MInt_ j (Vec.replace traces i rest) (te1 :: t) ->
        MInt_ i traces (te2 :: te1 :: t).

    Lemma mint_empty_trace (traces : Traces) i t :
      Vec.Forall (eq []) traces ->
      MInt_ i traces t ->
      t = [].
    Proof.
      intros Hnil Ht.
      destruct Ht.
      - easy.
      - give_up.
    Admitted.
  End defn.

  Global Arguments Traces {_}.

  Definition always_can_switch {A} (_ _ : A) : Prop := True.

  Definition MultiIlv `{StateSpace} {N} (tt : Traces N) (t : list TE) :=
    exists i, MInt_ always_can_switch i tt t.
Section multi_interleaving.

Ltac resolve_fin_neq :=
  match goal with
    |- ?a <> ?b => now destruct (Fin.eq_dec a b)
  end.

Ltac vec_forall_contradiction H :=
  match type of H with
  | Vec.Forall ?P []%vector =>
    fail 0 "No contradiction found"
  | Vec.Forall ?P (?a :: ?rest)%vector =>
    let vec := fresh in
    remember (a :: rest)%vector as vec;
    destruct H; [discriminate|idtac]
  end.

Section tests.
  Context A (a b c : A).

  Goal Vec.Forall (eq []) [[]%list; [a]%list; [b]%list]%vector -> False.
  Proof.
    intros H.
    dependent destruction H.
    dependent destruction H0.
  Qed.
End tests.

Ltac vec_forall_nil :=
  repeat match goal with
           [H : Vec.Forall (eq []) ?vec |- _] =>
           dependent destruction H
         end.

Ltac resolve_vec_all_nil :=
  multimatch goal with
  | |- Vec.Forall (eq []) ?vec =>
    now repeat constructor
  | [H: Vec.Forall (eq []) ?vec |- _] =>
    vec_forall_nil; gen_contradiction
  | _ =>
    fail 0 "I can't solve this goal"
  end.

Hint Extern 3 (_ <> _) => resolve_fin_neq : slot_gen.
Hint Extern 3 (Vec.Forall _ _) => resolve_vec_all_nil : slot_gen.

Ltac mint_destruct H te rest Hte j :=
  match type of H with
  | MInt_ _ _ _ ?t =>
    apply mint_empty_trace in H;
    [idtac|resolve_vec_all_nil];
    subst t
  | MInt_ _ _ ?traces ?t =>
    let t' := fresh "t'" in
    let te_pred := fresh "te_pred" in
    let Hij := fresh "Hij" in
    let Hswitch := fresh "Hswitch" in
    let traces0 := fresh "traces0" in
    let Htraces := fresh "Htraces" in
    let traces' := fresh "traces" in
    remember traces as traces0;
    destruct H as [traces' Htraces
                  |te rest traces' t' Hte Htraces
                  |j te_pred te rest traces' t' Hij Hswitch Hte Htraces];
    subst traces';
    clear H; rename Htraces into H
  end.

Ltac mint_case_analysis i H te rest Hte :=
  repeat dependent destruction i;
  simpl in Hte;
  lazymatch type of Hte with
  | ?t_x = te :: rest =>
    gen_consume t_x te rest; simpl in H; clear Hte
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

  Goal MultiIlv [[a;b]%list; [c;d]%list]%vector [a; b; c; d].
  Proof. exists fin2_zero. mint2. Qed.

  Goal MultiIlv [[a;b]%list; [c;d]%list]%vector [a; c; b; d].
  Proof. exists fin2_zero. mint2. Qed.

  Goal MultiIlv [[a;b]%list; [c;d]%list]%vector [a; c; d; b].
  Proof. exists fin2_zero. mint2. Qed.

  Goal MultiIlv [[a;b]%list; [c;d]%list]%vector [c; a; b; d].
  Proof. exists fin2_one. mint2. Qed.

  Goal MultiIlv [[a;b]%list; [c;d]%list]%vector [c; a; d; b].
  Proof. exists fin2_one. mint2. Qed.

  Goal MultiIlv [[a;b]%list; [c;d]%list]%vector [c; d; a; b].
  Proof. exists fin2_one. mint2. Qed.

  Goal forall t1 t2 t3 t (P : list TE -> Prop),
      Generator (eq [a; b]) t1 ->
      Generator (eq [c; d]) t2 ->
      Generator (eq [e; f]) t3 ->
      MultiIlv [t1; t2; t3]%vector t ->
      P t.
  Proof.
    intros * Gt1 Gt2 Gt3 H.
    destruct H as [i H].
    mint_destruct H te rest Hte j.
    { resolve_vec_all_nil. }
    { mint_case_analysis i H te rest Hte.
      - mint_destruct H te2 rest2 Hte j2.
        + resolve_vec_all_nil.
        + mint_case_analysis i H te2 rest2 Hte.
          { mint_destruct H te3 rest3 Hte j3.
            - resolve_vec_all_nil.
            - simpl in Hte.
              discriminate.
            -
  Abort.

  Goal forall t,
      let t1 := [a; b] in
      let t2 := [c; d] in
      MultiIlv [t1; t2]%vector t ->
      t = [].
  Abort.
End tests.

Lemma te_comm_dec : forall `{StateSpace} a b, trace_elems_commute a b \/ not (trace_elems_commute a b).
Proof.
  intros. apply classic.
Qed.

Section uniq.
  Context `{Hssp : StateSpace}
          (Hcomm_dec : forall a b, trace_elems_commute a b \/ not (trace_elems_commute a b)).

  Fixpoint interleaving_to_mens_ t1 t2 t (H : Interleaving t1 t2 t) :
    MultiIlv [t1; t2]%vector t.
  Proof with simpl; eauto.
    destruct H;
      [pose (i0 := fin2_zero); pose (tx := t1)
      |pose (i0 := fin2_one); pose (tx := t2)
      |exists fin2_zero; eapply mint_nil; repeat constructor
      ];
      (* Resolve goals 1-2: *)
      exists i0;
      (* Obtain induction hypothesis: *)
      eapply interleaving_to_mens_ in H; destruct H as [i H];
      (* Check if we keep direction or switch it: *)
      (destruct (Fin.eq_dec i i0);
       [(* Keep direction, resolve by contructor: *)
         subst; apply mint_keep with (rest := tx); simpl; auto
       |(* Switch direction: *)
       remember [t1; t2]%vector as t_;
       destruct t; subst t_;
       [inversion H;
        vec_forall_nil;
        eapply mint_keep; simpl; eauto;
        eapply mint_nil; simpl;
        resolve_vec_all_nil
       |eapply mint_switch with (j := i); eauto; easy
       ]
      ]).
  Defined.

  Definition MIntUniq_ {N} (tt : Traces N) (t : list TE) :=
    exists i, MInt_ trace_elems_commute i tt t.

  Lemma vec_replace_nth {A N} i a vec : (@Vec.replace A N vec i a)[@i] = a.
  Admitted. (* TODO *)

  Lemma vec_replace_forall {A N} P i a (vec : @Vec.t A N) :
    Vec.Forall P (Vec.replace vec i a) ->
    P a.
  Admitted.

  Fixpoint umint_append {N} (i j : Fin.t N) te rest (traces : Traces N) (t : list TE)
           (Ht : MInt_ trace_elems_commute j (Vec.replace traces i rest) t)
           s s' s'' (Hls : LongStep s' t s'')
           (Hte : s ~[te]~> s')
           {struct Ht} :
    exists t', MInt_ trace_elems_commute i (Vec.replace traces i (te :: rest)) t' /\ LongStep s t' s''.
  Proof with eauto with slot; try apply vec_replace_nth.
    remember (Vec.replace traces i rest) as traces0.
    destruct Ht; subst traces0.
    { exists [te].
      long_step Hls. subst.
      replace rest with ([] : list TE) in *.
      - split...
        apply mint_keep with (rest0 := [])...
        rewrite Vec.replace_replace_eq.
        now apply mint_nil.
      - (* [] = rest *)
        now apply vec_replace_forall in H.
    }
    { long_step Hls.
      destruct (Fin.eq_dec i j).
      { subst.
        replace rest with (te0 :: rest0) in * by now rewrite vec_replace_nth in H.
        rewrite Vec.replace_replace_eq in Ht.
        eapply umint_append in Ht...
        destruct Ht as [t' [Hu Ht']].
        exists (te :: t').
        split...
        apply mint_keep with (rest1 := (te0 :: rest0))...
        rewrite Vec.replace_replace_eq.
        assumption.
      }
      { destruct (Hcomm_dec te te0).
  Admitted.


  (* Proof with repeat (try assumption ; constructor); eauto with hoare. *)
  (*   remember (Vec.replace traces i rest) as traces0. *)
  (*   destruct Ht. *)
  (*   - exists []. *)
  (*     subst. *)
  (*     split. *)
  (*     + constructor. *)

  Fixpoint canonicalize_mens_ {N} (t : list TE) (traces : Traces N)
             s s' i
             (Ht : MInt_ always_can_switch i traces t)
             (Hls : LongStep s t s') :
      exists t', MInt_ trace_elems_commute i traces t' /\ LongStep s t' s'.
    Proof with eauto with slot.
      destruct Ht.
      { exists [].
        split...
        constructor...
      }
      { long_step Hls.
        eapply canonicalize_mens_ in Hls...
        destruct Hls as [t' [Huniq Ht']].
        exists (te :: t').
        split...
        eapply mint_keep...
      }
      { long_step Hls.
        eapply canonicalize_mens_ in Hls...
        destruct Hls as [t' [Huniq Ht']].
        replace traces with (Vec.replace traces i (te2 :: rest)).
        - eapply umint_append...
        - rewrite <-H1, Vec.replace_id.
          reflexivity.
      }
    Defined.

  Lemma mint_uniq_correct_ : forall {N} P Q (traces : Traces N),
      -{{P}} MIntUniq_ traces {{Q}} ->
      -{{P}} MultiIlv traces {{Q}}.
  Proof.
    intros * H t Ht. unfold_ht.



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
