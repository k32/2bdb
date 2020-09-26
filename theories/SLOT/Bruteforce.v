(** * SLOT model checker *)
From LibTx Require Import
     FoldIn
     Misc
     EventTrace
     Permutation
     SLOT.Hoare
     SLOT.Ensemble
     SLOT.Generator
     SLOT.Zipper.

Module Zip := SLOT.Zipper.OfLists.
Module Zip0 := SLOT.Zipper.

From Coq Require Import
     List
     Program
     Logic.Classical_Prop
     Logic.Decidable
     Relations.

Import ListNotations.

Open Scope list_scope.
Open Scope hoare_scope.

Class te_commut_rel {A} :=
  { comm_rel : relation A;
    comm_rel_symm : symmetric _ comm_rel;
    comm_rel_dec : forall a b, decidable (comm_rel a b);
  }.

Definition always_can_switch {A} (_ _ : A) : Prop := True.

Definition trace_elems_don't_commute `{StateSpace} a b :=
  not (trace_elems_commute a b).

Program Instance nonCommRel `{StateSpace} : @te_commut_rel TE :=
  { comm_rel := trace_elems_don't_commute
  }.
Next Obligation.
unfold symmetric. intros x y Hcomm.
firstorder. Qed.
Next Obligation.
unfold decidable. apply classic. Qed.

Program Instance alwaysCommRel {TE} : @te_commut_rel TE :=
  { comm_rel := always_can_switch;
  }.
Next Obligation.
easy. Qed.
Next Obligation.
cbv. left. easy. Qed.

Section restricted_ensemble.
  Context `{HSsp : StateSpace} (Hcomm_rel : @te_commut_rel TE).

  Definition can_pick l a := Forall (comm_rel a) l.

  Inductive RestrictedEnsemble (e : @TraceEnsemble TE) (non_comm_set : list TE) : TraceEnsemble :=
  | restr_ens_nil :
      e [] ->
      RestrictedEnsemble e non_comm_set []
  | restr_ens_cons : forall te t,
      e (te :: t) ->
      can_pick non_comm_set te ->
      RestrictedEnsemble e non_comm_set (te :: t).

  Inductive UniqueInterleaving comm_set : list TE -> list TE -> TraceEnsemble :=
  | uilv_cons_l : forall l t1 t2 t,
      can_pick comm_set l ->
      UniqueInterleaving [] t1 t2 t ->
      UniqueInterleaving comm_set (l :: t1) t2 (l :: t)
  | uilv_cons_r1 : forall l r t1 t2 t,
      can_pick (l :: comm_set) r ->
      UniqueInterleaving [] (l :: t1) t2 (l :: t) ->
      UniqueInterleaving comm_set (l :: t1) (r :: t2) (r :: l :: t)
  | uilv_cons_r2 : forall r1 r2 t1 t2 t,
      can_pick comm_set r2 ->
      UniqueInterleaving [] t1 (r1 :: t2) (r1 :: t) ->
      UniqueInterleaving comm_set t1 (r2 :: r1 :: t2) (r2 :: r1 :: t)
  | uilv_nil : forall t, UniqueInterleaving comm_set [] t t.
End restricted_ensemble.

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
          inversion_ H'.
      - right. intros H.
        inversion_ H.
    }
  Defined.
End forall_dec.

Section picker_idea.
  Context `{HSsp : StateSpace} {Hcomm_rel : @te_commut_rel TE}.

  Let T := list TE.
  Let TT := list T.

  Fail Inductive Picker (non_comm_set : list TE) : TT -> TT -> TE -> Prop :=
  | picker_skip : forall (t : T) te (tt tt' : TT)
                    (p : Picker tt tt' te),
      Picker non_comm_set (t :: tt) (t :: tt') te
  | picker_pick : forall te,
      can_pick non_comm_set te ->
      Picker non_comm_set te.
End picker_idea.

Section multi_interleaving2.
  Section defn.
    Context `{Hssp : StateSpace} (Hcomm_rel : @te_commut_rel TE).

    Definition Traces := @Zip.t TE.

    Let T := list TE.
    Let TT := list T.

    Definition can_skip_to (z : Traces) (te : TE) : Prop :=
      match z with
      | (_, [], _) => True
      | (_, te' :: _, _) => comm_rel te te'
      end.

    Inductive MInt : Traces -> @TraceEnsemble TE :=
    | mint_nil : forall t r,
        filter Zip.nonempty r = [] ->
        MInt ([], t, r) t
    | mint_pick : forall (l r : TT) (te : TE) (rest t : T),
        MInt (Zip.rewind (l, rest, r)) t ->
        MInt (l, te :: rest, r) (te :: t)
    | mint_skip : forall z te t,
        can_skip_to z te ->
        MInt (Zip.movr z) (te :: t) ->
        MInt z (te :: t).

    Definition MultiIlv (tt : TT) : @TraceEnsemble TE :=
      MInt (Zip.of_list tt).
  End defn.

  Global Arguments Traces {_}.
End multi_interleaving2.

Section tests.
  Context `{Hssp : StateSpace} (a b c d e f : TE).

  Goal MultiIlv alwaysCommRel [[a;b]; [c;d]] [a; b; c; d].
  Proof. repeat constructor. Qed.

  Goal MultiIlv alwaysCommRel [[a;b]; [c;d]] [c; d; a; b].
  Proof. repeat constructor. Qed.

  Goal MultiIlv alwaysCommRel [[a;b]; [c;d]] [a;c;b;d].
  Proof. repeat constructor. Qed.

  Goal MultiIlv alwaysCommRel [[a]; [b]; [c]] [a;b;c].
  Proof. repeat constructor. Qed.

  Goal MultiIlv alwaysCommRel [[a]; [b]; [c]] [b;a;c].
  Proof. repeat constructor. Qed.

  Goal MultiIlv alwaysCommRel [[a]; [b]; [c]] [b;c;a].
  Proof. repeat constructor. Qed.

  Goal MultiIlv alwaysCommRel [[a]; [b]; [c]] [c;a;b].
  Proof. repeat constructor. Qed.

  Goal MultiIlv alwaysCommRel [[a]; [b]; [c]] [c;b;a].
  Proof. repeat constructor. Qed.
End tests.

Section uniq.
  Context `{Hssp : StateSpace}.

  Lemma always_can_skip_to z (te : TE) : can_skip_to alwaysCommRel z te.
  Proof.
    now destruct z as [[l [|m]] r].
  Qed.

  Hint Resolve always_can_skip_to : slot.

  Fixpoint ilv_to_mint (t : list TE)
           t1 t2 (Ht : Interleaving t1 t2 t) {struct Ht} :
    MInt alwaysCommRel (Zip.of_list [t1; t2]) t.
  Proof with eauto with slot.
    destruct t1 as [|te1 t1].
    { apply interleaving_nil in Ht. subst.
      destruct t; repeat constructor.
    }
    destruct t2 as [|te2 t2].
    { apply interleaving_symm, interleaving_nil in Ht. subst.
      constructor...
    }
    simpl.
    remember (te1 :: t1) as t1_.
    remember (te2 :: t2) as t2_.
    destruct Ht as [te t1' t2' t Ht
                   |te t1' t2' t Ht
                   |]; subst.
    - eapply ilv_to_mint in Ht.
      now constructor.
    - eapply ilv_to_mint in Ht...
      apply mint_skip...
      constructor...
    - discriminate.
  Qed.

  Theorem mint_sufficient_replacement tt :
    sufficient_replacement_p (MultiIlv alwaysCommRel tt) (MultiIlv nonCommRel tt).
  Proof with eauto with slot.
    intros t Ht.
    unfold MultiIlv in *.
    induction Ht.
    - exists t. split; constructor...
    - destruct IHHt as [t' [Ht' HPerm]].
      exists (te :: t'). split.
      + constructor...
      + apply perm_cons...
    - destruct IHHt as [t' [Ht' Hperm]]. clear Ht.
      destruct t' as [|te' t'].
      { exfalso. inversion_ Hperm. symmetry in H0. now apply app_cons_not_nil in H0. }
      destruct z as [[l m] r].
      destruct m as [|te0 rest].
      + exists (te' :: t'). split... constructor...
      +

        inversion_ Hperm.
        * exists (te' :: t'). split... constructor...

        exists (te' :: t'). split...

        constructor...
        unfold can_skip_to.


        simpl in *.
        destruct m as [|m_h m].
        * simpl in *.



      destruct t as [].
      2:{
      + exists [te]. split.
        * constructor. unfold can_skip_to

    remember tt as tt_.
    induction Ht.
    - exists t. split...
      apply mint_nil.


  Fixpoint canonicalize_mint (t : list TE) z
           (Ht : MInt alwaysCommRel z t)
           s s' (Hls : LongStep s t s') {struct Ht} :
    exists t', MInt nonCommRel z t' /\ LongStep s t' s'.
  Proof with eauto with slot.
    destruct Ht as [t
                   |l r te rest t Ht
                   |z te t Hpick Ht
                   ].
    - exists t. split... constructor...
    - inversion_ Hls.
      eapply canonicalize_mint with (s := s'0) (s' := s') in Ht...
      destruct Ht as [t' [Ht' Hls']].
      exists (te :: t'). split...
      constructor. assumption.
    - (* Welcome to the hell proof: *)
      remember (te :: t) as t_.
      eapply canonicalize_mint in Ht...
      destruct Ht as [[|te_r t'] [Ht' Hls']].
      +
        inversion_ Ht'.



    destruct z as [[l [|te' m]] r].
    { eapply canonicalize_mint in Ht...
      destruct Ht as [[|te' t'] [Ht' Hls']].
      - exists []. split...
        cbn in Ht'.
        destruct r as [|r].
        + inversion_ Ht'.
        + inversion_ Ht'.  constructor...
      - exists (te' :: t'). split...
        constructor...
    }


    destruct (@comm_rel_dec _ nonCommRel te te').
    {
      exists t'. split...



    { eapply canonicalize_mint in Ht...
      destruct Ht as [t' [Ht' Hls']].



      exists t'. split...
      destruct t' as [|t'].
      -


(**** GOMI GOMI ***************************************************)


Section multi_interleaving.
  Section defn.
    Context `{Hssp : StateSpace} (Hcomm_rel : @te_commut_rel TE).

    Definition Traces := @Zip.t TE.

    Definition push te (traces : Traces) :=
      match traces with
      | (l, v, r) => (l, te :: v, r)
      end.

    Let T := list TE.
    Let TT := list T.

    Definition can_pick_ te l :=
      match l with
      | [] => True
      | (te' :: _) => comm_rel te te'
      end.

    Definition can_pick' (tt : TT) (te : TE) : Prop :=
      Forall (can_pick_ te) tt.

    Inductive MInt : Traces -> @TraceEnsemble TE :=
    | mint_nil : forall t,
        MInt ([], t, []) t
    | mint_pick : forall (l r : TT) (te : TE) (rest t : T),
        can_pick' l te ->
        MInt (Zip.rewind (l, rest, r)) t ->
        MInt (l, te :: rest, r) (te :: t)
    | mint_skip : forall z t,
        MInt (Zip.movr z) t ->
        MInt z t.

    Definition MultiIlv (tt : TT) : @TraceEnsemble TE :=
      match tt with
      | [] => eq []
      | (e :: rest) => MInt ([], e, rest)
      end.
  End defn.

  Global Arguments Traces {_}.
End multi_interleaving.

Section tests.
  Context `{Hssp : StateSpace} (a b c d e f : TE).

  Goal MultiIlv alwaysCommRel [[a;b]; [c;d]] [a; b; c; d].
  Proof.
    repeat constructor.
  Qed.

  Goal MultiIlv alwaysCommRel [[a;b]; [c;d]] [c; d; a; b].
  Proof.
    repeat constructor.
  Qed.

  Goal MultiIlv alwaysCommRel [[a;b]; [c;d]] [a;c;b;d].
  Proof.
    repeat constructor.
  Qed.
End tests.

Section uniq.
  Context `{Hssp : StateSpace}.

  Lemma always_can_pick l (te : TE) : can_pick' alwaysCommRel l te.
  Proof.
    unfold can_pick', comm_rel, alwaysCommRel, always_can_switch.
    induction l.
    - constructor.
    - constructor.
      + destruct a; easy.
      + assumption.
  Qed.

  Hint Resolve always_can_pick : slot.

  Fixpoint ilv_to_mint (t : list TE)
           t1 t2 (Ht : Interleaving t1 t2 t)
           s s' (Hls : LongStep s t s') {struct Ht} :
    exists t', MInt alwaysCommRel (Zip.of_list [t1; t2]) t' /\ LongStep s t' s'.
  Proof with eauto with slot.
    destruct t1 as [|te1 t1].
    { exists t2.
      split...
      destruct t2; repeat constructor.
    }
    destruct t2 as [|te2 t2].
    { exists (te1 :: t1). simpl. split...
      constructor.
    }
    simpl.
    remember (te1 :: t1) as t_.
    destruct Ht as [te t1' t2' t Ht
                   |te t1' t2' t Ht
                   |].
    - inversion_ Hls.
      eapply ilv_to_mint in Ht...
      destruct Ht as [t' [Ht' Hls']].
      exists (te :: t'). split...
      constructor...
    - inversion_ Hls.
      eapply ilv_to_mint in Ht...
      destruct Ht as [t' [Ht' Hls']].
      exists (te :: t'). split...
      apply mint_skip.
      simpl.
      apply mint_pick...
    - discriminate.
  Qed.

  Lemma can_pick_dec te a : decidable (can_pick_ nonCommRel te a).
  Proof.
    (* TODO: don't abuse classic *)
    apply classic.
  Qed.

  Fixpoint canonicalize_mint2 (t : list TE) z
           (Ht : MInt alwaysCommRel z t)
           s s' (Hls : LongStep s t s') {struct Ht} :
    exists t', MInt nonCommRel z t' /\ LongStep s t' s'.
  Proof with eauto with slot.
    destruct Ht as [t
                   |l r te rest t Hpick Ht
                   |z t Ht
                   ].
    1:{ exists t. split... constructor. }
    (* Skip case is relatively easy: *)
    2:{ eapply canonicalize_mint2 in Ht...
        destruct Ht as [t' [Ht' Hls']].
        exists t'. split...
        constructor. assumption.
    }
    (* Welcome to the hell proof *)
    destruct l.
    - eapply canonicalize_mint2


    destruct (Forall_dec (can_pick_ nonCommRel te) l).
    { apply can_pick_dec. }
    { eapply canonicalize_mint2 in Hls...
      destruct l.
      -





  Fixpoint canonicalize_mint_ (t : list TE)
           z (Ht : MInt alwaysCommRel z t)
           s s' (Hls : LongStep s t s') {struct Ht} :
    exists t', MInt nonCommRel z t' /\ LongStep s t' s'.
  Proof with eauto with slot.
    destruct Ht as [t
                   |l r te rest t Hpick Ht
                   |z t Ht
                   ].
    { exists t. split...
      constructor.
    }
    2:{ apply (canonicalize_mint_ t z Ht s s' Hls).

    { clear Ht0. clear Hpick.

      destruct rest.
      - simpl in *.





  (*Fixpoint interleaving_to_mens_ t1 t2 t (H : Interleaving t1 t2 t) :
    MultiIlv [t1; t2]%vector t.
  Proof with simpl; eauto.
    destruct H;
      [pose (i0 := fin2_zero); pose (tx := t1)
      |pose (i0 := fin2_one); pose (tx := t2)
      |exists fin2_zero; eapply mint_nil; repeat consturctor
      ];
      (* Resolve goals 1-2: *)
      exists i0;
      (* Obtain induction hypothesis: *)
      eapply interleaving_to_mens_ in H; destruct H as [i H];
      apply
      (* Check if we keep direction or switch it: *)
      (destruct (Fin.eq_dec i i0);
       [(* Keep direction, resolve by contructor: *)
         subst; apply mint_keep with (rest := tx); simpl; auto
       |(* Switch direction: *)
        remember ([t1; t2]%vector) as t_;
        destruct t; subst t_;
        [inversion_ H;
         vec_forall_nil;
         eapply mint_keep; simpl; eauto;
         eapply mint_nil; simpl; eauto;
         now resolve_vec_all_nil
        |apply mint_switch with (j := i) (rest := tx); simpl; eauto;
         unfold always_can_switch;
         now firstorder
        ]
      ]).
  Defined.*)

  Definition MIntUniq_ (tt : list (list TE)) (t : list TE) :=
    exists z, zipper_of z tt ->
         MInt_ trace_elems_don't_commute z t.

  Fixpoint canonicalize_mint (t : list TE) traces
             s s'
             (Ht : MInt_ always_can_switch traces t)
             (Hls : LongStep s t s') {struct Ht} :
    exists t', MInt_ trace_elems_don't_commute traces t' /\ LongStep s t' s'.
  Proof with eauto with slot.
    destruct Ht as [t
                   |l m r t Ht
                   |l m r t Ht
                   |l r rest te t Ht
                   |l r rest traces' te t Htraces' Ht
                   |l r rest traces' te1 te2 t Hte12 Htraces Ht
                   ].
    { exists t.
      firstorder.
      constructor.
    }
    { apply canonicalize_mint with (s := s) (s' := s') in Ht...
      destruct Ht as [t' [Ht' Hss']].
      exists t'.
      split...
      constructor...
    }
    { apply canonicalize_mint with (s := s) (s' := s') in Ht...
      destruct Ht as [t' [Ht' Hss']].
      exists t'.
      split...
      constructor...
    }
    { long_step Hls.
      eapply canonicalize_mint in Hls...
      destruct Hls as [t' [Ht' Hss']].
      exists (te :: t').
      split...
      constructor...
    }
    { long_step Hls.
      eapply canonicalize_mint in Hls...
      destruct Hls as [t' [Ht' Hss']].
      exists (te :: t').
      split...
      eapply mint_cons_l...
    }
    {


      destruct (Hcomm_dec te1 te2).
      2:{

      { apply trace_elems_commute_head in Hls; try assumption.
        long_step Hls.
        induction Ht.
        6:{
        apply canonicalize_mint with

  Definition uilv_add_by_constr {N} te (t : list TE) (traces : Traces N)
             i j (Ht : MInt_ trace_elems_don't_commute j traces t)
             s s' (Hls : LongStep s (te :: t) s')
             (H : trivial_add i j t te) :
    MInt_ trace_elems_don't_commute i (push_te traces i te) (te :: t).
  Proof with autorewrite with vector; eauto with vector.
    unfold push_te, trivial_add in *.
    destruct H as [Hij|H].
    (* [i=j], solving by constructor: *)
    { subst.
      eapply mint_cons. with (rest := traces[@j])...
    }
    destruct t as [|te0 t].
    (* [t] is empty, solving by constructor: *)
    { inversion_ Ht.
      eapply mint_keep with (rest := [])...
      { replace traces[@i] with ([]:list TE)...
        eapply vec_forall_nth...
      }
      eapply mint_nil...
      eapply vec_replace_forall_rev...
    }
    destruct H as [Hij Hte].
    (* [te] and [te0] don't commute, solving by constructor: *)
    eapply mint_switch with (rest := traces[@i])...
  Defined.

  Fixpoint uilv_add {N} te (t : list TE) (traces : Traces N)
           i j (Ht : MInt_ trace_elems_don't_commute j traces t)
           s s' (Hls : LongStep s (te :: t) s')
           {struct Ht} :
    (exists t', MInt_ trace_elems_don't_commute j (push_te traces i te) t' /\
           LongStep s t' s') \/
    (MInt_ trace_elems_don't_commute i (push_te traces i te) (te :: t) /\
     LongStep s (te :: t) s' /\ trivial_add i j t te).
  Proof with autorewrite with vector; eauto with vector.
    unfold push_te.
    destruct (trivial_add_dec i j t te) as [Htriv|Htriv].
    { right. clear uilv_add.
      eapply uilv_add_by_contr in Htriv as H...
    }
    { (* Simplify [Htriv]: *)
      unfold trivial_add in Htriv.
      destruct (Fin.eq_dec i j) as [Hij|Hij]; [exfalso; firstorder|idtac].
      destruct t as [|te0 t]; [exfalso; firstorder|idtac].
      destruct (Hcomm_dec te0 te) as [Hcomm|Hcomm]; [idtac|exfalso; firstorder].
      (* Use commutativity hypothesis: *)
      apply trace_elems_commute_head in Hls; [idtac|assumption].
      long_step Hls.
      inversion Ht as [vec Hvec|? ? ? ? Hj Hcont|? ? ? ? ? ? Hjj0 Hswitch Hj Hcont];
        subst; clear Ht.
      { eapply uilv_add with (te := te) (i := i) (s := s0) (s' := s') in Hcont...
        destruct Hcont as [[t' [Hu Ht']]|[Hu [Ht' Htriv']]].
        { left.
          unfold push_te in Hu.
          autorewrite with vector in Hu.
          rewrite vec_replace_nth_rewr, Vec.replace_replace_neq in Hu...
          exists (te0 :: t').
          split.
          - eapply mint_keep...
          - forward s0...
        }
        { unfold trivial_add in Htriv'.
          destruct Htriv'; [contradiction Hij|idtac].

          inversion

          destruct t as [|te0_ t].
          2:{ destruct H as [? nonsense].
              contradiction nonsense.

          left.

          unfold push_te in Hu.
          autorewrite with vector in Hu.
          rewrite vec_replace_nth_rewr, Vec.replace_replace_neq in Hu...
          exists (te0 :: te :: t').
          split.
          - eapply mint_switch with (rest0 := rest)...
            left.








        2:{ unfold trivial_add in Htriv'.
            destruct Htriv' as [nonsense|H]; try contradiction n.

        { left.




    (* Let's solve "easy" cases first: *)
    destruct (Fin.eq_dec i j) as [Hij|Hij].
    (* [i=j], solving by constructor: *)
    { clear uilv_add.
      subst.
      right. exists (te :: t).
      split; try split...
      eapply mint_keep with (rest := traces[@j])...
    }
    destruct t as [|te0 t].
    (* [t] is empty, solving by constructor: *)
    { clear uilv_add.
      right. exists [te].
      split; try split...
      inversion_ Ht.
      eapply mint_keep with (rest := [])...
      { replace traces[@i] with ([]:list TE)...
        eapply vec_forall_nth...
      }
      eapply mint_nil...
      eapply vec_replace_forall_rev...
    }
    destruct (Hcomm_dec te0 te).
    (* [te] and [te0] don't commute, solving by constructor: *)
    2:{ clear uilv_add.
        right. exists (te :: te0 :: t).
        split; try split...
        eapply mint_switch with (rest := traces[@i])...
    }
    (* Now to the interesting part: *)
    { left.
      apply trace_elems_commute_head in Hls...
      long_step Hls.
      inversion Ht as [vec Hvec|? ? ? ? Hj Hcont|? ? ? ? ? ? Hjj0 Hswitch Hj Hcont];
        clear Ht; subst.
      - eapply uilv_add with (te := te) (i := i) (s := s0) (s' := s') in Hcont as Hcont'...
        clear uilv_add.
        unfold push_te in Hcont'; autorewrite with vector in Hcont'.
        destruct Hcont' as [[t' [Hu Ht']]|[t' [Hu [Ht' Hcontr]]]].
        { rewrite vec_replace_nth_rewr, Vec.replace_replace_neq in Hu...
          exists (te0 :: t').
          split.
          - eapply mint_keep...
          - forward s0...
        }
        { rewrite vec_replace_nth_rewr, Vec.replace_replace_neq in Hu...
          destruct Hcontr as [Hcontr|Hcontr].
          { contradiction Hij. }
          { destruct t as [|te_ t]; subst.
            - inversion_ Hcont.
              replace rest with ([] : list TE) in * by
                  now apply vec_replace_forall in H0.
              exists [te0; te].
              split.
              + eapply mint_switch...
              + forward s0...
            -






  (*Fixpoint uilv_add {N} te1 te2 (t : list TE) (traces : Traces N)
           i j (Ht : MInt_ trace_elems_don't_commute j traces (te1 :: t))
           s s' (Hls : LongStep s (te2 :: te1 :: t) s')
           (Hcomm : trace_elems_commute te1 te2)
           {struct Ht} :
    exists t', MInt_ trace_elems_don't_commute j (push_te traces i te2) t' /\ LongStep s t' s'.
  Proof with eauto with vector.
    Ltac unpush := unfold push_te; autorewrite with vector.
    destruct (Fin.eq_dec i j) as [Hij|Hij].
    { subst.
      exists (te2 :: te1 :: t).
      split...
      eapply mint_keep with (rest := traces[@j])...
      + now unpush.
      + now unpush.
    }
    (* [i <> j]: *)
    inversion Ht as [vec Hvec|? ? ? ? Hj Hcont|? ? ? ? ? ? Hjj0 Hswitch Hj Hcont]; clear Ht; subst.
    { destruct t as [|te0 t].
      { inversion_ Hcont.
        exists [te1; te2].
        unpush.
        apply Hcomm in Hls.
        replace rest with ([] : list TE) in *...
        split...
        apply mint_switch with (j0 := i) (rest0 := [])...
        apply mint_keep with (rest0 := []) (i0 := i)...
        - transform_vec_replace_nth...
          replace traces[@i] with ([]:list TE)...
          { eapply vec_forall_replace_nth... }
        - apply mint_nil.
          rewrite Vec.replace_replace_neq, Vec.replace_replace_eq, Vec.replace_replace_neq...
          eapply vec_replace_forall_rev...
      }
      { eapply trace_elems_commute_head in Hls...
        long_step Hls.
        destruct (Hcomm_dec te0 te2) as [Hcomm'|Hcomm'].
        { eapply uilv_add with (i := i) in Hls...
          destruct Hls as [t' [Hu Ht']].
          exists (te1 :: t').
          split.
          - eapply mint_keep with (rest0 := rest)...
            + unpush...
            + unfold push_te in *.
              rewrite Vec.replace_replace_neq...
              rewrite <-vec_replace_nth_rewr in Hu...
          - forward s0...
        }
        { exists (te1 :: te0 :: te2 :: t).
          split.
          - eapply mint_switch with (j0 := i) (rest0 := rest)...
            + left.*)


  Fixpoint canonicalize_mens_ {N} (t : list TE) (traces : Traces N)
             s s' i
             (Ht : MInt_ always_can_switch i traces t)
             (Hls : LongStep s t s') :
    exists t' k, MInt_ trace_elems_don't_commute k traces t' /\ LongStep s t' s'.
  Proof with eauto with slot.
    destruct Ht as [vec Hvec|? ? ? ? Hj Hcont|? ? te ? ? ? Hjj0 Hswitch Hj Hcont].
    { exists []. exists i.
      split...
      constructor...
    }
    { long_step Hls.
      eapply canonicalize_mens_ in Hls...
      destruct Hls as [t' [k [Huniq Ht']]].
      remember (Vec.replace traces i rest) as traces0.
      replace traces with (Vec.replace traces0 i (te :: traces0[@i])).
      - eapply uilv_add...
      - subst.
        rewrite Vec.replace_replace_eq, vec_replace_nth, <- Hj, Vec.replace_id.
        reflexivity.
    }
    { long_step Hls.
      eapply canonicalize_mens_ in Hls...
      destruct Hls as [t' [k [Huniq Ht']]].
      remember (Vec.replace traces i rest) as traces0.
      replace traces with (Vec.replace traces0 i (te :: traces0[@i])).
      - eapply uilv_add...
      - subst.
        rewrite Vec.replace_replace_eq, vec_replace_nth, <- Hj, Vec.replace_id.
        reflexivity.
    }
  Qed.

  Lemma mint_uniq_correct_ : forall {N} P Q (traces : Traces N),
      -{{P}} MIntUniq_ traces {{Q}} ->
      -{{P}} MultiIlv traces {{Q}}.
  Proof with eauto.
    intros * H t Ht. unfold_ht.
    destruct Ht as [i Ht].
    eapply canonicalize_mens_ in Hls...
    destruct Hls as [t' [k [Hu Ht']]].
    eapply H...
    exists k...
  Qed.

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
