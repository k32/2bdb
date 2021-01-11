(** * SLOT model checker *)
From LibTx Require Import
     FoldIn
     Misc
     EventTrace
     Permutation
     SLOT.Zipper
     SLOT.Hoare
     SLOT.Ensemble
     SLOT.Generator.

From Coq Require Import
     List
     Program
     Logic.Classical_Prop
     Logic.Decidable
     Relations
     Lia.

Import ListNotations.

From Coq Require
     Vector
     Fin.

Module Z := Zipper.

Module Vec := Vector.

Open Scope list_scope.
Open Scope hoare_scope.
Open Scope zipper_scope.

Lemma trace_elems_commute_dec `{StateSpace} a b : decidable (trace_elems_commute a b).
Proof.
  apply classic.
Qed.

Section comm_rel.
  Class te_commut_rel {A} :=
    { comm_rel : relation A;
      comm_rel_symm : symmetric _ comm_rel;
      comm_rel_dec : forall a b, decidable (comm_rel a b);
    }.

  Definition always_can_switch {A} (_ _ : A) : Prop := True.

  Program Instance nonCommRel `{StateSpace} : @te_commut_rel TE :=
    { comm_rel a b := not (trace_elems_commute a b)
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
End comm_rel.

Module ZipIlv.
  Section defn.
    Context `{Hssp : StateSpace} (Hcomm_rel : @te_commut_rel TE).

    Let T := list TE.
    Let TT := list T.

    Definition Traces := Z.t T.

    Let clean (l : T) := match l with
                         | [] => None
                         | _  => Some l
                         end.

    Inductive MInt_ : Traces -> @TraceEnsemble TE :=
    | mint_nil :
        MInt_ ([], None, []) []
    | mint_cons : forall te rest l r t,
        MInt_ (l, clean rest, r) t ->
        MInt_ (l, Some (te :: rest), r) (te :: t)
    | mint_cons_l : forall te rest l r zipper t,
        zipper >z (l, clean rest, r) ->
        MInt_ zipper t ->
        MInt_ (l, Some (te :: rest), r) (te :: t)
    | mint_cons_r : forall te te' rest l r zipper t,
        zipper <z (l, clean rest, r)->
        comm_rel te te' ->
        MInt_ zipper (te' :: t) ->
        MInt_ (l, Some (te :: rest), r) (te :: te' :: t).

    Inductive MInt tt : @TraceEnsemble TE :=
      mint : forall z t,
        Z.zipper_of z tt ->
        MInt_ z t ->
        MInt tt t.

    Ltac inv H := inversion_ H; clear H.

    Section tests.
      Goal forall a b,
          MInt [[a]; [b]] [a; b] /\
          (comm_rel a b -> MInt [[a]; [b]] [b; a]).
      Proof.
        split.
        { apply mint with (z := ([], Some [a], [[b]])).
          { constructor. }
          apply mint_cons_l with (zipper := ([], Some [b], [])); repeat constructor.
        }
        { intros Hcomm.
          apply mint with (z := ([[a]], Some [b], [])).
          { repeat constructor. }
          apply mint_cons_r with (zipper := ([], Some [a], [])); repeat constructor.
          now apply comm_rel_symm.
        }
      Qed.

      Goal forall a b t,
          comm_rel a b ->
          MInt [[a]; [b]] t ->
          t = [a; b] \/ t = [b; a].
        intros a b t Hcomm H. destruct H. cbv in H.
        inv H.
        - inv H0.
          + inv H5.
          + inv H5. inv H6.
            * inversion H4. subst. left. reflexivity.
            * exfalso. inv H4.
            * exfalso. inv H4.
          + exfalso. inv H5.
        - inv H3.
          inv H0.
          + exfalso. inv H5.
          + exfalso. inv H5.
          + inv H5. inv H7.
            * inversion H0. subst. right. reflexivity.
            * exfalso. inv H1.
            * exfalso. inv H2.
      Qed.
    End tests.
  End defn.
End ZipIlv.

Module VecIlv.
  Open Scope vector_scope.

  Section defn.
    Context `{Hssp : StateSpace} (Hcomm_rel : @te_commut_rel TE).

    Let T := list TE.
    Let TT := list T.

    Definition Traces := Vec.t T.

    Definition vec_append {N} i te (vec : Vec.t (list TE) N) :=
      let rest := Vec.nth vec i in
      Vec.replace vec i (te :: rest).

    Inductive MInt Nelems : forall (start : Fin.t Nelems), Traces Nelems -> @TraceEnsemble TE :=
    | mint_nil : forall i,
        MInt Nelems i (vec_same Nelems []) []
    | mint_cons1 : forall (i j : Fin.t Nelems) vec te t,
        i <= j ->
        MInt Nelems j vec t ->
        MInt Nelems i (vec_append i te vec) (te :: t)
    | mint_cons2 : forall (i j : Fin.t Nelems) vec te_i te_j t,
        j < i ->
        comm_rel te_i te_j ->
        MInt Nelems j vec (te_j :: t) ->
        MInt Nelems i (vec_append i te_i vec) (te_i :: te_j :: t).

    Definition MInt_ (tt : TT) : @TraceEnsemble TE :=
      fun t => exists i, MInt (length tt) i (Vec.of_list tt) t.
  End defn.

  Section prune_interleavings.
    Context `{Hssp : StateSpace}.

    Lemma vec_append_swap {N} (i j : Fin.t N) vec (te_i te_j : TE) :
      i <> j ->
      vec_append j te_j (vec_append i te_i vec) = vec_append i te_i (vec_append j te_j vec).
    Admitted.

    Ltac swap_vec_append := rewrite vec_append_swap; [|intros nonsense; subst; lia].

    Fixpoint mint_add0 {N} (i k : Fin.t N) te_i te' t0 vec
             (Ht : MInt nonCommRel N k vec (te' :: t0))
             (Hik : k < i)
             (Hcomm0 : trace_elems_commute te_i te')
             {struct Ht} :
      exists t' : list TE,
          MInt nonCommRel N k (vec_append i te_i vec) (te' :: t') /\
          Permutation trace_elems_commute (te_i :: te' :: t0) (te' :: t').
    Proof with eauto.
      (* Welcome to the hell proof! *)
      remember (te' :: t0) as t_.
      destruct Ht as [k
                     |k j vec te_k t Hij Ht
                     |k j vec te_k te_j t Hij Hcomm Ht
                     ];
        [discriminate
        |replace te' with te_k in * by congruence; clear Heqt_..
        ].
      2:{ destruct (trace_elems_commute_dec te_i te_j).
          - apply mint_add0 with (te_i := te_i) (i := i) in Ht; [|lia|assumption].
            destruct Ht as [t' [Ht' Hperm']].
            exists (te_j :: t'). split.
            + swap_vec_append.
              eapply mint_cons2...
            + apply permut_cons with (a := te_k) in Hperm'.
              eapply permut_trans...
              now apply permut_head'.
          - exists (te_i :: te_j :: t). split.
            + swap_vec_append.
              apply mint_cons1 with (j0 := i); [lia|].
              apply mint_cons2 with (j0 := j); [lia|auto..].
            + now apply permut_head'.
      }
      { inversion_ Ht.
        - exists [te_i]. split.
          + swap_vec_append.
            apply mint_cons1 with (j0 := i); [lia|].
            apply mint_cons1 with (j0 := i); [lia|].
            constructor.
          + now apply permut_head'.
        - rename te into te_j.
          destruct (PeanoNat.Nat.lt_ge_cases j i).
          2:{ exists (te_i :: te_j :: t1). split.
              - swap_vec_append.
                apply mint_cons1 with (j1 := i); [lia|].
                apply mint_cons1 with (j1 := j); [lia|assumption].
              - now apply permut_head'.
          }
          { destruct (trace_elems_commute_dec te_i te_j) as [Hte_ij|Hte_ij].
            - apply mint_add0 with (i := i) (te_i := te_i) in Ht; [|lia|assumption].
              destruct Ht as [t' [Ht' Hperm']].
              exists (te_j :: t'). split.
              + swap_vec_append.
                eapply mint_cons1...
              + apply permut_cons with (a := te_k) in Hperm'.
                now apply permut_head.
            - exists (te_i :: te_j :: t1). split.
              + swap_vec_append.
                apply mint_cons1 with (j1 := i); [lia|].
                apply mint_cons2 with (j1 := j); [lia|assumption..].
              + apply permut_head; [assumption|constructor].
          }
        - rename j0 into i0. cbn in H0.
          destruct (PeanoNat.Nat.lt_ge_cases j i).
          2:{ exists (te_i :: te_i0 :: te_j :: t1). split.
              + swap_vec_append.
                apply mint_cons1 with (j0 := i); [lia|].
                apply mint_cons1 with (j0 := j); [lia|assumption].
              + now apply permut_head'.
          }
          { destruct (trace_elems_commute_dec te_i te_i0).
            - apply mint_add0 with (i := i) (te_i := te_i) in Ht; [|lia|assumption].
              destruct Ht as [t' [Ht' Hperm']].
              exists (te_i0 :: t'). split.
              + swap_vec_append.
                eapply mint_cons1...
              + apply permut_cons with (a := te_k) in Hperm'.
                now apply permut_head.
            - exists (te_i :: te_i0 :: te_j :: t1). split.
              + swap_vec_append.
                apply mint_cons1 with (j0 := i); [lia|].
                apply mint_cons2 with (j0 := j); [lia|assumption..].
              + apply permut_head.
                * assumption.
                * constructor.
          }
      }
    Qed.

    Lemma mint_add {N} (i k : Fin.t N) t te vec
          (Ht : MInt nonCommRel N k vec t) :
      exists t' : list TE, exists (j : Fin.t N),
          MInt nonCommRel N j (vec_append i te vec) t' /\
          Permutation trace_elems_commute (te :: t) t'.
    Proof.
      destruct (PeanoNat.Nat.lt_ge_cases k i) as [Hki|Hki].
      2:{ exists (te :: t). exists i. split.
          - apply mint_cons1 with (j := k); auto.
          - constructor.
      }
      destruct t as [|te' t].
      { inversion_ Ht.
        exists [te]. exists i. split.
        - eapply mint_cons1; eauto. constructor.
        - constructor.
      }
      destruct (trace_elems_commute_dec te te') as [Hcomm|Hcomm].
      { eapply mint_add0 in Hcomm; eauto.
        destruct Hcomm as [t' H].
        exists (te' :: t'). exists k. assumption.
      }
      { exists (te :: te' :: t). exists i. split.
        - apply mint_cons2 with (j := k); auto.
        - constructor.
      }
    Qed.

    Fixpoint mint_prune N i0 tt_vec t
      (Ht : MInt alwaysCommRel N i0 tt_vec t) {struct Ht} :
      exists t' : list TE, exists i : Fin.t N,
          MInt nonCommRel N i tt_vec t' /\ Permutation trace_elems_commute t t'.
    Proof.
      destruct Ht as [i
                     |i j vec te t Hij Ht
                     |i j vec te_i te_j t Hij Hcomm Ht
                     ].
      - exists []. exists i. split; constructor.
      - subst. apply mint_prune in Ht. destruct Ht as [t' [k [Ht' Hperm]]].
        specialize (mint_add i k t' te vec Ht') as H.
        destruct H as [t'' [i' [Ht'' Hperm'']]].
        exists t''. exists i'. split.
        + assumption.
        + eapply permut_cons in Hperm;
            eapply permut_trans; eauto.
      - subst. apply mint_prune in Ht. destruct Ht as [t' [k [Ht' Hperm]]].
        specialize (mint_add i k t' te_i vec Ht') as H.
        destruct H as [t'' [i' [Ht'' Hperm'']]].
        exists t''. exists i'. split.
        + assumption.
        + eapply permut_cons in Hperm;
            eapply permut_trans; eauto.
    Qed.

    Theorem mint_noncomm_sufficient tt : sufficient_replacement_p (MInt_ alwaysCommRel tt) (MInt_ nonCommRel tt).
    Proof.
      intros t Ht.
      destruct Ht as [i0 Ht]. unfold MInt_.
      remember (Vec.of_list tt) as tt_vec.
      eapply mint_prune in Ht. destruct Ht as [t' [i [Ht Hperm]]].
      exists t'. split.
      - now exists i.
      - assumption.
    Qed.
  End prune_interleavings.

  Section pack_interleaving.
    Context `{Hssp : StateSpace}.

    Lemma shiftin_append_swap {N} t (i : Fin.t N) (te : TE) vec :
      (Vec.shiftin t (vec_append i te vec)) = vec_append (Fin.L_R 1 i) te (Vec.shiftin t vec).
    Admitted.

    Lemma shiftin_cons_append {N} (vec : Vec.t (list TE) N) te t :
      Vec.shiftin (te :: t) vec = vec_append (last_fin N) te (Vec.shiftin t vec).
    Proof.
      induction vec.
      - reflexivity.
      - simpl. rewrite IHvec. reflexivity.
    Qed.

    Fixpoint shiftin_interleaving N i (vec : Vec.t (list TE) N) t1 t2 t
      (HMint : MInt alwaysCommRel N i vec t1)
      (HIlv : Interleaving t1 t2 t) {struct HIlv} :
      exists j, MInt alwaysCommRel (S N) j (Vec.shiftin t2 vec) t.
    Proof.
      destruct HIlv as [te t1' t2' t' HIlv
                       |te t1' t2' t' HIlv
                       |].
      (* Solve easy cases first: *)
      3:{ (* Null: *)
        inversion_ HMint.
        exists (last_fin N). rewrite shiftin_same. constructor.
      }
      2:{ (* t2: *)
        apply shiftin_interleaving with (t2 := t2') (t := t') in HMint; auto.
        rewrite shiftin_cons_append.
        set (k := last_fin N).
        exists k.
        destruct HMint as [j Ht'].
        destruct (last_fin_is_last j).
        - subst.
          apply mint_cons1 with (j := k); auto.
        - destruct t' as [|te' t'].
          + inversion_ Ht'.
            apply mint_cons1 with (j0 := last_fin N); constructor.
          + apply mint_cons2 with (j0 := j); auto.
            constructor.
      }
      set (i' := Fin.L_R 1 i). exists i'.
      inversion_ HMint.
      - eapply shiftin_interleaving in H4; eauto. clear HMint.
        destruct H4 as [k Ht'].
        rewrite shiftin_append_swap.
        destruct (PeanoNat.Nat.lt_ge_cases k i').
        2:{ now apply mint_cons1 with (j0 := k). }
        { destruct t' as [|te' t'].
          - inversion_ Ht'.
            apply mint_cons1 with (j0 := i'); constructor.
          - apply mint_cons2 with (j0 := k); auto; constructor.
        }
      - eapply shiftin_interleaving in H5; eauto. clear HMint.
        destruct H5 as [k Ht'].
        rewrite shiftin_append_swap.
        destruct (PeanoNat.Nat.lt_ge_cases k i').
        2:{ now apply mint_cons1 with (j0 := k). }
        { destruct t' as [|te' t'].
          - inversion_ Ht'.
            apply mint_cons1 with (j0 := i'); constructor.
          - apply mint_cons2 with (j0 := k); auto; constructor.
        }
    Qed.
  End pack_interleaving.
End VecIlv.

(* Deeply magical function from here:
http://jamesrwilcox.com/more-cardinality.html. Reproduced with
permission from the author *)
Definition fin_case n x :
  forall (P : Fin.t (S n) -> Type),
    P Fin.F1 ->
    (forall y, P (Fin.FS y)) ->
    P x :=
  match x as x0 in Fin.t n0
     return
       forall P,
         match n0 as n0' return (Fin.t n0' -> (Fin.t n0' -> Type) -> Type) with
           | 0 => fun _ _ => False
           | S m => fun x P => P Fin.F1 -> (forall x0, P (Fin.FS x0)) -> P x
         end x0 P
  with
  | Fin.F1 => fun _ H1 _ => H1
  | Fin.FS _ => fun _ _ HS => HS _
  end.

Ltac fin_dep_destruct v :=
  let v' := fresh v in
  rename v into v';
  generalize dependent v'; intros v'; pattern v';
  apply fin_case; try clear v'; [|intros v].

Ltac fin_all_cases v :=
  repeat fin_dep_destruct v ; [..|exfalso; inversion v].

Section tests.
  Goal forall (n : Fin.t 3), const True n.
  Proof.
    intros.
    fin_all_cases n.
    - constructor.
    - constructor.
    - constructor.
  Qed.

  Goal forall (n m : Fin.t 3), n < m -> const False n.
  Proof.
    intros.
    fin_all_cases n; fin_all_cases m; intros Hnm; try (lia || now inversion Hnm); cbv.
    3:{
  Abort.
End tests.

Check VecIlv.MInt.

(* I can't into Ltac, sorry *)
Ltac destruct_mint H :=
  let H__type := type of H in
  lazymatch H__type with
  | VecIlv.MInt _ ?Nelems ?i0 ?vec ?t =>
    let Hvec := fresh "Hvec" in
    let vec0 := fresh "vec" in
    let vec' := fresh "vec" in
    let i0' := fresh "pos_" in
    let Hi0' := fresh "Hpos_" in
    let i1 := fresh "pos" in
    let i2 := fresh "pos" in
    let Hij := fresh "H_" i1 "_" i2 in
    let te := fresh "te" in
    let te2 := fresh "te" in
    let Hcomm := fresh "Hcomm" in
    let t := fresh "t" in
    remember vec as vec0 eqn:Hvec;
    remember i0 as i0' eqn:Hi0';
    destruct H as [i1
                  |i1 i2 vec' te t Hij H
                  |i1 i2 vec' te te2 t Hij Hcomm H
                  ];
    [inversion_clear Hi0';
     inversion Hvec
    |fin_all_cases i1;
     fin_all_cases i2;
     intros H Hvec Hi0' Hij;
     ((now inversion Hij) || clear Hij);
     inversion_clear Hi0'
     ..
    ]
  | _ =>
    fail 100 "The argument doesn't look like MInt"
  end.

Section tests.
  Goal forall `{Hssp : StateSpace} i0 vec t, VecIlv.MInt nonCommRel 2 i0 vec t -> const True t -> False.
  Proof.
    intros *. intros H Ht.
    destruct_mint H.
    5:{ destruct_mint H.
        3:{
  Abort.

  Import Vector.VectorNotations.

  Context `{Hssp : StateSpace nat nat}.

  Let vec := [[1; 2]%list; [3; 4]%list]%vector.

  Goal forall i t, VecIlv.MInt nonCommRel 2 i vec t -> const True t -> False.
  Proof.
    subst vec.
    intros *. intros H Ht.
    destruct_mint H.
    - (* Hvec : VecIlv.vec_append Fin.F1 te vec0 = [[1; 2]%list; [3; 4]%list] *)
  Abort.
End tests.
