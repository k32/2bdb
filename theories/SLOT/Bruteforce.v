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

From Hammer Require Import
     Hammer
     Tactics.

Module Zip := SLOT.Zipper.OfLists.
Module Zip0 := SLOT.Zipper.

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

Coercion fin_to_nat : Fin.t >-> nat.
Coercion Fin.of_nat_lt : lt >-> Fin.t.

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

    Theorem pack_interleaving N i (vec : Vec.t (list TE) N) t1 t2 t :
      MInt alwaysCommRel N i vec t1 ->
      Interleaving t1 t2 t ->
      exists j, MInt alwaysCommRel (S N) j (Vec.shiftin t2 vec) t.
    Proof.
      intros H Hilv.
      set (last := last_fin N).
      induction H.
      - apply interleaving_nil in Hilv. subst.
        exists last. induction t.
        + rewrite shiftin_same. constructor.
        + replace (Vec.shiftin (a :: t) (vec_same N [])) with
              (vec_append last a (Vec.shiftin t (vec_same N []))).
          * apply mint_cons1 with (j := last); auto.
          * unfold vec_append. now rewrite shiftin_nth_last, shiftin_replace_last.
      -
    Abort.
  End pack_interleaving.
End VecIlv.
