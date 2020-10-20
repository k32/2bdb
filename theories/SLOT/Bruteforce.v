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
     Relations.

Import ListNotations.

From Coq Require
     Vector
     Fin.

Module Vec := Vector.

Open Scope list_scope.
Open Scope hoare_scope.
Open Scope zipper_scope.

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

Module PermIlv.
  (** * Interleaving of threads as permutation of trace elements

      This definition of interleaving is fairly impractical, because
      it requires unfolding all threads before interleavings can be
      calculated, and we prefer to evaluate code lazily, but it's
      useful for internal proofs *)

  Section defn.
    Context `{Hssp : StateSpace} (Hcomm_rel : @te_commut_rel TE).

    Definition tag_traces {A} (tt : list (list A)) : list (list (nat * A)) :=
      let f acc l := match acc with
                     | (i, acc) =>
                       let l' := map (fun j => (i, j)) l in
                       (S i, l'  :: acc)
                     end in
      snd (fold_left f tt (0, [])).

    Definition can_swap (a b : nat * TE) : Prop :=
      match a, b with
      | (pid1, te1), (pid2, te2) => pid1 <> pid2 /\ comm_rel te1 te2
      end.

    Definition TaggedPermutation (tt : list (list TE)) (t : list (nat * TE)) : Prop :=
      Permutation can_swap (concat (tag_traces tt)) t.

    Inductive PermEnsemble (tt : list (list TE)) : @TraceEnsemble TE :=
    | perm_ensemble : forall t,
        TaggedPermutation tt t ->
        PermEnsemble tt (snd (split t)).
  End defn.

  Definition PermIlvAll {TE} := @PermEnsemble TE alwaysCommRel.

  Definition PermIlvNonComm `{StateSpace} := @PermEnsemble TE nonCommRel.

  Section transform_ensemble.
    Context `{Hssp : StateSpace} (e1 e2 : list (list TE) -> @TraceEnsemble TE).

    Let te_s (l : list (nat * TE)) := snd (split l).

    Lemma perm_non_comm tt :
      sufficient_replacement_p (PermIlvAll tt) (@PermIlvNonComm _ _ Hssp tt).
    Proof.
      intros t Ht. unfold PermIlvAll in Ht. inversion Ht as [t_tagged Ht']. subst. clear Ht.
      assert (H : exists t', TaggedPermutation nonCommRel tt t' /\
                        Permutation trace_elems_commute (te_s t_tagged) (te_s t')).
      2:{ destruct H as [t'' [Ht'' Hperm'']].
          exists (snd (split t'')). split.
          - now constructor.
          - assumption.
      }
      induction Ht'.
      - exists (concat (tag_traces tt)). split; constructor.
      - destruct a as [a_idx a_te]. destruct b as [b_idx b_te].
        destruct IHHt' as [t'' [Ht'' Hperm'']].
        simpl in H. destruct H as [Hidx Hgarbage]. clear Hgarbage.
    Admitted.
(*

        inversion Ht''; subst.



        destruct (@comm_rel_dec _ nonCommRel a_te b_te) as [Hcomm|Hcomm].
        + exists (l' ++ (b_idx, b_te) :: (a_idx, a_te) :: r'). split.
          * constructor.
            --
          * apply perm_orig.
        + unfold comm_rel, nonCommRel in Hcomm. apply not_not in Hcomm; [..|apply classic].
          exists (l' ++ (a_idx, a_te) :: (b_idx, b_te) :: r'). split.
          * apply Ht''.

      induction Ht'.
      - exists (snd (split (concat (tag_traces tt)))). split; repeat constructor.
      -
        destruct a as [a_idx a_te]. destruct b as [b_idx b_te].
        destruct (@comm_rel_dec _ nonCommRel a_te b_te) as [Hcomm|Hcomm].
        + exists (snd (split (l' ++ (b_idx, b_te) :: (a_idx, a_te) :: r'))). split.
          * constructor. constructor.
            -- simpl. *)

    Lemma sufficient_replacement_with_comm_reduction tt :
      sufficient_replacement_p (e1 tt) (PermEnsemble alwaysCommRel tt) ->
      sufficient_replacement_p (PermEnsemble nonCommRel tt) (e2 tt) ->
      sufficient_replacement_p (e1 tt) (e2 tt).
    Proof.
      intros Hforth Hback.
      eapply sufficient_replacement_p_trans; eauto.
      eapply sufficient_replacement_p_trans; eauto.
      apply perm_non_comm.
    Qed.
  End transform_ensemble.
End PermIlv.

Coercion Fin.of_nat_lt : lt >-> Fin.t.

Definition fin_to_nat {N} (n : Fin.t N) : nat :=
  match Fin.to_nat n with
    exist _ a C => a
  end.

Coercion fin_to_nat : Fin.t >-> nat.

Module VecIlv.
  Open Scope vector_scope.

  Section defn.
    Context `{Hssp : StateSpace} (Hcomm_rel : @te_commut_rel TE).

    Let T := list TE.
    Let TT := list T.

    Definition Traces := Vec.t T.

    Inductive MInt Nelems : forall (start : Fin.t Nelems), Traces Nelems -> @TraceEnsemble TE :=
    | mint_nil : forall i,
        MInt Nelems i (vec_same Nelems []) []
    | mint_cons1 : forall (i j : Fin.t Nelems) rest vec te t,
        i <= j ->
        Vec.nth vec i = rest ->
        MInt Nelems j vec t ->
        MInt Nelems i (Vec.replace vec i (te :: rest)) (te :: t)
    | mint_cons2 : forall (i j : Fin.t Nelems) rest vec te_i te_j t,
        j < i ->
        Vec.nth vec i = rest ->
        comm_rel te_i te_j ->
        MInt Nelems j vec (te_j :: t) ->
        MInt Nelems i (Vec.replace vec i (te_i :: rest)) (te_i :: te_j :: t).

    Definition MInt_ (tt : TT) : @TraceEnsemble TE :=
      fun t => exists i, MInt (length tt) i (Vec.of_list tt) t.
  End defn.

  Module try_using_perm.
    Import PermIlv.

    Section sisyphus.
      Context `{Hssp : StateSpace}.

      Lemma pipe_dream tt : sufficient_replacement_p (PermEnsemble nonCommRel tt) (MInt_ nonCommRel tt).
      Proof.
        intros t Ht.
        inversion Ht as [tt_tagged Ht' Htt_tagged]. subst. clear Ht.
        induction Ht'.
        2:{ destruct IHHt' as [t'' [Ht'' Hperm'']].
            destruct a as [idx1 te1]. destruct b as [idx2 te2].
            simpl in H.
      Abort.
    End sisyphus.
  End try_using_perm.

  Section sisyphus.
    Context `{Hssp : StateSpace}.

    Fixpoint pipe_dream0 N i0 tt_vec t
      (Ht : MInt alwaysCommRel N i0 tt_vec t) {struct Ht} :
      exists t' : list TE,
        (exists i : Fin.t N, MInt nonCommRel N i tt_vec t') /\ Permutation trace_elems_commute t t'.
    Proof.
      destruct Ht as [i
                     |i j rest vec te t Hij Hi Ht
                     |i j rest vec te_i te_j t Hij Hi Hcomm Ht
                     ].
      { exists []. split; [..|now constructor].
        exists i. constructor.
      }
      { apply pipe_dream0 in Ht. destruct Ht as [t' [[k Ht'] Hperm]].
    Admitted.

    Theorem pipe_dream tt : sufficient_replacement_p (MInt_ alwaysCommRel tt) (MInt_ nonCommRel tt).
    Proof.
      intros t Ht.
      destruct Ht as [i0 Ht]. unfold MInt_.
      remember (Vec.of_list tt) as tt_vec.
      now apply pipe_dream0 in Ht.
    Qed.
  End sisyphus.
End VecIlv.

Section multi_interleaving2.
  Section defn.
    Context `{Hssp : StateSpace} (Hcomm_rel : @te_commut_rel TE).

    Definition Traces := @Zip.t TE.

    Let T := list TE.
    Let TT := list T.

    Definition can_skip_to te (from : T) : Prop :=
      match from with
      | [] => True
      | (a :: _) => comm_rel te a
      end.

    Inductive MInt : Traces -> @TraceEnsemble TE :=
    | mint_nil : forall l r te,
        filter Zip.nonempty r = [] ->
        filter Zip.nonempty l = [] ->
        MInt (l, [te], r) [te]
    | mint_right : forall te_l te_r rest l r z' t,
        comm_rel te_l te_r ->
        (l, rest, r) <- z' ->
        MInt z' (te_r :: t) ->
        MInt (l, te_l :: rest, r) (te_l :: te_r :: t)
    | mint_keep : forall te rest l r t,
        MInt (l, rest, r) t ->
        MInt (l, te :: rest, r) (te :: t)
    | mint_left : forall te l r rest z' t,
        z' <- (l, rest, r) ->
        MInt z' t ->
        MInt (l, te :: rest, r) (te :: t).

    Inductive MultiIlv (tt : TT) : @TraceEnsemble TE :=
    | muilv_nil :
        filter Zip.nonempty tt = [] ->
        MultiIlv tt []
    | muilv : forall l te mid r t,
        let z := (l, te :: mid, r) in
        to_list z = tt ->
        Forall (can_skip_to te) l ->
        MInt z t ->
        MultiIlv tt t.
  End defn.

  Global Arguments Traces {_}.
End multi_interleaving2.

Section sanity_check.
  Context `{Hssp : StateSpace} (a b c d e f : TE)
          (Hac_neq : a <> c)
          (Had_neq : a <> d)
          (Hbc_neq : b <> c)
          (Hbd_neq : b <> d)
          (Hac : trace_elems_commute a c)
          (Hbd : trace_elems_commute b d).

  Ltac mint2 :=
    lazymatch goal with
    | |- MInt _ (_, ?a :: ?b :: _, _) (?a :: ?b :: _) =>
      apply mint_keep
    | |- MInt _ (?l, ?a :: ?rest, (?b :: ?r1) :: ?r) (?a :: ?b :: _) =>
      apply mint_right with (z' := (rest :: l, b :: r1, r)); [easy|constructor|idtac]
    | |- MInt _ ((?b :: ?l1) :: ?l, ?a :: ?rest, ?r) (?a :: ?b :: _) =>
      apply mint_left with (z' := (l, b :: l1, rest :: r)); [constructor|idtac]
    | |- _ => constructor || eapply mint_left; eauto
    end.

  Ltac muilv2 :=
    lazymatch goal with
    | |- MultiIlv _ [?A :: ?E; ?R] (?A :: _) =>
      apply muilv with (l := []) (r := [R]) (mid := E) (te := A)
    | |- MultiIlv _ [?L; ?A :: ?E] (?A :: _) =>
      apply muilv with (l := [L]) (r := []) (mid := E) (te := A)
    end; try easy; repeat mint2.

  Goal MultiIlv alwaysCommRel [[a;b]; [c;d]] [a; b; c; d].
  Proof. muilv2. Qed.

  Goal MultiIlv alwaysCommRel [[a;b]; [c;d]] [a; c; b; d].
  Proof. muilv2. Qed.

  Goal MultiIlv alwaysCommRel [[a;b]; [c;d]] [a; c; d; b].
  Proof. muilv2. Qed.

  Goal MultiIlv alwaysCommRel [[a;b]; [c;d]] [c; d; a; b].
  Proof. muilv2. Qed.

  Goal MultiIlv alwaysCommRel [[a;b]; [c;d]] [c; a; d; b].
  Proof. muilv2. Qed.

  Goal MultiIlv alwaysCommRel [[a;b]; [c;d]] [c; a; b; d].
  Proof. muilv2. Qed.

  Goal ~MultiIlv nonCommRel [[a]; [c]] [c; a].
  Proof.
    intros H. inversion_ H.
    destruct l.
    - simpl in H0. inversion_ H0. inversion_ H2.
    - simpl in H0. destruct l0.
      + simpl in H0. inversion_ H0.
        inversion_ H1.
      + simpl in H0. destruct l1; simpl in *.
        * discriminate.
        * repeat rewrite <-app_assoc in H0. simpl in H0.
          admit.
  Abort.

  Goal Permutation trace_elems_commute [a; c; b; d] [a; c; d; b].
  Proof.
    replace [a; c; d; b] with ([a;c] ++ [d; b]) by reflexivity.
    replace [a; c; b; d] with ([a;c] ++ [b; d]) by reflexivity.
    apply perm_shuf.
    - apply perm_orig.
    - assumption.
  Qed.

  Goal ~MultiIlv nonCommRel [[a; b]; [c; d]] [a; c; d; b].
  Proof.
    intros H. destruct H; [discriminate|..]. cbn in H.
    lazymatch goal with
    | [H : rev ?l ++ ?mid :: ?r = ?list |- _ ] =>
      destruct l; simpl in H; inversion H; subst
    end.
  Abort.

  (* Goal forall (P : list TE -> Prop) t, MultiIlv nonCommRel [[a; b]; [c; d]] t -> P t. *)
  (* Proof. *)
  (*   intros P t H. unfold MultiIlv in H. cbn in *. *)
  (*   match goal with *)
  (*   | [H : MInt _ _ _ |- _ ] => inversion H; subst; clear H *)
  (*   end; cbn in *; try discriminate. *)
  (*   2:{ match goal with *)
  (*       | [H: left_of ?z ?z' |- _] => *)
  (*         inversion H; subst; clear H *)
  (*       end. *)
  (*       1:{ inversion H2. *)
  (*           subst te. subst. clear H2. cbn in H0. *)


  (*       2:{ *)
  (*         inversion H. subst. clear H. *)



  (*   inversion_ H; clear H; try discriminate. *)

  (*   2:{ *)

  (*   repeat *)
  (*   1:{ *)
  (* Qed. *)

End sanity_check.


Section uniq.
  Context `{Hssp : StateSpace}.

  Lemma mint_head_eq CR1 CR2 (te : TE) l m r (t t' : list TE) :
    MInt CR1 (l, m, r) (te :: t) ->
    MInt CR2 (l, m, r) t' ->
    exists t'', t' = te :: t''.
  Proof.
    intros H1 H2.
    inversion_ H1; inversion_ H2;
    match goal with
      |- (exists _, te :: ?T = te :: _) => now exists T
    end.
  Qed.

  Lemma mint_head CR (te : TE) l m r (t : list TE) :
    MInt CR (l, m, r) (te :: t) ->
    exists m', m = te :: m'.
  Proof with reflexivity.
    intros H.
    inversion_ H.
    - exists []...
    - exists rest...
    - exists rest...
    - exists rest...
  Qed.

  Lemma Forall_filter_empty {REL te} (l : list (list TE)) :
    filter Zip.nonempty l = [] ->
    Forall (can_skip_to REL te) l.
  Admitted.
  Hint Resolve Forall_filter_empty : slot.

  Lemma filter_nonempty_to_list (l r : list (list TE)) :
    filter Zip.nonempty r = [] ->
    filter Zip.nonempty l = [] ->
    filter Zip.nonempty (to_list (l, [], r)) = [].
  Admitted.
  Hint Resolve filter_nonempty_to_list : slot.

  Let same_payload (z1 z2 : @Traces TE) := to_list z1 = to_list z2.

  Lemma filter_empty_rev {A} P (l : list A) :
    filter P l = [] ->
    filter P (rev l) = [].
  Admitted.
  Hint Resolve filter_empty_rev : slot.

  Ltac split3 := split; [..|split]; [try reflexivity|..|try now constructor].

  Lemma mint_rotate (te1 te2 : TE) l1 l2 r1 r2 mid1 mid2 t :
    same_payload (l1, te1 :: mid1, r1) (l2, te2 :: mid2, r2) ->
    trace_elems_commute te1 te2 ->
    MInt nonCommRel (l1, te1 :: mid1, r2) t ->
    exists t', MInt nonCommRel (l2, te2 :: mid2, r2) t' /\ Permutation trace_elems_commute t t'.
  Admitted.

  Lemma same_payload_nil {REL} l mid r l' mid' r' :
    same_payload (l', mid', r') (l, mid, r) ->
    filter Zip.nonempty r' = [] ->
    filter Zip.nonempty l' = [] ->
    MInt REL (l, mid, r) mid'.
  (* Proof. *)
  (*   intros H Hr' Hl'. *)
  Admitted.

  Fixpoint mint_add l mid r z te t (H : MInt nonCommRel z t) {struct H} :
    same_payload z (l, mid, r) ->
    exists t' z', same_payload (l, te :: mid, r) z' /\
             MInt nonCommRel z' t' /\
             Permutation trace_elems_commute (te :: t) t'.
  Proof with eauto with slot.
    intros Hz.
    inversion H as [l' r' t' Hr Hl
                   |te_l te_r rest l' r' z' t' Hcomm Hz' H'
                   |te' rest l' r' t' H'
                   |te' l' r' rest z' t' Hz' H'
                   ]; clear H; subst.
    3:{ exists (te :: te' :: t'). exists (l', te :: te' :: rest, r'). split3.
        -
  Abort.

  Fixpoint mint_add l mid r z te t (H : MInt nonCommRel z t) {struct H} :
    same_payload z (l, mid, r) ->
    exists t' z', same_payload (l, te :: mid, r) z' /\
             MInt nonCommRel z' t' /\
             Permutation trace_elems_commute (te :: t) t'.
  Proof with eauto with slot.
    intros Hz. apply left_of_dec in Hz.
    destruct Hz as [Hz|[Hz|Hz]].
    { exists (te :: t). exists (l, te :: mid, r). split3.
      subst z. now constructor.
    }
    { exists (te :: t). exists (l, te :: mid, r). split3.
      now apply mint_left with (z' := z).
    }
    destruct t as [|te_l t].
    { inversion_ H. }
    destruct (@comm_rel_dec _ nonCommRel te te_l) as [Hte_te_l|Hte_te_l].
    { exists (te :: te_l :: t). exists (l, te :: mid, r). split3.
      now apply mint_right with (z' := z).
    }
    (* Welcome to the hell proof: *)
    cbn in Hte_te_l. apply not_not in Hte_te_l; [..|apply classic].
    destruct z as [[l' mid'] r'].
    apply mint_head in H as Hmid'. destruct Hmid' as [mid'' Hmid']. subst mid'.
    inversion H as [l_ r_ t' Hr Hl
                   |te_l_ te_r_ rest l_ r_ z' t' Hcomm Hz' H'
                   |te_ rest l_ r_ t' H'
                   |te_ l_ r_ rest z' t' Hz' H'
                   ]; clear H; subst.
    - exists [te_l; te].
      remember (l, mid, r) as z. remember (l', [te_l], r') as z'.
      induction Hz.
      + inversion_ Heqz. inversion_ Heqz'.
        exists ((te :: mid) :: l, [te_l], r'). split3.
        * unfold same_payload, to_list. cbn. now rewrite <-app_assoc.
        * apply mint_left with (z' := (l, (te :: mid), [] :: r')).
          -- constructor.
          -- destruct mid; [..|discriminate].
             apply mint_nil; assumption.
        * replace [te; te_l] with ([] ++ [te; te_l]) by reflexivity.
          replace [te_l; te] with ([] ++ [te_l; te]) by reflexivity.
          apply perm_shuf; [constructor|assumption].
      + give_up.
    - cbn in Hcomm.
      destruct z' as [[l''' mid'''] r'''].
      apply mint_add with (te := te) (l := l''') (mid := mid''') (r := r''') in H'; [..|reflexivity].
      destruct H' as [t''' [z''' [Hz''' [Ht''' Hperm''']]]]. cbn in Hcomm.
      exists (te_l :: t''').
  Admitted.

  Fixpoint mint_sufficient_replacement0 z t (H : MInt alwaysCommRel z t) {struct H} :
    exists t' z', same_payload z z' /\ MInt nonCommRel z' t' /\ Permutation trace_elems_commute t t'.
  Proof with eauto with slot.
    destruct H as [l r t Hr Hl
                  |te_l te_r rest l r z t Hcomm Hz H'
                  |te rest l r t H'
                  |te l r rest z t Hz H'
                  ].
    { exists [t]. exists (l, [t], r). split; [..|split].
      - reflexivity.
      - constructor; assumption.
      - constructor.
    }
    { apply mint_sufficient_replacement0 in H'. destruct H' as [t' [z' [Hz' [Ht' Hperm]]]].
      unfold same_payload in *. apply left_of_to_list in Hz. rewrite <-Hz in Hz'. symmetry in Hz'.
      specialize (mint_add l rest r _ te_l t' Ht' Hz') as [t'' [z'' [Hz'' [Ht'' Hperm'']]]].
      exists t''. exists z''. split3...
      apply permut_cons with (a := te_l) in Hperm. eapply permut_trans...
    }
    { apply mint_sufficient_replacement0 in H'. destruct H' as [t' [z' [Hz' [Ht' Hperm]]]].
      symmetry in Hz'.
      specialize (mint_add l rest r _ te t' Ht' Hz') as [t'' [z'' [Hz'' [Ht'' Hperm'']]]].
      exists t''. exists z''. split; [..|split]...
      eapply permut_cons in Hperm... eapply permut_trans...
    }
    { apply mint_sufficient_replacement0 in H'. destruct H' as [t' [z' [Hz' [Ht' Hperm]]]].
      apply left_of_to_list in Hz. symmetry in Hz'. unfold same_payload in Hz'. rewrite Hz in Hz'.
      specialize (mint_add l rest r _ te t' Ht' Hz') as [t'' [z'' [Hz'' [Ht'' Hperm'']]]].
      exists t''. exists z''. split; [..|split]...
      eapply permut_cons in Hperm... eapply permut_trans...
    }
  Qed.

  Lemma mint_to_muilv z t :
    MInt nonCommRel z t ->
    exists t', MultiIlv nonCommRel (to_list z) t' /\ Permutation trace_elems_commute t t'.
  Admitted.

  Theorem mint_sufficient_replacement tt :
    sufficient_replacement_p (MultiIlv alwaysCommRel tt) (MultiIlv nonCommRel tt).
  Proof with eauto with slot.
    intros t_ Ht_.
    inversion Ht_ as [|l0 te0 mid r0 t z Htt Hlr Ht].
    - subst. exists []. split; constructor. assumption.
    - subst tt. subst t_.
      eapply mint_sufficient_replacement0 in Ht. destruct Ht as [t' [z' [Hzz' [Ht' Hperm]]]].
      unfold same_payload in Hzz'. rewrite Hzz'.
      apply mint_to_muilv in Ht'. destruct Ht' as [t'' [Ht'' Hperm'']].
      exists t''. split...
      eapply permut_trans...
  Qed.

  (* TODO:
  Fixpoint ilv_to_mint (t : list TE)
           t1 t2 (Ht : Interleaving t1 t2 t) {struct Ht} :
    MultiIlv alwaysCommRel [t1; t2] t.
  Proof with eauto with slot.
    destruct t1 as [|te1 t1].
    { exists ([[]], t2, []). cbn. split.
      - right. constructor.
      - apply interleaving_nil in Ht. subst.
        now constructor.
    }
    destruct t2 as [|te2 t2].
    { apply interleaving_symm, interleaving_nil in Ht. subst.
      exists ([], te1 :: t1, [[]]). split.
      - now left.
      - now constructor.
    }
    cbn. remember (te1 :: t1) as t1_. remember (te2 :: t2) as t2_.
    destruct Ht as [te t1' t2' t Ht
                   |te t1' t2' t Ht
                   |]; subst; try discriminate.
    - eapply ilv_to_mint in Ht.
      exists ([], te :: t1', [te2 :: t2]). split...
      destruct Ht as [z [[Hz|Hz] Ht]].
      + subst. eapply mint_left; eauto.
      + eapply
      now constructor.
    - eapply ilv_to_mint in Ht...
      apply mint_skip with (z' := ([te1 :: t1], te :: t2', []))...
      constructor...
    - discriminate.
  Qed. *)
End uniq.
