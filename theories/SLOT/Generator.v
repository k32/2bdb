(** * Lazy definition of Ensemble
 *)

From Coq Require Import
     Program.Basics
     List.

Import ListNotations.

From LibTx Require Import
     Misc
     EventTrace
     Permutation
     SLOT.Hoare
     SLOT.Ensemble.

Section defn.
  Context `{Hssp : StateSpace}.

  Class Generator (A : Type) :=
    { next : A -> option (TE * A) -> Prop
    }.

  Section unfold.
    Context {G} `{Generator G}.

    Inductive UnfoldsTo (g : G) : list TE -> Prop :=
    | gen_unf_nil :
        (next g) None ->
        UnfoldsTo g []
    | gen_unf_cons : forall te g' l,
        (next g) (Some (te, g')) ->
        UnfoldsTo g' l ->
        UnfoldsTo g (te :: l).
  End unfold.

  Global Instance listGenerator : Generator (list TE) :=
    {| next l :=
         match l with
         | [] => eq None
         | a :: l => eq (Some (a, l))
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
        specialize (IHl l0 H1).
        subst.
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
    Context {G1 G2} `{Generator G1} `{Generator G2}.

    Inductive ParallelGen :=
    | gen_parallel : G1 -> G2 -> ParallelGen.

    Inductive ParallelGenerator (g1 : G1) (g2 : G2) : option (TE * ParallelGen) -> Prop :=
    | gen_par_nil :
        (next g1) None ->
        (next g2) None ->
        ParallelGenerator g1 g2 None
    | gen_par_l : forall te g1',
        (next g1) (Some (te, g1')) ->
        ParallelGenerator g1 g2 (Some (te, gen_parallel g1' g2))
    | gen_par_r : forall te g2',
        (next g2) (Some (te, g2')) ->
        ParallelGenerator g1 g2 (Some (te, gen_parallel g1 g2')).

    Global Instance parallelGenerator : Generator ParallelGen :=
      {| next gen :=
           match gen with
           | gen_parallel g1 g2 => ParallelGenerator g1 g2
           end
      |}.
  End parallel.
End defn.
