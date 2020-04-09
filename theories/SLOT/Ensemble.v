From Coq Require Import
     List.

From LibTx Require Import
     Hoare.

Import ListNotations.

Open Scope hoare_scope.

Reserved Notation "'-{{' a '}}' t '{{' b '}}'" (at level 40).

Section defn.
  Context {S TE} `{StateSpace S TE}.
  Let T := list TE.

  Class Generator (A : Type) :=
    { unfolds_to : A -> T -> Prop;
    }.

  Definition TraceEnsemble := T -> Prop.

  Definition EHoareTriple (pre : S -> Prop) (g : TraceEnsemble) (post : S -> Prop) :=
    forall t, g t ->
         {{ pre }} t {{ post}}.

  Notation "'?{{' a '}}' t '{{' b '}}'" := (EHoareTriple a t b).

  Inductive TraceEnsembleConcat (e1 e2 : TraceEnsemble) : TraceEnsemble :=
  | et_concat : forall t1 t2, e1 t1 -> e2 t2 -> TraceEnsembleConcat e1 e2 (t1 ++ t2).

  Inductive Interleaving : T -> T -> TraceEnsemble :=
  | ilv_cons_l : forall te t1 t2 t,
      Interleaving t1 t2 t ->
      Interleaving (te :: t1) t2 (te :: t)
  | ilv_cons_r : forall te t1 t2 t,
      Interleaving t1 t2 t ->
      Interleaving t1 (te :: t2) (te :: t)
  | ilv_nil_l : forall t2,
      Interleaving [] t2 t2
  | ilv_nil_r : forall t1,
      Interleaving t1 [] t1.

  Inductive Parallel (e1 e2 : TraceEnsemble) : TraceEnsemble :=
  | ilv_par : forall t1 t2 t,
      e1 t1 -> e2 t2 ->
      Interleaving t1 t2 t ->
      Parallel e1 e2 t.
End defn.

Notation "'-{{' a '}}' t '{{' b '}}'" := (EHoareTriple a t b) : hoare_scope.
Infix ">>" := (TraceEnsembleConcat) (at level 100) : hoare_scope.

Infix "|>" := (Parallel) (at level 101) : hoare_scope.

Section props.
  Context {S TE} `{StateSpace S TE}.
  Let T := list TE.

  Lemma e_hoare_concat : forall pre mid post e1 e2,
      -{{pre}} e1 {{mid}} ->
      -{{mid}} e2 {{post}} ->
      -{{pre}} e1 >> e2 {{post}}.
  Proof.
    intros *. intros H1 H2 t Ht.
    destruct Ht.
    apply hoare_concat with (mid0 := mid); auto.
  Qed.

  Lemma e_hoare_par_seq : forall e1 e2 e P Q R,
      -{{P}} e1 |> e {{Q}} ->
      -{{Q}} e2 |> e {{R}} ->
      -{{P}} e1 >> e2 |> e {{R}}.
  Proof.
    intros *. intros H1 H2 t Ht s s' Hss' Hpre.
    destruct Ht as [t1 t2 t Ht1 Ht2 Hint].
  Abort.
End props.
