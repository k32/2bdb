From Coq Require Import
     Ensembles.

From LibTx Require Export
     SLOT.EventTrace
     SLOT.Hoare.

Section IOHandler.
  Context {PID : Set}.

  Local Notation "'Nondeterministic' a" := ((a) -> Prop) (at level 200).

  Record t : Type :=
    {
      h_state         : Set;
      h_req           : Set;
      h_ret           : h_req -> Set;
      h_initial_state : Nondeterministic h_state;
      h_chain_rule    : h_state -> h_state -> @TraceElem (mkCtx PID h_req h_ret) -> Prop
    }.

  Definition hToCtx (h : t) := mkCtx PID h.(h_req) h.(h_ret).
End IOHandler.

Section Hoare.
  (* Here we specialize definitions from Hoare module *)
  Context {PID : Set} {H : @t PID}.

  Let S := h_state H.
  Let ctx := hToCtx H.
  Let TE := @TraceElem ctx.

  Global Instance handlerStateSpace : StateSpace S TE :=
    {| chain_rule := h_chain_rule H |}.

  Definition HoareTripleH (pre : S -> Prop) (trace : @Trace ctx) (post : S -> Prop) :=
    @HoareTriple S TraceElem _ pre trace post.

  Definition Local := @Local S TE _.

  Definition ChainRuleLocality := @ChainRuleLocality S TE _.

  Definition PossibleTrace := @PossibleTrace S TE _.

  Definition trace_elems_commute_h (te1 te2 : TE) :=
    forall s s',
      @LongStep S TE _ s [te1; te2] s' <-> LongStep s [te2; te1] s'.
End Hoare.

Section ComposeHandlers.
  Context {PID : Set} (h_l h_r : @t PID).

  Let S_l := h_state h_l.
  Let S_r := h_state h_r.
  Let Q_l := h_req h_l.
  Let Q_r := h_req h_r.

  Definition compose_state : Set := S_l * S_r.
  Let S := compose_state.

  Definition compose_req : Set := Q_l + Q_r.
  Let Q := compose_req.

  Definition compose_initial_state state :=
    h_l.(h_initial_state) (fst state) /\ h_r.(h_initial_state) (snd state).

  Hint Transparent compose_initial_state.

  Definition compose_ret (req : Q) : Set :=
    match req with
    | inl l => h_l.(h_ret) l
    | inr r => h_r.(h_ret) r
    end.

  Let ctx := mkCtx PID Q compose_ret.
  Let TE := @TraceElem ctx.

  Inductive compose_chain_rule_i : S -> S -> TE -> Prop :=
  | cmpe_left :
      forall (l l' : S_l) (r : S_r) pid req ret,
        h_chain_rule h_l l l' (trace_elem _ pid req ret) ->
        compose_chain_rule_i (l, r) (l', r) (trace_elem ctx pid (inl req) ret)
  | cmpe_right :
      forall (r r' : S_r) (l : S_l) pid req ret,
        h_chain_rule h_r r r' (trace_elem _ pid req ret) ->
        compose_chain_rule_i (l, r) (l, r') (trace_elem ctx pid (inr req) ret).

  Definition compose_chain_rule (s s' : S) (te : TE) : Prop.
    destruct te as [pid req ret].
    destruct s as [l r].
    destruct s' as [l' r'].
    remember req as req0.
    destruct req;
      [ refine (r = r' /\ (h_chain_rule h_l) l l' _)
      | refine (l = l' /\ (h_chain_rule h_r) r r' _)
      ];
      apply trace_elem with (te_req := q);
      try apply pid;
      subst;
      unfold compose_ret in ret; easy.
  Defined.

  Inductive ComposeChainRule s s' te :=
  | h_cr_par : compose_chain_rule s s' te ->
               ComposeChainRule s s' te.

  Definition compose : t :=
    {| h_state         := compose_state;
       h_req           := compose_req;
       h_ret           := compose_ret;
       h_initial_state := compose_initial_state;
       h_chain_rule    := ComposeChainRule;
    |}.

  Definition te_subset_l (te : TE) :=
    match te_req te with
    | inl _ => True
    | inr _ => False
    end.

  Definition te_subset_r (te : TE) :=
    match te_req te with
    | inl _ => False
    | inr _ => True
    end.

  Definition lift_l (prop : S_l -> Prop) : compose_state -> Prop :=
    fun s => match s with
            (s_l, _) => prop s_l
          end.

  Definition lift_r (prop : S_r -> Prop) : compose_state -> Prop :=
    fun s => match s with
            (_, s_r) => prop s_r
          end.

  Lemma lift_l_local : forall (prop : S_l -> Prop),
      @Local PID compose te_subset_l (lift_l prop).
  Proof.
    unfold Local, HoareTriple.
    intros prop te Hin s s' Hte Hpre.
    unfold te_subset_l in Hin.
    destruct te as [pid req ret].
    unfold In in *.
    destruct req as [req|req]; simpl in *.
    - easy.
    - inversion_ Hte.
      unfold compose_chain_rule in H2.
      destruct s, s', s'0.
      firstorder.
      unfold eq_rec_r in *. simpl in *.
      subst.
      inversion_ H4.
  Qed.

  Lemma lift_r_local : forall (prop : S_r -> Prop),
      @Local PID compose te_subset_r (lift_r prop).
  Proof.
    unfold Local, HoareTriple.
    intros prop te Hin s s' Hte Hpre.
    unfold te_subset_r in Hin.
    destruct te as [pid req ret].
    unfold In in *.
    destruct req as [req|req]; simpl in *.
    - inversion_ Hte.
      unfold compose_chain_rule in H2.
      destruct s, s', s'0.
      firstorder.
      unfold eq_rec_r in *. simpl in *.
      subst.
      inversion_ H4.
    - easy.
  Qed.

  Lemma local_l_chain_rule : @ChainRuleLocality PID compose te_subset_l.
  Proof.
    intros te1 te2 Hte1 Hte2 [l r] [l' r'].
    split; intros Hs';
    destruct te1 as [pid1 req1 ret1];
    destruct te2 as [pid2 req2 ret2];
    destruct req1, req2; unfold Ensembles.In, te_subset_l in *; try easy;
      clear Hte1; clear Hte2;
      inversion Hs' as [|[l1 r1] [l2 r2]]; subst; clear Hs';
      inversion H0 as [|[l3 r3] [l4 r4]]; subst; clear H0;
      inversion H2; subst; clear H2;
      unfold compose_chain_rule in *;
      firstorder; subst;
      unfold eq_rec_r in *; simpl in *.
    - apply ls_cons with (s' := (l, r')); firstorder.
      apply ls_cons with (s' := (l', r')); firstorder.
    - apply ls_cons with (s' := (l', r)); firstorder.
      apply ls_cons with (s' := (l', r')); firstorder.
  Qed.

  Lemma local_r_chain_rule : @ChainRuleLocality PID compose te_subset_r.
  Proof.
    intros te1 te2 Hte1 Hte2 [l r] [l' r'].
    split; intros Hs';
    destruct te1 as [pid1 req1 ret1];
    destruct te2 as [pid2 req2 ret2];
    destruct req1, req2; unfold Ensembles.In, te_subset_r in *; try easy;
      clear Hte1; clear Hte2;
      inversion Hs' as [|[l1 r1] [l2 r2]]; subst; clear Hs';
      inversion H0 as [|[l3 r3] [l4 r4]]; subst; clear H0;
      inversion H2; subst; clear H2;
      unfold compose_chain_rule in *;
      firstorder; subst;
      unfold eq_rec_r in *; simpl in *.
    - apply ls_cons with (s' := (l', r)); firstorder.
      apply ls_cons with (s' := (l', r')); firstorder.
    - apply ls_cons with (s' := (l, r')); firstorder.
      apply ls_cons with (s' := (l', r')); firstorder.
  Qed.
End ComposeHandlers.

Ltac destruct_tuple tup a b :=
  let t0 := fresh "t" in
  let eq := fresh "Heq" in
  remember tup as t0 eqn:eq;
  destruct tup as [a b];
  subst t0;
  repeat match goal with
         | [H : (a,b) = (_,_) |- _] => inversion_clear H
         | [H : (_,_) = (a,b) |- _] => inversion_clear H
         end.

Goal forall {A} (a b : A * A), a = b -> fst a = fst b.
  intros.
  destruct_tuple a al ar.
  destruct_tuple b bl br.
  easy.
Qed.

Ltac unfold_compose_handler H s s' :=
  let l := fresh "s__l" in
  let r := fresh "s__r" in
  let l' := fresh "s__l" in
  let r' := fresh "s__r" in
  let Hcr_l := fresh H "_l" in
  let Hcr_r := fresh H "_r" in
  match s with
  | (_, _) => idtac
  | _ => destruct_tuple s l r
  end;
  destruct_tuple s' l' r';
  destruct H as [H];
  simpl in H;
  destruct H as [Hcr_l Hcr_r];
  lazymatch type of Hcr_l with
  | ?x = l' => subst l'
  | ?x = r' => subst r'
  end;
  rename Hcr_r into H;
  idtac.

Ltac handler_step Hcr :=
  lazy in Hcr;
  lazymatch type of Hcr with
  | ComposeChainRule ?Hl ?Hr ?s ?s' ?te =>
    repeat unfold_compose_handler Hcr s s'
  end.

Create HintDb handlers.

Ltac trace_step f :=
  lazy in f;
  lazymatch type of f with
  | LongStep _ [] _ =>
    let s := fresh "s" in
    let Hx := fresh "Hx" in
    let Hy := fresh "Hy" in
    let Hz := fresh "Hz" in
    inversion f as [s Hx Hy Hz|];
    subst s; clear f; clear Hy
  | LongStep _ (_ :: _) _ =>
    let s' := fresh "s" in
    let te := fresh "te" in
    let tail := fresh "tail" in
    let Hcr := fresh "Hcr" in
    let Htl := fresh "Htl" in
    inversion_clear f as [|? s' ? te tail Hcr Htl];
    rename Htl into f;
    repeat handler_step Hcr;
    auto with handlers
  end.

Tactic Notation "unfold_trace_deep" ident(f) := unfold_trace f (fun x => inversion x); subst.

Hint Transparent compose_state.
