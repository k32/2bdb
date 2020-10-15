From Coq Require Import
     Ensembles.

From LibTx Require Export
     SLOT.EventTrace
     SLOT.Hoare.

Class Handler {PID Req Ret} : Type :=
  mkHandler
    { h_state : Type;
      h_chain_rule : h_state -> h_state -> @TraceElem PID Req Ret -> Prop;
    }.

(** * Helper functions for getting request and result types of the handler
    ** In case handler does not depend on PID: *)
Definition get_handler_req {Req Ret} `(_ : forall PID, @Handler PID Req Ret) := Req.
Definition get_handler_ret {Req Ret} `(_ : forall PID, @Handler PID Req Ret) := Ret.
(** ** In case it depends on PID: *)
Definition get_handler_req_pid {PID Req Ret} `(_ : @Handler PID Req Ret) := Req.
Definition get_handler_ret_pid {PID Req Ret} `(_ : @Handler PID Req Ret) := Ret.

Global Instance handlerStateSpace `{Handler} : StateSpace h_state TraceElem :=
  {| chain_rule := h_chain_rule |}.

Section ComposeHandlers.
  Context {PID Q_l Q_r R_l R_r}
          (h_l : @Handler PID Q_l R_l)
          (h_r : @Handler PID Q_r R_r).

  Let S_l := @h_state _ _ _ h_l.
  Let S_r := @h_state _ _ _ h_r.

  Definition compose_state : Type := S_l * S_r.
  Let S := compose_state.

  Definition compose_req : Type := Q_l + Q_r.
  Let Q := compose_req.

  Definition compose_ret (req : Q) :=
    match req with
    | inl l => R_l l
    | inr r => R_r r
    end.

  Definition ComposeTE := @TraceElem PID Q compose_ret.
  Let TE := ComposeTE.

  Inductive compose_chain_rule_i : S -> S -> TE -> Prop :=
  | cmpe_left :
      forall (l l' : S_l) (r : S_r) pid req ret,
        h_chain_rule l l' (trace_elem pid req ret) ->
        compose_chain_rule_i (l, r) (l', r) (trace_elem pid (inl req) ret)
  | cmpe_right :
      forall (r r' : S_r) (l : S_l) pid req ret,
        h_chain_rule r r' (trace_elem pid req ret) ->
        compose_chain_rule_i (l, r) (l, r') (trace_elem pid (inr req) ret).

  Definition compose_chain_rule (s s' : S) (te : TE) : Prop.
    destruct te as [pid req ret].
    destruct s as [l r].
    destruct s' as [l' r'].
    remember req as req0.
    destruct req;
      [ refine (r = r' /\ h_chain_rule l l' _)
      | refine (l = l' /\ h_chain_rule r r' _)
      ];
      apply trace_elem with (te_req := q);
      try apply pid;
      subst;
      unfold compose_ret in ret; easy.
  Defined.

  Inductive ComposeChainRule s s' te :=
  | h_cr_par : compose_chain_rule s s' te ->
               ComposeChainRule s s' te.

  Global Instance compose : @Handler PID Q compose_ret :=
    {| h_state         := compose_state;
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

  Lemma compose_comm pid1 pid2 req1 req2 ret1 ret2 :
      trace_elems_commute (pid1 @ ret1 <~ inl req1)
                          (pid2 @ ret2 <~ inr req2).
  Proof with repeat constructor; auto.
    intros [s_l s_r] [s_l' s_r'].
    split; intros H;
    inversion_ H; inversion_ H5; inversion_ H7;
    destruct s'; simpl in *; destruct H3; destruct H4; simpl in *; firstorder; subst.
    - forward (s_l, s_r')...
      forward (s_l', s_r')...
    - forward (s_l', s_r)...
      forward (s_l', s_r')...
  Qed.

  Definition lift_l (prop : S_l -> Prop) : compose_state -> Prop :=
    fun s => match s with
            (s_l, _) => prop s_l
          end.

  Definition lift_r (prop : S_r -> Prop) : compose_state -> Prop :=
    fun s => match s with
            (_, s_r) => prop s_r
          end.

  Lemma lift_l_local : forall (prop : S_l -> Prop),
      @Local _ _ handlerStateSpace te_subset_l (lift_l prop).
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
      @Local _ _ handlerStateSpace te_subset_r (lift_r prop).
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

  Lemma local_l_chain_rule : @ChainRuleLocality _ _ handlerStateSpace te_subset_l.
  Proof with auto with slot; firstorder.
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
    - forward (l, r')...
      forward (l', r')...
    - forward (l', r)...
      forward (l', r')...
  Qed.

  Lemma local_r_chain_rule : @ChainRuleLocality _ _ handlerStateSpace te_subset_r.
  Proof with auto with slot; firstorder.
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
    - forward (l', r)...
      forward (l', r')...
    - forward (l, r')...
      forward (l', r')...
  Qed.
End ComposeHandlers.

Infix "<+>" := (compose)(at level 100).

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
  lazymatch type of Hcr with
  | ComposeChainRule ?Hl ?Hr ?s ?s' ?te =>
    repeat unfold_compose_handler Hcr s s'
  (* TODO: figure out how to move this tactic to Handlers.Mutable where
     it belongs: *)
  | ?s = ?s' /\ ?ret = ?ret' =>
    let Hs := fresh "Hs" in
    let Hret := fresh "Hret" in
    destruct Hcr as [Hret Hs];
    try (rewrite Hret in *; clear Hret);
    try (rewrite Hs in *; clear Hs);
    try clear Hcr
  end.

Create HintDb handlers.

Ltac trace_step f :=
  long_step f (fun H => handler_step H; auto with handlers).

Tactic Notation "unfold_trace_deep" ident(f) := unfold_trace f (fun x => inversion x); subst.

Ltac decompose_state :=
  repeat match goal with
           [H : compose_state _ _ |- _ ] =>
           let l := fresh "s_l" in
           let r := fresh "s_r" in
           destruct H as [l r]; simpl in l,r
         end.

Hint Transparent compose_state.

Global Arguments h_state {_} {_} {_}.
Global Arguments h_chain_rule {_} {_} {_}.

(** Warning: [lift] tactic will emit arbitrary crap when there are
multiple handlers of the same type combined, so avoid using it this
way *)
Ltac lift X :=
 match goal with
   |- ?top =>
   match eval cbv in top with
   | _ => exact X
   | (?a + ?b)%type =>
     (apply (@inl a b) + apply (@inr a b)); lift X
   end
 end.

Tactic Notation "lift" constr(X) := lift X.
