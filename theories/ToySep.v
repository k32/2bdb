(*** Minimalistic implementation of concurrent separation logic *)
(** This module defines the model of distributed system used in the
rest of the project. Whether you trust the LibTx depends on whether
you trust the below definitions.

* Motivation

Before diving into lengthy description of the model, let me first
motivate a sceptical reader:

** Q: Why not TLA+?

A: ToySep allows to describe nondeterministic parts of the model in a
way very similar to TLA+. But its deterministic part enjoys from using
a full-fledged functional language

- I want to write inductive proofs

- I want to use a more or less traditional functional language

- I want to extract verified programs

- While TLA+ model checker is top notch, its proof checker isn't, by
  far

** Q: Why not %model checker%?

A: Model checkers show why the code _fails_, which is good for
verifying algorithms, but formal proofs show why the code _works_ (via
tree of assumptions), which is good for reasoning about algorithms
and, in particular, predicting the outcome of optimisations. Also
model checkers can't explore the entire state space of a typical
real-life system with unbounded number of actors.

** Q: Why not Verdi?

- Verdi models are low level: think UDP packets and disk IO. ToySep is
  meant to model systems on a much higher level: think Kafka client
  API.

- Nondeterminisic part of Verdi is hardcoded, while ToySep allows user
  to define custom nondeterministic IO handlers.

** Q: Why not disel?

A: disel models are closer to what I need, but implementation itself
is an incomprehensible, undocumetned burp of ssreflect. Proofs are as
useful as their premises: "garbage in - garbage out". Good model
should be well documented and well understood.

** Q: Why not iris/aneris?

A: iris allows user to define semantics of their very own programming
language. ToySep is focused on proving properties of _regular pure
functinal programs_ that do IO from time to time. Hence it defines
actors in regular Gallina language, rather than some DSL, and frees
the user from reinventing basic control flow constructions.

*)
From Coq Require Import
     List
     Omega
     Tactics
     Sets.Ensembles
     Structures.OrdersEx.

Import ListNotations.

From Containers Require Import
     OrderedType
     OrderedTypeEx
     MapInterface
     MapFacts
     MapAVLInstance.

From QuickChick Require Import
     QuickChick.

From LibTx Require Import
     FoldIn.

Reserved Notation "aid '@' req '<~' ret" (at level 30).
Reserved Notation "'{{' a '}}' t '{{' b '}}'" (at level 40).
Reserved Notation "'{{' a '&' b '}}' t '{{' c '&' d '}}'" (at level 10).

Global Arguments Ensembles.In {_}.
Global Arguments Complement {_}.
Global Arguments Ensembles.Disjoint {_}.

Ltac inversion_ a := inversion a; subst; auto.

Section IOHandler.
  Context {AID : Set} `{AID_ord : OrderedType AID}.

  Local Notation "'Nondeterministic' a" := ((a) -> Prop) (at level 200).

  Record TraceElem_ {Req : Set} {Ret : Req -> Set} : Set :=
    trace_elem { te_aid : AID;
                 te_req : Req;
                 te_ret : Ret te_req;
               }.

  Record t : Type :=
    {
      h_state         : Set;
      h_req           : Set;
      h_ret           : h_req -> Set;
      h_initial_state : Nondeterministic h_state;
      h_chain_rule    : h_state -> h_state -> @TraceElem_ h_req h_ret -> Prop
    }.

  Definition TraceElem {h : t} : Set := @TraceElem_ h.(h_req) h.(h_ret).

  Definition Trace {h : t} := list (@TraceElem h).
End IOHandler.

Section Hoare.
  Context {AID : Set} {H : @t AID}.

  Section defn.
    Let TE := @TraceElem AID H.
    Let T := @Trace AID H.

    Context {S : Type} {chain_rule : S -> S -> TE -> Prop}.

    Inductive HoareTriple : (S -> Prop) -> T -> (S -> Prop) -> Prop :=
    | ht_skip :
        forall (p : S -> Prop), {{ p }} [] {{ p }}
    | ht_step :
        forall (pre post : S -> Prop) (s : S) (te : TE) (tail : T),
          {{ fun s' => chain_rule s s' te }} tail {{ post }} ->
          pre s ->
          {{ pre }} (te :: tail) {{ post }}
    where
      "'{{' A '}}' t '{{' B '}}'" := (HoareTriple A t B).

    Lemma hoare_cons : forall pre mid post (te : TE) (tail : T),
        HoareTriple pre [te] mid -> HoareTriple mid tail post ->
        HoareTriple pre (te :: tail) post.
    Proof.
      intros. inversion H0. subst. inversion H5. subst.
      apply ht_step with (s := s); auto.
    Qed.

    Lemma hoare_cons' : forall s te t post,
        {{fun s' : S => chain_rule s s' te}} t {{post}} <->
        {{fun s' => s = s'}} te :: t {{post}}.
    Proof.
      split; intros.
      - apply ht_step with (s := s); easy.
      - inversion_ H0.
    Qed.

    Theorem hoare_concat : forall pre mid post t1 t2,
        HoareTriple pre t1 mid ->
        HoareTriple mid t2 post ->
        HoareTriple pre (t1 ++ t2) post.
    Proof.
      intros.
      induction H0.
      - easy.
      - set (mid' := (fun s' : S => chain_rule s s' te)) in *.
        apply IHHoareTriple in H1.
        rewrite <-app_comm_cons.
        apply hoare_cons with (mid := mid'); auto.
        apply ht_step with (s := s).
        + constructor.
        + assumption.
    Qed.

    Notation "'{{' A '&' B '}}' t '{{' C '&' D '}}'" :=
        ({{ fun s => A s /\ B s }} t {{ fun s => C s /\ D s }}).

    Lemma hoare_and : forall (A B C D : S -> Prop) (t : T),
        {{ A }} t {{ B }} ->
        {{ C }} t {{ D }} ->
        {{ fun s => A s /\ C s }} t {{ fun s => B s /\ D s }}.
    Abort. (* TODO *)

    Definition trace_elems_commute (te1 te2 : TE) :=
      forall P Q, {{P}} [te1; te2] {{Q}} <-> {{P}} [te2; te1] {{Q}}.

    Section ExpandTrace.
      Variable te_subset : Ensemble TE.

      Definition Local (prop : S -> Prop) :=
        forall te,
          ~Ensembles.In te_subset te ->
          {{ prop }} [te] {{ prop }}.

      Example True_is_local : Local (fun s => True).
      Proof.
        unfold Local. intros.
        (* We can't prove it, thankfully! *)
      Abort.

      Definition ChainRuleLocality :=
        forall te s,
          Ensembles.In te_subset te ->
          Local (fun s' => chain_rule s s' te).

      Inductive ExpandedTrace : T -> T -> Prop :=
      | et_nil :
          ExpandedTrace [] []
      | et_match :
          forall te t t',
            Ensembles.In te_subset te ->
            ExpandedTrace t t' ->
            ExpandedTrace (te :: t) (te :: t')
      | et_expand :
          forall te t t',
            ~Ensembles.In te_subset te ->
            ExpandedTrace t t' ->
            ExpandedTrace t (te :: t').

      (* Let's prove that our definition of [ExpandedTrace] covers
      complete trace space; that is, any trace can be split into
      interleaving of members of [te_subset] and the complement
      ensemble: *)
      Theorem extend_trace_complete : forall (t t' : T),
          Forall (fun te => Ensembles.In te_subset te) t' ->
          ExpandedTrace t' t.
      Abort. (* TODO *)

      Lemma expand_trace_nil : forall prop t,
          Local prop ->
          ExpandedTrace [] t ->
          HoareTriple prop t prop.
      Proof.
        intros.
        remember [] as t.
        induction H1.
        - constructor.
        - exfalso.
          inversion Heqt.
        - apply hoare_cons with (mid := prop).
          + apply H0. assumption.
          + apply IHExpandedTrace. assumption.
      Qed.

      Theorem expand_trace_elem : forall pre post te trace',
          Local pre ->
          Local post ->
          ExpandedTrace [te] trace' ->
          {{pre}} [te] {{post}} ->
          {{pre}} trace' {{post}}.
      Proof.
        intros pre post te t' Hl_pre Hl_post Hexp_t' Ht.
        inversion_ Ht.
        inversion_ H3.
        clear Ht. clear H3.
        (* Interesting: we got [Local te_subset (fun s' : S => chain_rule s s' te)] *)
        (*      hypothesis for free *)
        set (mid := (fun s' : S => chain_rule s s' te)) in *.
        remember [te] as t.
        induction Hexp_t'; inversion_ Heqt.
        - apply hoare_cons with (mid := mid).
          + apply ht_step with (s := s); [constructor | easy].
          + apply expand_trace_nil; auto.
        - apply hoare_cons with (mid := pre).
          apply Hl_pre; auto.
          auto.
      Qed.

      (* This theorem is weaker than [expand_trace_elem], as it
      requires an additional assumption [ChainRuleLocality] *)
      Theorem expand_trace : forall pre post trace trace',
          Local pre ->
          Local post ->
          ChainRuleLocality ->
          ExpandedTrace trace trace' ->
          HoareTriple pre trace post ->
          HoareTriple pre trace' post.
      Proof.
        (* First element of [t] is special, as it is proven using
        [Local pre]. We don't want [Local pre] in our main induction
        hypothesis (as [chain_rule] is not guaranteed to be [Local]
        under any conditions), so let's handle very first element of
        [t] separately: *)
        intros pre post t t' Hl_pre Hl_post Hl_h Hexp Ht.
        induction Hexp; auto.
        2: { (* Here we drop irrelevant leading trace elements: *)
          apply hoare_cons with (mid := pre); auto.
        }
        1: {
          inversion_ Ht.
          apply ht_step with (s := s); auto.
          (* Now when we sorted out the situation with the
          precondition, we use induction over [Hexp] to prove the rest
          of the theorem: *)
          clear H6. clear IHHexp. clear Ht.
          generalize dependent s.
          generalize dependent te.
          induction Hexp; intros; auto.
          - inversion_ H4.
            apply hoare_cons with (mid := fun s' => chain_rule s0 s' te).
            apply ht_step with (s := s0); auto. constructor.
            apply IHHexp; auto.
          - specialize (Hl_h te0 s H1).
            apply hoare_cons with (mid := fun s' => chain_rule s s' te0); auto.
        }
      Qed.
    End ExpandTrace.

    Section FrameRule.
      Theorem frame_rule : forall (e1 e2 : Ensemble TE) (P Q R : S -> Prop) (te : TE),
          Ensembles.Disjoint e1 e2 ->
          Local e1 P -> Local e1 Q -> Local e2 R ->
          Ensembles.In e1 te ->
          {{ P }} [te] {{ Q }} ->
          {{ fun s => P s /\ R s }} [te] {{ fun s => Q s /\ R s }}.
        Abort.
    End FrameRule.
  End defn.
End Hoare.

Section PossibleTrace.
  (** Property that tells if a certain sequence of side effects is
      "physically possible". E.g. mutex can't be taken twice, messages
      don't travel backwards in time, memory doesn't change all by
      itself and so on: *)
  Context {AID : Set} {H : @t AID}.

  Definition HoareTripleH := @HoareTriple AID H (h_state H) (h_chain_rule H).

  Definition PossibleTrace t := HoareTripleH (fun _ => True) t (fun _ => True).
End PossibleTrace.

Section ComposeHandlers.
  Context {AID : Set} `{OrderedType AID} (h_l h_r : @t AID).

  Definition compose_state : Set := h_state h_l * h_state h_r.

  Definition compose_req : Set := h_req h_l + h_req h_r.

  Hint Transparent compose_state.

  Definition compose_initial_state state :=
    h_l.(h_initial_state) (fst state) /\ h_r.(h_initial_state) (snd state).

  Hint Transparent compose_initial_state.

  Definition compose_ret (req : compose_req) : Set :=
    match req with
    | inl l => h_l.(h_ret) l
    | inr r => h_r.(h_ret) r
    end.

  Hint Transparent compose_ret.

  Check trace_elem.

  Inductive compose_chain_rule : compose_state ->
                                 compose_state ->
                                 @TraceElem_ AID compose_req compose_ret
                                 -> Prop :=
  | cmpe_left :
      forall (l l' : h_state h_l) (r : h_state h_r)
        (aid : AID) (req : h_req h_l) (ret : (h_ret h_l) req),
        h_chain_rule h_l l l' (trace_elem _ _ aid req ret) ->
        compose_chain_rule (l, r) (l', r) (trace_elem _ _ aid (inl req) ret)
  | cmpe_right :
      forall (r r' : h_state h_r) (l : h_state h_l)
        (aid : AID) (req : h_req h_r) (ret : (h_ret h_r) req),
        h_chain_rule h_r r r' (trace_elem _ _ aid req ret) ->
        compose_chain_rule (l, r) (l, r') (trace_elem _ _ aid (inr req) ret).

  Definition compose : t :=
    {| h_state         := compose_state;
       h_req           := compose_req;
       h_ret           := compose_ret;
       h_initial_state := compose_initial_state;
       h_chain_rule    := compose_chain_rule;
    |}.

  Definition te_subset_l (te : @TraceElem AID compose) :=
    match te_req te with
    | inl _ => True
    | inr _ => False
    end.

  Definition te_subset_r (te : @TraceElem AID compose) :=
    match te_req te with
    | inl _ => False
    | inr _ => True
    end.

  Theorem composed_state_locality_l :
    @ChainRuleLocality AID compose compose_state
                       compose_chain_rule te_subset_l.
  Proof.
    unfold ChainRuleLocality, Local.
    intros [aid1 req1 ret1] [s_l s_r] H1 [aid2 req2 ret2] H2.
    unfold te_subset_l, Ensembles.In in H1, H2.
    destruct req1 as [req1|req1], req2 as [req2|req2]; try contradiction.
    simpl in *.
    assert (s_r' : h_r.(h_state)). admit.
    apply ht_step with (s := (s_l, s_r')).
  Abort.
End ComposeHandlers.

Module Mutable.
  Inductive req_t {T : Set} :=
  | get : req_t
  | put : T -> req_t.

  Section defs.
  Context (AID T : Set) `{AID_ord : OrderedType AID} (initial_state : T -> Prop).

  Local Definition ret_t (req : @req_t T) : Set :=
    match req with
    | get => T
    | _   => True
    end.

  Inductive mut_chain_rule : T -> T -> @TraceElem_ AID req_t ret_t -> Prop :=
  | mut_get : forall s aid,
      mut_chain_rule s s (trace_elem _ _ aid get s)
  | mut_put : forall s val aid,
      mut_chain_rule s val (trace_elem _ _ aid (put val) I).

  Definition t : t :=
    {|
      h_state := T;
      h_req := req_t;
      h_initial_state := initial_state;
      h_chain_rule := mut_chain_rule;
    |}.
  End defs.
End Mutable.

Module Mutex.
  Inductive req_t : Set :=
  | grab    : req_t
  | release : req_t.

  Local Definition ret_t (req : req_t) : Set :=
    match req with
    | grab => True
    | release => bool
    end.

  Section defs.
  Variable AID : Set.

  Definition state_t : Set := option AID.

  Inductive mutex_chain_rule : state_t -> state_t -> @TraceElem_ AID req_t ret_t -> Prop :=
  | mutex_grab : forall aid,
      mutex_chain_rule None (Some aid) (trace_elem _ _ aid grab I)
  | mutex_release_ok : forall aid,
      mutex_chain_rule (Some aid) None (trace_elem _ _ aid release true)
  | mutex_release_fail : forall aid,
      mutex_chain_rule (Some aid) None (trace_elem _ _ aid release false).

  Definition t : t :=
    {|
      h_state         := state_t;
      h_req           := req_t;
      h_initial_state := fun s0 => s0 = None;
      h_chain_rule    := mutex_chain_rule
    |}.

  Local Notation "aid '@' ret '<~' req" := (trace_elem req_t ret_t aid req ret).

  Theorem no_double_grab : forall (a1 a2 : AID),
      ~(@PossibleTrace AID t [ a1 @ I <~ grab;
                               a2 @ I <~ grab
                             ]).
  Proof.
    intros a1 a2 H.
    inversion_ H.
    destruct s.
    - inversion_ H3. inversion H7.
    - simpl in *.
      inversion H3.
      inversion_ H7.
      inversion_ H4. (* TODO: fix this *)
      set (f := fun _:state_t => True) in *.
      assert (nonsense : f (Some a1) = True) by easy.
      rewrite <- H1 in nonsense.
      rewrite <-nonsense in H5.
      inversion H5.
  Qed.
  End defs.
End Mutex.

Section Actor.
  Context {AID : Set} `{AID_ord : OrderedType AID} {H : @t AID}.

  CoInductive Actor : Type :=
  | a_cont : forall (pending_req : H.(h_req))
               (continuation : H.(h_ret) pending_req -> option Actor)
           , Actor.

  Definition Actors := Map[AID, Actor].

  Definition throw (_ : string) : option Actor :=
    None.

  Record ModelState : Type :=
    mkState
      {
        m_actors : Actors;
        m_state  : H.(h_state);
      }.

  Definition perform_io aid (req : h_req H) cont (ret : (h_ret H) req) ms s' :=
    match ms with
      {| m_state := s; m_actors := aa |} =>
      let aa' := match cont ret with
                 | Some a' => add aid a' aa
                 | None    => remove aid aa
                 end in
      mkState aa' s'
    end.

  Definition actor_chain_rule_ (ms : ModelState) (te : TraceElem) (s' : H.(h_state)) : Prop :=
     match te, ms with
     | trace_elem _ _ aid req ret, mkState aa s =>
       {HIn : In aid aa |
        let HReq := match find' aid aa HIn with
                    | a_cont req' _ => req = req'
                    end in
        HReq /\ H.(h_chain_rule) (m_state ms) s' te}
     end.

  Definition actor_chain_rule (ms ms' : ModelState) (te : TraceElem) : Prop :=
    actor_chain_rule_ ms te (m_state ms').

  Definition apply_trace_elem (ms : ModelState) (te : TraceElem) (s' : H.(h_state))
             (Hte : actor_chain_rule_ ms te s') : ModelState.
    destruct te as [aid req ret].
    destruct ms as [aa s].
    destruct Hte as [HIn [Hreq Hs]].
    destruct (find' aid aa HIn) as [req0 cont].
    subst.
    apply (perform_io aid req0 cont ret (mkState aa s) s').
  Defined.

  Definition HoareTripleA :=
    @HoareTriple AID H ModelState actor_chain_rule.

  Definition ReachableState initial_actors (ms : ModelState) : Prop :=
    exists (t : @Trace AID H),
      HoareTripleA (fun ms0 => H.(h_initial_state) (m_state ms0) /\ (m_actors ms0) = initial_actors)
                   t
                   (fun m => ms = m).
End Actor.

Module ExampleModelDefn.
  Definition AID : Set := nat.

  Local Definition handler := compose (Mutable.t AID nat (fun a => a = 0))
                                      (Mutex.t AID).

  Notation "'do' V '<-' I ; C" := (@a_cont AID handler (I) (fun V => Some C))
                                    (at level 100, C at next level, V ident, right associativity).

  Notation "'done' I" := (@a_cont AID handler (I) (fun _ => None))
                           (at level 100, right associativity).

  Local Definition put (val : nat) : handler.(h_req) :=
    inl (Mutable.put val).

  Local Definition get : h_req handler :=
    inl (Mutable.get).

  Local Definition grab : h_req handler :=
    inr (Mutex.grab).

  Local Definition release : h_req handler :=
    inr (Mutex.release).

  (* Just a demonstration how to define a program that loops
  indefinitely, as long as it does IO: *)
  Local CoFixpoint infinite_loop (aid : AID) : Actor :=
    do _ <- put 0;
    infinite_loop aid.

  (* Data race example: *)
  Local Definition counter_race (_ : AID) : Actor :=
    do v <- get;
    done put (v + 1).

  (* Fixed example: *)
  Local Definition counter_correct (_ : AID) : Actor :=
    do _ <- grab;
    do v <- get;
    do _ <- put (v + 1);
    done release.

  Local Definition two_actors := add 0 (counter_race 0) (add 1 (counter_race 1) (empty _) : Map [nat, Actor]).
End ExampleModelDefn.
