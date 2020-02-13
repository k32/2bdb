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

** Q: Why not <${model checker}>?

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

Global Arguments Ensembles.In {_}.
Global Arguments Complement {_}.

Section IOHandler.
  Context {AID : Set} `{AID_ord : OrderedType AID}.

  Inductive HandlerRet {req_t state_t : Type} (req : req_t) (rep_t : req_t -> Set) : Type :=
  | r_return : forall (reply : rep_t req)
                 (state' : state_t)
    , HandlerRet req rep_t
  | r_stall : HandlerRet req rep_t.

  Local Notation "'Nondeterministic' a" := ((a) -> Prop) (at level 200).

  Record t : Type :=
    {
      h_state         : Set;
      h_req           : Set;
      h_ret           : h_req -> Set;
      h_initial_state : Nondeterministic h_state;
      h_eval          : forall (state : h_state)
                          (aid : AID)
                          (req : h_req),
                        Nondeterministic @HandlerRet h_req h_state req h_ret;
    }.
End IOHandler.

Section Trace.
  Context {AID : Set} {H : @t AID}.

  Record TraceElem : Set :=
    trace_elem { te_aid : AID;
                 te_req : H.(h_req);
                 te_ret : H.(h_ret) te_req;
               }.

  Definition Trace := list TraceElem.

  Definition make_ret (te : TraceElem) (s' : h_state H) : HandlerRet (te_req te) (h_ret H) :=
    match te with
      trace_elem _ req ret => r_return req (h_ret H) ret s'
    end.

  Definition valid_trace_elem (s s' : H.(h_state)) (te : TraceElem) : Prop :=
    match te with
    | trace_elem aid req ret =>
      let hret := r_return req (h_ret H) ret s' in
      h_eval H s aid req hret
    end.

  Inductive ExpandedTrace (trace' : Trace) (prop : Ensemble TraceElem) (trace : Trace) : Prop :=
    (* TODO *)
    .
End Trace.

Section Hoare.
  Context {AID : Set} {H : @t AID}.

  Section defn.
    Let TE := @TraceElem AID H.
    Let T := @Trace AID H.

    Context {S : Type} {chain_rule : S -> S -> TE -> Prop}.

    Inductive HoareTriple (pre post : S -> Prop) : T -> Prop :=
    | ht_nil : forall s,
        pre s ->
        post s ->
        HoareTriple pre post []
    | ht_cons : forall (s : S) (te : TE)
                  (tail : T)
                  (th : HoareTriple (fun s' => chain_rule s s' te) post tail),
        pre s ->
        HoareTriple pre post (te :: tail).

    Definition Local (te_subset : Ensemble TE) (prop : S -> Prop) :=
      forall te,
        ~Ensembles.In te_subset te ->
        HoareTriple prop prop [te].

    Theorem frame_rule : forall pre post te_subset trace trace',
        Local te_subset pre ->
        Local te_subset post ->
        ExpandedTrace trace' (Complement te_subset) trace ->
        HoareTriple pre post trace ->
        HoareTriple pre post trace'.
    Abort. (* TODO *)
  End defn.

  Section PossibleTrace.
    Definition HoareTripleH :=
      @HoareTriple (h_state H) valid_trace_elem.

    (** Property that tells if a certain sequence of side effects is
        "physically possible". E.g. mutex can't be taken twice, messages
        don't travel backwards in time, memory doesn't change all by
        itself and so on: *)
    Definition PossibleTrace := HoareTripleH (fun _ => True) (fun _ => True).
  End PossibleTrace.
End Hoare.

Notation "'{{' a '}}' t '{{' b '}}'" := (HoareTriple a b t) (at level 50).

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

  Definition perform_io aid (req : h_req H) cont (ret : HandlerRet req (h_ret H)) ms :=
    match ms with
      {| m_state := s; m_actors := aa |} =>
      match ret with
      | r_stall _ _         => ms
      | r_return _ _ rep s' =>
        let aa' := match cont rep with
                   | Some a' => add aid a' aa
                   | None    => remove aid aa
                   end in
        mkState aa' s'
      end
    end.

  Definition valid_transition_ (ms : ModelState) (te : TraceElem) (s' : H.(h_state)) : Prop :=
     match te, ms with
     | trace_elem aid req ret, mkState aa s =>
       {HIn : In aid aa |
        let HReq := match find' aid aa HIn with
                    | a_cont req' _ => req = req'
                    end in
        HReq /\ valid_trace_elem (m_state ms) s' te}
     end.

  Definition valid_transition (ms ms' : ModelState) (te : TraceElem) : Prop :=
    valid_transition_ ms te (m_state ms').

  Definition apply_trace_elem (ms : ModelState) (te : TraceElem) (s' : H.(h_state))
             (Hte : valid_transition_ ms te s') : ModelState.
    destruct te as [aid req ret].
    destruct ms as [aa s].
    destruct Hte as [HIn [Hreq Hs]].
    destruct (find' aid aa HIn) as [req0 cont].
    refine (perform_io aid req0 cont _ (mkState aa s)).
    - rewrite <-Hreq.
      apply (r_return _ _ ret s').
  Defined.

  Definition is_reachable (ms ms' : ModelState) (te : @TraceElem AID H) : Prop.
    refine ({Hte : valid_transition ms ms' te | _}).
    set (ms_ := ms).
    set (ms_' := ms').
    (* Peform some initial pattern-matching: *)
    destruct ms as [aa s].
    destruct ms' as [aa' s'].
    set (hret := make_ret te s').
    destruct te as [aid req ret].
    destruct Hte as [HIn [Hreq _]].
    destruct (find' aid aa HIn) as [req' cont].
    symmetry in Hreq. subst.
    (* This is our property: *)
    exact (ms_' = perform_io aid req cont hret ms_).
  Defined.

  Definition HoareTripleA :=
    @HoareTriple AID H ModelState is_reachable.

  Definition ReachableState initial_actors (ms : ModelState) : Prop :=
    exists (t : @Trace AID H),
      HoareTripleA (fun ms0 => H.(h_initial_state) (m_state ms0) /\ (m_actors ms0) = initial_actors)
                   (fun m => ms = m) t.
End Actor.

Section ComposeHandlers.
  Context {AID : Set} `{OrderedType AID}.

  Definition compose_state (h1 h2 : @t AID) : Set :=
    h_state h1 * h_state h2.

  Definition compose_req (h1 h2 : @t AID) : Set :=
    h_req h1 + h_req h2.

  Hint Transparent compose_state.

  Definition compose_initial_state (h1 h2 : @t AID) state :=
    h1.(h_initial_state) (fst state) /\ h2.(h_initial_state) (snd state).

  Hint Transparent compose_initial_state.

  Definition compose_ret_t (h1 h2 : t) (req : compose_req h1 h2) : Set :=
    match req with
    | inl l => h1.(h_ret) l
    | inr r => h2.(h_ret) r
    end.

  Hint Transparent compose_ret_t.

  Definition ComposeHandlerRet h1 h2 req : Type :=
    @HandlerRet (compose_req h1 h2)
                (compose_state h1 h2)
                req
                (compose_ret_t h1 h2).

  Definition compose_eval h1 h2
             (state : compose_state h1 h2)
             (aid : AID)
             req
             (ret : ComposeHandlerRet h1 h2 req) : Prop.
    refine (
        (let (s1, s2) := state in
         match req as req' return (req = req' -> Prop) with
         | inl req' => fun H => h1.(h_eval) s1 aid req' _
         | inr req' => fun H => h2.(h_eval) s2 aid req' _
         end) (eq_refl req));
      subst;
      destruct ret;
      try simpl in reply;
      constructor; assumption.
  Defined.

  Definition compose (h1 h2 : t) : t :=
    {| h_state         := compose_state h1 h2;
       h_req           := compose_req h1 h2;
       h_ret           := compose_ret_t h1 h2;
       h_initial_state := compose_initial_state h1 h2;
       h_eval          := compose_eval h1 h2;
    |}.
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

  Local Definition eval_f (s0 : T) (aid : AID) (req : req_t) : @HandlerRet req_t T req ret_t :=
    match req with
    | get   => r_return _ _ s0 s0
    | put x => r_return _ _ I x
    end.

  Definition t : t :=
    {|
      h_state := T;
      h_req := req_t;
      h_initial_state := initial_state;
      h_eval := fun s0 aid req ret => ret = eval_f s0 aid req;
    |}.
  End defs.
End Mutable.

Module Mutex.
  Inductive req_t : Set :=
  | grab    : req_t
  | release : req_t.

  Local Definition ret_t (_ : req_t) : Set := True.

  Section defs.
  Variable AID : Set.

  Local Definition state_t : Set := option AID.

  Local Definition eval_f (s0 : state_t) (aid : AID) (req : req_t) : @HandlerRet req_t state_t req ret_t :=
    match req, s0 with
    | grab, None   => r_return _ _ I (Some aid)
    | grab, Some _ => r_stall _ _
    | release, _   => r_return _ _ I None
    end.

  Definition t : t :=
    {|
      h_state         := state_t;
      h_req           := req_t;
      h_initial_state := fun s0 => s0 = None;
      h_eval          := fun s0 aid req ret => ret = eval_f s0 aid req;
    |}.

  Local Notation "aid '@' req '<~' ret" := (@trace_elem AID t aid req ret).

  Theorem no_double_grab : forall (a1 a2 : AID),
      ~(PossibleTrace [ a1 @ grab <~ I;
                        a2 @ grab <~ I
                      ]).
  Proof.
    intros a1 a2 H.
    unfold PossibleTrace, HoareTripleH in H.
    inversion H as [|s te tail Htail _]. subst.
    inversion Htail as [|s' te' tail' Htail' Hss']. subst.
    unfold valid_trace_elem, h_eval in *.
    destruct s, s'; simpl in *; inversion Hss'.
    - inversion Htail'. inversion H0.
  Qed.
  End defs.
End Mutex.

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
