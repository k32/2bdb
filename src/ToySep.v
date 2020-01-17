(** This module contains a minimalistic implementation of separation logic *)
From Coq Require Import
     List
     Omega.

From Containers Require Import
     Maps.

Import List.ListNotations.

From QuickChick Require Import
     QuickChick.

Section IOHandler.
  Variable AID : Set.
  Context {AID_ord : OrderedType AID}.

  Inductive HandlerRet {req_t state_t : Type} (req : req_t) {rep_t : req_t -> Set} : Type :=
  | r_return : forall (reply : rep_t req)
                 (state' : state_t)
    , HandlerRet req
  | r_stall : HandlerRet req.

  Notation "'Nondeterministic' a" := ((a) -> Prop) (at level 200).

  Record t : Type :=
    {
      h_state         : Type;
      h_req           : Set;
      h_ret           : h_req -> Set;
      h_initial_state : Nondeterministic h_state;
      h_eval          : forall (state : h_state)
                          (aid : AID)
                          (req : h_req),
                        Nondeterministic @HandlerRet h_req h_state req h_ret;
    }.

  CoInductive Actor {T : t} : Type :=
  | a_sync1 : forall (pending_req : T.(h_req))
                (continuation : T.(h_ret) pending_req -> Actor)
              , Actor
  | a_sync2 : forall (req : T.(h_req))
                (pending_rep : T.(h_ret) req)
                (continuation : T.(h_ret) req -> Actor)
              , Actor
  | a_dead : Actor.

  Definition Actors {H : t} := Map[AID, (@Actor H)].

  Definition Trace {H : t} := list H.(h_req).

  Record ModelState {H : t} : Type :=
    mkState
      {
        m_actors : @Actors H;
        m_state  : H.(h_state);
        m_trace  : @Trace H;
      }.

  (* TODO: Update trace! *)
  Definition eval_sync {H : t} (aid : AID) (ms : ModelState) (ms' : ModelState) : Prop :=
    match ms with
      {| m_state := s; m_actors := aa; m_trace := t |} =>
      match find aid aa with
      | None =>
        ms = ms'

      | Some a_dead =>
        ms = ms'

      | Some (a_sync1 req cont) =>
        forall ret : @HandlerRet H.(h_req) H.(h_state) req H.(h_ret),
          H.(h_eval) s aid req ret ->
          match ret with
          | r_stall _         => ms = ms'
          | r_return _ rep s' => let a' := a_sync2 req rep cont in
                                let aa' := add aid a' aa in
                                ms' = mkState H aa' s' t
          end

      | Some (a_sync2 req ret cont) =>
          let a' := cont ret in
          ms' = mkState H (add aid a' aa) s t
      end
    end.

  (** Define all schedulings of the system *)
  Inductive Schedulings {H : t} initial_actors : ModelState -> Prop :=
  | model_init : forall s0,
      H.(h_initial_state) s0 ->
      Schedulings initial_actors {| m_actors := initial_actors;
                                    m_state  := s0;
                                    m_trace  := nil;
                                 |}

  | sync_step : forall (aid : AID) (ms : ModelState),
      forall ms', Schedulings initial_actors ms ->
             eval_sync aid ms ms' ->
             Schedulings initial_actors ms'.

  Definition exit {T : t} : @Actor T := a_dead.

  Definition compose_state h1 h2 : Type :=
    h_state h1 * h_state h2.

  Definition compose_req h1 h2 : Set :=
    h_req h1 + h_req h2.

  Hint Transparent compose_state.

  Definition compose_initial_state h1 h2 state :=
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
End IOHandler.

Arguments compose {_}.
Arguments h_state {_}.
Arguments h_req {_}.
Arguments h_ret {_}.
Arguments h_initial_state {_}.
Arguments h_eval {_}.
Arguments Actor {_} {_}.
Arguments a_sync1 {_} {_}.
Arguments exit {_} {_}.

Module Mutable.
  Inductive req_t {T : Set} :=
  | get : req_t
  | put : T -> req_t.

  Section defs.
  Variables AID T : Set.

  Local Definition ret_t (req : @req_t T) : Set :=
    match req with
    | get => T
    | _   => True
    end.

  Local Definition eval_f (s0 : T) (aid : AID) (req : req_t) : @HandlerRet req_t T req ret_t :=
    match req with
    | get   => r_return _ s0 s0
    | put x => r_return _ I x
    end.

  Inductive example_initial_state : T -> Prop :=
  | example_initial_state1 : forall (x : T), example_initial_state x.

  Definition t : (t AID) :=
    {|
      h_state := T;
      h_req := req_t;
      h_initial_state := example_initial_state;
      h_eval := fun s0 aid req ret => ret = eval_f s0 aid req;
    |}.
  End defs.
End Mutable.

Module Mutex.
  Inductive req_t :=
  | grab    : req_t
  | release : req_t.

  Local Definition ret_t (_ : req_t) : Set := True.

  Section defs.
  Variable AID : Set.

  Local Definition state_t : Type := option AID.

  Local Definition eval_f (s0 : state_t) (aid : AID) (req : req_t) : @HandlerRet req_t state_t req ret_t :=
    match req, s0 with
    | grab, None   => r_return _ I (Some aid)
    | grab, Some _ => r_stall _
    | release, _   => r_return _ I None
    end.

  Definition t : (t AID) :=
    {|
      h_state := state_t;
      h_req := req_t;
      h_initial_state := fun s0 => s0 = None;
      h_eval := fun s0 aid req ret => ret = eval_f s0 aid req;
    |}.
  End defs.
End Mutex.


Module ExampleModelDefn.
  Definition AID : Set := nat.

  Local Definition handler := compose (Mutable.t AID nat) (Mutex.t AID).

  Notation "'sync' V '<-' I ; C" := (@a_sync1 AID handler (I) (fun V => C))
                                    (at level 100, C at next level, V ident, right associativity).

  Local Definition put (val : nat) : handler.(h_req) :=
    inl (Mutable.put val).

  Local Definition get : h_req handler :=
    inl (Mutable.get).

  Local Definition grab : h_req handler :=
    inr (Mutex.grab).

  Local Definition release : h_req handler :=
    inr (Mutex.release).

  (* Just a demonstration that we can define programs that loop
  indefinitely, as long as they do IO: *)
  Local CoFixpoint infinite_loop (aid : AID) : Actor :=
    a_sync1 (put 1) (fun ret => infinite_loop aid).

  (* Data race example: *)
  Local Definition counter_race (_ : AID) : Actor :=
    sync v <- get;
    sync _ <- put (v + 1);
    exit.

  (* Fixed example: *)
  Local Definition counter_correct (_ : AID) : Actor :=
    sync _ <- grab;
    sync v <- get;
    sync _ <- put (v + 1);
    sync _ <- release;
    exit.

End ExampleModelDefn.
