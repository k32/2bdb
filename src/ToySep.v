(** This module contains toy implementation of separation logic *)
Require Coq.Vectors.Fin.
Require Coq.Vectors.Vector.
Module Fin := Coq.Vectors.Fin.
Module Vec := Coq.Vectors.Vector.

Module IOHandler.
  Variable N_actors : nat.

  Definition AID : Set := Fin.t N_actors.

  Inductive HandlerRet {req_t state_t : Type} (req : req_t) {rep_t : req_t -> Set} : Type :=
  | r_return : forall (reply : rep_t req)
                 (state : state_t)
               , HandlerRet req
  | r_stall : HandlerRet req.

  Record t : Type :=
    {
      h_state : Set;
      h_req : Set;
      h_ret : h_req -> Set;
      (* Nondeterministic: *)
      h_initial_state : h_state -> Prop;
      (* Nondeterministic: *)
      h_eval : forall (state : h_state)
                 (aid : AID)
                 (req : h_req)
                 (ret : @HandlerRet h_req h_state req h_ret)
               , Prop;
    }.

  Section Composition.
    Definition compose_state h1 h2 : Set :=
      h_state h1 * h_state h2.

    Definition compose_req h1 h2 : Set :=
      h_req h1 + h_req h2.

    Hint Transparent compose_state.

    Definition compose_ret_t h1 h2 req :=
      match req with
      | inl l => h1.(h_ret) l
      | inr r => h2.(h_ret) r
      end.

    Hint Transparent compose_ret_t.

    Definition compose_initial_state h1 h2 state :=
      h1.(h_initial_state) (fst state) /\ h2.(h_initial_state) (snd state).

    Hint Transparent compose_initial_state.

    Definition ComposeHandlerRet h1 h2 req := @HandlerRet (compose_req h1 h2)
                                                          (compose_state h1 h2)
                                                          req
                                                          (compose_ret_t h1 h2).

    Hint Transparent ComposeHandlerRet.

    Definition compose_eval h1 h2
               (state : compose_state h1 h2)
               (aid : AID)
               req
               (ret : ComposeHandlerRet h1 h2 req) : Prop.
    Admitted.
      (* let (s1, s2) := state in *)
      (* match req with *)
      (* | inl req => h1.(h_eval) s1 aid req ret *)
      (* | inr req => h2.(h_eval) s2 aid req ret *)
      (* end. *)

    Definition compose (h1 h2 : t) :=
      {| h_state := compose_state h1 h2;
         h_req   := compose_req h1 h2;
         h_ret   := fun req => compose_ret_t h1 h2 req;
         h_initial_state := fun state => compose_initial_state h1 h2 state;
         h_eval  := fun state aid io result => compose_eval h1 h2 state aid io result
      |}.
  End Composition.

  Variable H : t.

  CoInductive Actor {T : t} : Type :=
  | a_waiting : forall (pending_io : T.(h_req))
                  (continuation : T.(h_ret) pending_io -> Actor)
                , Actor
  | a_dead : Actor.

  Definition Actors := Vec.t (@Actor H) N_actors.

  Definition Trace := list H.(h_req).

  Record ModelState (T : t) : Type :=
    mkState
      {
        m_actors : Actors;
        m_state  : T.(h_state);
        m_trace  : Trace;
      }.

  (* Local Definition init_actors : Actors. *)
  (*   refine (fix go i := *)
  (*             match i with *)
  (*             | 0 => Vec.nil *)
  (*             | Fin.S i' => Vec.cons (start_actor i) (go i') *)
  (*             end). *)



  (* Inductive model_step (s : ModelState) : ModelState -> Prop := *)
  (* | mod_init : forall s0, H.(h_initial_state) s0 -> *)
  (*                   mkState init_actors s0 []. *)

  Definition exit {T : t} : @Actor T := a_dead.
End IOHandler.

Module ExampleModelDefn.
  Import IOHandler.
  Local Definition state : Set := nat * bool.

  Inductive io :=
  | get : io
  | put : nat -> io
  | lock : io
  | unlock : io
  .

  Local Definition ret_t (io : io) : Set :=
    match io with
    | get => nat
    | _ => True
    end.

  Local Definition eval_f (s0 : state) (aid : AID) (req : io) : @HandlerRet io state req ret_t :=
    match req, s0 with
    | get, (x, _)      => r_return _ x s0
    | put N, (_, l)    => r_return _ I (N, l)
    | lock, (x, false) => r_return _ I (x, true)
    | lock, (x, true)  => r_stall  _
    | unlock, (x, _)   => r_return _ I (x, false)
    end.

  Inductive example_eval (s0 : state) (aid : AID) (req : io) : @HandlerRet io state req ret_t -> Prop :=
  | example_eval1 : example_eval s0 aid req (eval_f s0 aid req).

  Inductive example_initial_state : state -> Prop :=
  | example_initial_state1 : example_initial_state (0, false).

  Local Definition exampleHandler : IOHandler.t :=
    {|
      h_state := state;
      h_req := io;
      h_ret := ret_t;
      h_initial_state := example_initial_state;
      h_eval := example_eval;
    |}.

  Notation "'do' V '<-' I ; C" := (@a_waiting exampleHandler (I) (fun V => C))
                                    (at level 100, C at next level, V ident, right associativity).

  (* Just a demonstration that we can define programs that loop
  indefinitely, as long as they do IO: *)
  Local CoFixpoint infinite_loop (aid : AID) : @Actor exampleHandler :=
    @a_waiting exampleHandler (put 1) (fun ret => infinite_loop aid).

  (* Data race example: *)
  Local Definition counter_race (_ : AID) : @Actor exampleHandler :=
    do v <- get;
    do _ <- put (v + 1);
    exit.  Notation "'do' I; C" := (do _ <- I ; C)
                            (at level 100, C at next level, right associativity).

  (* Fixed example: *)
  Local Definition counter_correct (_ : AID) : @Actor exampleHandler :=
    do _ <- lock;
    do v <- get;
    do _ <- put (v + 1);
    do _ <- unlock;
    exit.

End ExampleModelDefn.
