Require Import Coq.Lists.List Coq.Arith.Le.
Require Coq.Vectors.Vector.
Import ListNotations.

Module KafkaClients.
Module Fin := Coq.Vectors.Fin.
Module Vec := Coq.Vectors.Vector.

(** Type of data stored in the TLog and the agent state: *)
Variables TLogEntry NodeState : Set.

(** Number of agents in the system: *)
Variable N : nat.
(** Agent callbacks: *)
Variable CanProduce : NodeState -> Prop.
Variable ProduceCallback : NodeState -> TLogEntry * NodeState.
Variable ConsumeCallback : NodeState -> nat -> TLogEntry -> NodeState.

Definition node_states (tlogN : nat) := Vec.t (Fin.t tlogN * NodeState) N.

Definition world (tlogN : nat) : Set := Vec.t TLogEntry tlogN * node_states tlogN.

Definition get_agent {tlogN} (n : Fin.t N) (w : world tlogN) : (Fin.t tlogN * NodeState) :=
  let (_, S) := w in Vec.nth S n.

Definition get_state {tlogN} (n : Fin.t N) (w : world tlogN) : NodeState :=
  let (_, s) := get_agent n w in s.

Definition get_offset {tlogN} (n : Fin.t N) (w : world tlogN) : Fin.t tlogN :=
  let (o, _) := get_agent n w in o.

Definition can_produce {tlogN} (n : Fin.t N) (w : world tlogN) : Prop :=
  let s := get_state n w in
  CanProduce s.

Definition do_produce {tlogN} (n : Fin.t N) (w : world tlogN) : world (S tlogN) :=
  let (tlog, S) := w in
  let (offset, s) := Vec.nth S n in
  let (a, s') := ProduceCallback s in
  (Vec.shiftin a tlog, Vec.replace S n (offset, s')).

Definition can_consume (tlogN : nat) (n : Fin.t N) (w : world tlogN) : Prop :=
  let (tlog, S) := w in
  let (offset, _) := Vec.nth S n in
  let tlogN := length tlog in
  le offset tlogN.

Definition do_consume (n : Fin.t N) (w : world) : world :=
  let (tlog, S) := w in
  let (offset, s) := Vec.nth S n in
  let s' := ConsumeCallback s offset (nth_ offset list) in
  Vec.replace S n (S offset, s').

CoInductive game : world -> Set :=
| Produce : forall (n : Fin.t N) (w : world),
    can_produce n w ->
    game w ->
    game (do_produce n w)
| Consume : forall (n : Fin.t N) (w : world),
    can_consume n w ->
    game w ->
    game (do_consume n w).

Lemma game1_log_lt_N : forall N l (g : game1 N l),
    Forall (fun n => lt n N) l.
Proof.
  intros.
  induction l.
  - apply Forall_nil.
  - apply Forall_cons.
