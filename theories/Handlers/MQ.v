(** * Distributed message queue

    This IO handler implements a generic "message queue" service
    similar to Apache Kafka. Every published message gets an integer
    offset, and can later be fetched using the offset as a key.
*)
From Coq Require Import
     List.

Import ListNotations.

From LibTx Require Import
     SLOT.EventTrace
     SLOT.Handler.

Section defs.
  (** Parameters:
      - [PID] type of process ids
      - [T] type of message *)
  Context {PID T : Set}.

  Definition Offset := nat.

  (** ** Syscalls:
      This handler implements the following syscalls: *)

  Inductive req_t :=
  (** Nonblocking poll: *)
  | poll : Offset -> req_t
  (** Block execution of the caller until a message with the given
  offset is produced by some other process: *)
  | fetch : Offset -> req_t
  (** Attempt to produce a message. This syscall is
     nondeterministic, with the following possible outcomes:
     - message gets successfully produced, and its offset is
       returned to the caller as [Some Offset]
     - message gets lost in transition, [None] is returned to the
       caller
     - message gets successfully produced, but the response gets
       lost in transition. The caller gets [None] *)
  | produce : T -> req_t.

  Local Definition ret_t (req : req_t) : Set :=
    match req with
    | poll _ => option T
    | fetch _ => T
    | produce _ => option Offset
    end.

  Let TE := @TraceElem PID req_t ret_t.
  Let S := list T.

  (** ** Possible state space transitions: *)
  Inductive mq_chain_rule : S -> S -> TE -> Prop :=
  | mq_poll : forall s pid offset,
      mq_chain_rule s s (pid @ nth_error s offset <~ poll offset)
  | mq_fetch : forall s pid offset val,
      nth_error s offset = Some val ->
      mq_chain_rule s s (pid @ val <~ fetch offset)
  (** Message is successfully produced: *)
  | mq_produce : forall s pid val,
      mq_chain_rule s (val :: s) (pid @ Some (length s) <~ produce val)
  (** Response is lost: *)
  | mq_produce_lost_resp : forall s pid val,
      mq_chain_rule s (val :: s) (pid @ None <~ produce val)
  (** Message is lost: *)
  | mq_produce_lost_msg : forall s pid val,
      mq_chain_rule s s (pid @ None <~ produce val).

  Global Instance MQHandler : @Handler PID req_t ret_t :=
    { h_state := S;
      h_chain_rule := mq_chain_rule;
    }.
End defs.
