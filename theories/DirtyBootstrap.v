From LibTx Require Import
     Storage
     Handlers.Deterministic
     SLOT.

From Coq Require Import
     List.
Import ListNotations.

Section defn.
  Context K V DB `{@Storage K V DB}.

  (* We have only two processes in the system: [writer] that creates
  local transactions and [agent] that is used to bootstrap the remote
  replica: *)
  Inductive Pid := writer | agent.

  Definition Handler := KV.t Pid DB
                    <+> Log.t Pid (@Wlog_elem K V).

  Section boilerplate.
    Definition req_t := get_handler_req_pid Handler.
    Definition ret_t := get_handler_ret_pid Handler.

    Definition read (k : K) : req_t.
      lift (@KV.read K V k).
    Defined.

    Definition keys : req_t.
      lift (@KV.keys K V).
    Defined.

    Definition write (k : K) (v : V) : req_t.
      lift (KV.write k v).
    Defined.

    Definition delete (k : K) : req_t.
      lift (@KV.delete K V k).
    Defined.

    Definition forward_op (w : @Wlog_elem K V) : req_t.
      lift (fun (_ : Pid) => w).
    Defined.
  End boilerplate.

  Definition wlog_apply (w : @Wlog_elem K V) :=
    match w with
    | wl_write k v => write k v
    | wl_delete k => delete k
    end.

  Let Thread := @Thread req_t ret_t.

  Fixpoint writer_loop (ops : @Wlog K V) : Thread :=
    match ops with
    | [] => t_dead
    | op :: tail =>
      do _ <- wlog_apply op;
      writer_loop tail
    end.

  Fixpoint bootstrap (keys : list K) cont : Thread :=
    match keys with
    | [] => cont I
    | k :: tail =>
      do ret <- read k;
      match ret with
      | Some v =>
        do _ <- forward_op (wl_write k v);
        bootstrap tail cont
      | None =>
        bootstrap tail cont
      end
    end.

  Fixpoint export_wlog (ops : @Wlog K V) cont : Thread :=
    match ops with
    | [] => cont I
    | op :: tail =>
      do _ <- forward_op op;
      export_wlog tail cont
    end.

  Definition exporter (ops : @Wlog K V) : Thread :=
    do kk <- keys;
    call _ <- bootstrap kk;
    call _ <- export_wlog ops;
    t_dead.

  Definition dirty_bootstrapper ops := (ThreadGenerator writer (writer_loop ops))
                                   -|| (ThreadGenerator agent (exporter ops)).
End defn.
