From LibTx Require Import
     SLOT
     EqDec
     Storage.

(** Reliable key-value storage IO handler *)
(* Record KV : Type := *)
(*   makeKV *)
(*     { key_t : Set; *)
(*       val_t : Set; *)
(*       backend : Set; *)
(*       key_eq_dec : EqDec key_t; *)
(*       store_t : @Storage key_t val_t backend; *)
(*     }.  *)

Section defn.
  Context {PID K V : Set} {S : Set} `{HStore : @Storage K V S} `{HKeq_dec : EqDec K}.

  (* Context {PID : Set} {kv : KV}. *)
  (* Let K := key_t kv. *)
  (* Let V := val_t kv. *)
  (* Let S := backend kv. *)
  (* Let HStore := store_t kv. *)

  Inductive req_t :=
  | read : K -> req_t
  | delete : K -> req_t
  | write : K -> V -> req_t
  | snapshot : req_t.

  Definition ret_t (req : req_t) : Set :=
    match req with
    | read _ => option V
    | delete _ => True
    | write _ _ => True
    | snapshot => S
    end.

  Let ctx := mkCtx PID req_t ret_t.
  Let TE := @TraceElem ctx.

  Inductive kv_chain_rule : S -> S -> TE -> Prop :=
  | kv_read : forall pid s k,
      kv_chain_rule s s (trace_elem ctx pid (read k) (get k s))
  | kv_write : forall pid s k v,
      kv_chain_rule s (put k v s) (trace_elem ctx pid (write k v) I)
  | kv_delete : forall pid s k,
      kv_chain_rule s (Storage.delete k s) (trace_elem ctx pid (delete k) I)
  | kv_snapshot : forall pid s,
      kv_chain_rule s s (trace_elem ctx pid snapshot s).

  Definition t : t :=
    {| h_state := S;
       h_req := req_t;
       h_initial_state := fun x => x = Storage.new;
       h_chain_rule := kv_chain_rule;
    |}.
End defn.

Section Properties.
  Context {PID K V : Set} {S : Set} `{HStore : @Storage K V S} `{HKeq_dec : EqDec K}.

  Let ctx := mkCtx PID (@req_t K V) (@ret_t K V S).
  Let TE := @TraceElem ctx.

  Notation "pid '@' ret '<~' req" := (@trace_elem ctx pid req ret).

  Inductive KvTEComm : TE -> TE -> Prop :=
  | kv_rr_comm : forall p1 p2 k1 k2 v1 v2,
      KvTEComm (p1 @ v1 <~ read k1)
               (p2 @ v2 <~ read k2)
  | kv_rs_comm : forall p1 p2 k v s,
      KvTEComm (p1 @ v <~ read k)
               (p2 @ s <~ snapshot).

  Fail Lemma kv_comm : forall te1 te2, KvTEComm te1 te2 <->
                             @trace_elems_commute S TE _ te1 te2.
End Properties.
