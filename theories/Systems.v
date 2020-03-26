From LibTx Require Import
     SLOT
     EqDec
     Storage.

Import SLOT.Handler.

Module KV.
  (** Reliable key-value storage IO handler *)
  Section defn.
    Context {PID K V : Set} {S : Set} `{HStore : @Storage K V S} `{HKeq_dec : EqDec K}.

    Inductive req_t :=
    | get : K -> req_t
    | delete : K -> req_t
    | put : K -> V -> req_t
    | snapshot : req_t.

    Let ret_t (req : req_t) : Set :=
      match req with
      | get _ => option V
      | delete _ => True
      | put _ _ => True
      | snapshot => S
      end.

    Let ctx := mkCtx PID req_t ret_t.
    Let TE := @TraceElem ctx.

    Inductive kv_chain_rule : S -> S -> TE -> Prop :=
    | kv_get : forall pid s k,
        kv_chain_rule s s (trace_elem ctx pid (get k) (Storage.get k s))
    | kv_put : forall pid s k v,
        kv_chain_rule s (Storage.put k v s) (trace_elem ctx pid (put k v) I)
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
End KV.
