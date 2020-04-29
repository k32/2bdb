From LibTx Require Import
     SLOT.Handler
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

  Lemma kv_rr_comm : forall p1 p2 k1 k2 v1 v2,
      @trace_elems_commute_h _ t (p1 @ v1 <~ read k1) (p2 @ v2 <~ read k2).
  Proof.
    split; intros;
      unfold_trace_deep H;
      repeat apply ls_cons with (s' := s4); auto.
  Qed.

  Lemma kv_rs_comm : forall p1 p2 k v s,
      @trace_elems_commute_h _ t (p1 @ v <~ read k) (p2 @ s <~ snapshot).
  Proof.
    split; intros;
      unfold_trace_deep H;
      inversion_ Hcr; inversion_ Hcr0;
      repeat apply ls_cons with (s' := s5); auto.
  Qed.

  Lemma kv_read_get : forall pid (s : h_state t) k v,
      s ~[pid @ v <~ read k]~> s ->
      v = get k s.
  Admitted.
  (* Proof. *)
  (*   intros. *)
  (*   simpl in H. *)
  (*   set (te := pid @ v <~ read k) in *. *)
  (*   remember te as te0. *)
  (*   destruct H; inversion_ Heqte0.     *)
  (*   replace v with (te_ret te) by reflexivity. *)
  (* Abort. *)

  Lemma kv_rw_comm : forall p1 p2 k1 k2 v1 v2,
      k1 <> k2 ->
      @trace_elems_commute_h _ t (p1 @ v1 <~ read k1) (p2 @ I <~ write k2 v2).
  Proof.
    split; intros;
      unfold_trace_deep H0.
    - repeat apply ls_cons with (s' := put k2 v2 s1); auto.
      apply kv_read_get in Hcr.
      replace v1 with (get k1 (put k2 v2 s1)).
      constructor.
      replace v1 with (get k1 s1).
      symmetry; apply distinct; auto.
    - apply ls_cons with (s' := s).
      apply kv_read_get in Hcr0.
      replace v1 with (get k1 s).
      constructor.
      rewrite Hcr0.
      apply distinct; auto.
      apply ls_cons with (s' := put k2 v2 s); auto.
  Qed.
End Properties.
