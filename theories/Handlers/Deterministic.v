(** * Generic total deterministic IO handler *)
From LibTx Require Import
     SLOT.EventTrace
     SLOT.Handler.

From Coq Require Import
     List.

Import ListNotations.

Section defs.
  Context (PID S req_t : Set)
          (ret_t : req_t -> Set)
          (initial_state : S -> Prop).

  Definition ctx := mkCtx PID req_t ret_t.
  Let TE := @TraceElem ctx.

  Variable chain_rule : forall (pid : PID) (s : S) (req : req_t), S * ret_t req.

  Definition det_chain_rule (s s' : S) (te : TE) : Prop :=
    match te with
    | trace_elem _ pid req ret =>
      match chain_rule pid s req with
      | (s'_, ret_) => s' = s'_ /\ ret = ret_
      end
    end.

  Definition mkHandler : t :=
    {|
      h_state := S;
      h_req := req_t;
      h_chain_rule := det_chain_rule;
    |}.
End defs.

From Coq Require
     Classes.EquivDec
     Arith.Peano_dec.

Ltac elim_det H :=
  match type of H with
  | ?s = ?s' /\ ?ret = ?ret' =>
    let Hs := fresh "Hs" in
    let Hret := fresh "Hret" in
    destruct H as [Hret Hs];
    subst s; subst ret;
    clear H
  end.

Module Var.
  Section defs.
    Context {PID T : Set}.

    Inductive req_t : Set :=
    | read : req_t
    | write : T -> req_t.

    Definition ret_t req : Set :=
      match req with
      | read => T
      | write _ => True
      end.

    Definition step (_ : PID) s req : T * ret_t req :=
      match req with
      | read => (s, s)
      | write new => (new, I)
      end.

    Definition t := mkHandler PID T req_t ret_t step.
  End defs.
End Var.

Module AtomicVar.
  Import EquivDec Peano_dec.

  Section defs.
    Context {PID T : Set} `{@EqDec T eq eq_equivalence}.

    Inductive req_t : Set :=
    | read : req_t
    | write : T -> req_t
    | CAS : T -> T -> req_t.

    Definition ret_t req : Set :=
      match req with
      | read => T
      | write _ => True
      | CAS _ _ => bool
      end.

    Definition step (_ : PID) s req : T * ret_t req :=
      match req with
      | read => (s, s)
      | write new => (new, I)
      | CAS old new =>
        if equiv_dec old s then
          (new, true)
        else
          (s, false)
      end.

    Definition t := mkHandler PID T req_t ret_t step.
  End defs.

  Section tests.
    Let S := nat.
    Let PID := True.
    Let Handler := @t PID S eq_nat_dec.
    Let ctx := hToCtx Handler.
    Notation "pid '@' ret '<~' req" := (trace_elem ctx pid req ret).

    Goal forall (r1 r2 : S), r1 <> r2 ->
                        {{fun _ => True}} [I @ r1 <~ read; I @ r2 <~ read] {{fun s => False}}.
    Proof.
      intros. unfold_ht.
      repeat trace_step Hls.
    Qed.
  End tests.
End AtomicVar.

From LibTx Require
     EqDec
     Storage.

Module KV.
  Import Storage EqDec.

  Section defn.
    (** Parameters:
    - [PID] type of process id
    - [K] type of keys
    - [V] type of values
    - [S] intance of storage container that should implement [Storage] interface
    *)
    Context {PID K V : Set} {S : Set} `{HStore : @Storage K V S} `{HKeq_dec : EqDec K}.

    (** ** Syscall types: *)
    Inductive req_t :=
    | read : K -> req_t
    | delete : K -> req_t
    | write : K -> V -> req_t
    | snapshot : req_t.

    (** *** Syscall return types: *)
    Definition ret_t (req : req_t) : Set :=
      match req with
      | read _ => option V
      | delete _ => True
      | write _ _ => True
      | snapshot => S
      end.

    Let ctx := mkCtx PID req_t ret_t.
    Let TE := @TraceElem ctx.

    Definition step (_ : PID) (s : S) (req : req_t) : S * ret_t req :=
      match req with
      | read k => (s, get k s)
      | write k v => (put k v s, I)
      | delete k => (Storage.delete k s, I)
      | snapshot => (s, s)
      end.

    Definition t := mkHandler PID S req_t ret_t step.
  End defn.

  (** * Properties *)
  Section Properties.
    Context {PID K V : Set} {S : Set} `{HStore : @Storage K V S} `{HKeq_dec : EqDec K}
            {init_state : S -> Prop}.

    Let ctx := mkCtx PID (@req_t K V) (@ret_t K V S).
    Let TE := @TraceElem ctx.

    Notation "pid '@' ret '<~' req" := (@trace_elem ctx pid req ret).

    (** Two read syscalls always commute: *)
    Lemma kv_rr_comm : forall p1 p2 k1 k2 v1 v2,
        @trace_elems_commute_h _ t (p1 @ v1 <~ read k1) (p2 @ v2 <~ read k2).
    Proof.
      split; intros;
      repeat trace_step H; subst;
      repeat forward s';
      now constructor.
    Qed.

    (** Read and snapshot syscalls always commute: *)
    Lemma kv_rs_comm : forall p1 p2 k v s,
        @trace_elems_commute_h _ t (p1 @ v <~ read k) (p2 @ s <~ snapshot).
    Proof.
      split; intros;
      repeat trace_step H; subst;
      repeat forward s';
      repeat constructor.
    Qed.

    Lemma kv_read_get : forall pid (s : h_state t) k v,
        s ~[pid @ v <~ read k]~> s ->
        v = get k s.
    Proof.
      intros.
      cbn in H.
      destruct H.
      now subst.
    Qed.

    (** Read and write syscalls commute when performed on different keys: *)
    Lemma kv_rw_comm : forall p1 p2 k1 k2 v1 v2,
        k1 <> k2 ->
        @trace_elems_commute_h _ t (p1 @ v1 <~ read k1) (p2 @ I <~ write k2 v2).
    Proof with firstorder.
      split; intros; repeat trace_step H0.
      - forward (put k2 v2 s)...
        forward (put k2 v2 s)...
        now apply distinct.
      - forward s...
        + symmetry. now apply distinct.
        + forward (put k2 v2 s)...
    Qed.

    (** Read and delete syscalls commute when performed on different keys: *)
    Lemma kv_rd_comm : forall p1 p2 k1 k2 v1,
        k1 <> k2 ->
        @trace_elems_commute_h _ t (p1 @ v1 <~ read k1) (p2 @ I <~ delete k2).
    Proof with firstorder.
      split; intros; repeat trace_step H0.
      - forward (Storage.delete k2 s)...
        forward (Storage.delete k2 s)...
        now apply delete_distinct.
      - forward s...
        + symmetry. now apply delete_distinct.
        + forward (Storage.delete k2 s)...
    Qed.

    (** Write syscalls on different keys generally _don't_ commute! *)
    Example kv_ww_comm : forall p1 p2 k1 k2 v1 v2,
        k1 <> k2 ->
        @trace_elems_commute_h _ t (p1 @ I <~ write k1 v1) (p2 @ I <~ write k2 v2).
    Abort.
  End Properties.
End KV.

Module History.
  Section defs.
    Context {PID Event : Set}.

    Definition State : Set := list Event.

    Definition req_t := PID -> Event.

    Definition step (pid : PID) (s : State) (req : req_t) := (req pid :: s, I).

    Definition t := mkHandler PID State req_t (fun _ => True) step.
  End defs.
End History.
