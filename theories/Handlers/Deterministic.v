(** * Generic total deterministic IO handler *)
From Coq Require Import
     List.

From stdpp Require Import
     fin_maps.

From LibTx Require Import
     SLOT.EventTrace
     SLOT.Handler.

Import ListNotations.

Class DeterministicHandler {PID : Type} (Req : Type) (Ret : Req -> Type) :=
  { det_h_state : Type;
    det_h_chain_rule :  forall (pid : PID) (s : det_h_state) (req : Req), det_h_state * Ret req;
  }.

Global Instance deterministicHandler `{d : DeterministicHandler} : @Handler PID Req Ret :=
  { h_chain_rule s s' te :=
      let (pid, req, ret) := te in
      let (s'_, ret_) := det_h_chain_rule pid s req in
      s' = s'_ /\ ret = ret_;
  }.

Global Arguments deterministicHandler {_} {_} {_}.

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
    Context {PID T : Type}.

    Inductive var_req_t :=
    | read
    | write : T -> var_req_t.

    Definition var_ret_t req :=
      match req with
      | read => T
      | write _ => True
      end.

    Definition var_step (_ : PID) s req : T * var_ret_t req :=
      match req with
      | read => (s, s)
      | write new => (new, I)
      end.

    Global Instance varDetHandler : DeterministicHandler var_req_t var_ret_t :=
      { det_h_state := T;
        det_h_chain_rule := var_step;
      }.
  End defs.

  Definition t {PID} T := deterministicHandler (@varDetHandler PID T).
End Var.

Module AtomicVar.
  Import EquivDec Peano_dec.

  Section defs.
    Context {PID T : Type} `{@EqDec T eq eq_equivalence}.

    Inductive avar_req_t :=
    | read
    | write : T -> avar_req_t
    | CAS : T -> T -> avar_req_t.

    Definition avar_ret_t req :=
      match req with
      | read => T
      | write _ => True
      | CAS _ _ => bool
      end.

    Definition step (_ : PID) s req : T * avar_ret_t req :=
      match req with
      | read => (s, s)
      | write new => (new, I)
      | CAS old new =>
        if equiv_dec old s then
          (new, true)
        else
          (s, false)
      end.

    Global Instance atomVarDetHandler : DeterministicHandler avar_req_t avar_ret_t :=
      { det_h_state := T;
        det_h_chain_rule := step;
      }.
  End defs.

  Definition t {PID} T {H} := deterministicHandler (@atomVarDetHandler PID T H).

  Section tests.
    Goal forall (r1 r2 : nat),
        r1 <> r2 ->
        {{fun _ => True}}
          [I @ r1 <~ read;
           I @ r2 <~ read]
        {{fun s => False}}.
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
    Context {PID K V S : Type} `{HStore : @Storage K V S}.

    (** ** Syscall types: *)
    Inductive kv_req_t :=
    | read : K -> kv_req_t
    | delete : K -> kv_req_t
    | write : K -> V -> kv_req_t
    | snapshot.

    (** *** Syscall return types: *)
    Definition kv_ret_t (req : kv_req_t) : Type :=
      match req with
      | read _ => option V
      | delete _ => True
      | write _ _ => True
      | snapshot => S
      end.

    Let TE := @TraceElem PID kv_req_t kv_ret_t.

    Definition step (_ : PID) (s : S) (req : kv_req_t) : S * kv_ret_t req :=
      match req with
      | read k => (s, get k s)
      | write k v => (put k v s, I)
      | delete k => (Storage.delete k s, I)
      | snapshot => (s, s)
      end.

    Global Instance kvDetHandler : DeterministicHandler kv_req_t kv_ret_t :=
      { det_h_state := S;
        det_h_chain_rule := step;
      }.
  End defn.

  Definition t {PID} K V S {HS} := deterministicHandler (@kvDetHandler PID K V S HS).

  (** * Properties *)
  Section Properties.
    Context {PID K V S : Type} `{HStore : @Storage K V S}.
    (* Context {PID K V : Type} {S : Type} `{HStore : @Storage K V S} `{HKeq_dec : EqDec K}. *)

    (* Let ctx := mkCtx PID (@req_t K V) (@ret_t K V S). *)
    (* Let TE := @TraceElem PID (@req_t K V) (@ret_t K V S). *)

    (** Two read syscalls always commute: *)
    Lemma kv_rr_comm : forall (p1 p2 : PID) k1 k2 v1 v2,
        trace_elems_commute (p1 @ v1 <~ read k1) (p2 @ v2 <~ read k2).
    Proof.
      split; intros;
      repeat trace_step H; subst;
      repeat forward s';
      now constructor.
    Qed.

    (** Read and snapshot syscalls always commute: *)
    Lemma kv_rs_comm : forall (p1 p2 : PID) k v s,
        trace_elems_commute (p1 @ v <~ read k) (p2 @ s <~ snapshot).
    Proof.
      split; intros;
      repeat trace_step H; subst;
      repeat forward s';
      repeat constructor.
    Qed.

    (* Lemma kv_read_get : forall (pid : PID) (s : S) (k : K) (v : option V), *)
    (*     s ~[pid @ v <~ read k]~> s -> *)
    (*     v = get k s. *)
    (* Proof. *)
    (*   intros. *)
    (*   cbn in H. *)
    (*   destruct H. *)
    (*   now subst. *)
    (* Qed. TODO *)

    (** Read and write syscalls commute when performed on different keys: *)
    Lemma kv_rw_comm : forall (p1 p2 : PID) k1 k2 v1 v2,
        k1 <> k2 ->
        trace_elems_commute (p1 @ v1 <~ read k1) (p2 @ I <~ write k2 v2).
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
    Lemma kv_rd_comm : forall (p1 p2 : PID) k1 k2 v1,
        k1 <> k2 ->
        trace_elems_commute (p1 @ v1 <~ read k1) (p2 @ I <~ delete k2).
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
    Example kv_ww_comm : forall (p1 p2 : PID) k1 k2 v1 v2,
        k1 <> k2 ->
        trace_elems_commute (p1 @ I <~ write k1 v1) (p2 @ I <~ write k2 v2).
    Abort.
  End Properties.
End KV.

Module History.
  Section defs.
    Context {PID Event : Type}.

    Definition State : Type := list Event.

    Definition hist_req_t := PID -> Event.

    Definition step (pid : PID) (s : State) (req : hist_req_t) := (req pid :: s, I).

    Global Instance historyDetHandler : DeterministicHandler hist_req_t (fun _ => True) :=
      { det_h_state := list Event;
        det_h_chain_rule := step;
      }.
  End defs.

  Definition t {PID} Event := deterministicHandler (@historyDetHandler PID Event).
End History.

Module ProcessDictionary.
  Section defs.
    Context {PID Val : Type} `{FinMap PID Map}.

    Inductive req_t : Type :=
    | pd_get
    | pd_erase
    | pd_put : Val -> req_t.

    Definition ret_t req : Type :=
      match req with
      | pd_get => option Val
      | pd_put _ => True
      | pd_erase => True
      end.

    Definition State := Map Val.

    Definition step (pid : PID) (s : State) (req : req_t) : State * ret_t req :=
      match req with
      | pd_get => (s, s !! pid)
      | pd_put new_val => (<[pid := new_val]> s, I)
      | pd_erase => (delete pid s, I)
      end.

    Global Instance processDictDetHandler : DeterministicHandler req_t ret_t :=
      { det_h_state := State;
        det_h_chain_rule := step;
      }.

    Definition t := deterministicHandler processDictDetHandler.
  End defs.

  Global Arguments t {_}.
End ProcessDictionary.

Module Self.
  Section defs.
    Context {PID : Type}.

    Inductive req_t := self.

    Global Instance selfDetHandler : DeterministicHandler req_t (fun _ => PID) :=
      { det_h_state := True;
        det_h_chain_rule pid _ _ := (I, pid)
      }.

    Definition t := deterministicHandler selfDetHandler.
  End defs.
End Self.
