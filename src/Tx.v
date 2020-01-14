(*** Transactional operations *)
Require Import List.
Require Import Coq.Program.Basics.
Import ListNotations.
Import Decidable.
Require Import Sumbool.
Require Import FoldIn.
Require Import EqDec.
Require Import Storage.
Require Locker.

Module Impl (S : Storage.Interface).
  Module L := Locker.Unbounded S.


End Impl.

Module Consistency (I : Storage.Interface).
Module L := Unbounded S.


Variables TxId K V : Set.
Variable TxId_eq_dec : eq_decP TxId.
Variable K_eq_dec : eq_decP K.
Variable V_eq_dec : eq_decP V.

Inductive TxAgentOp : Set :=
| txa_open : TxId -> TxAgentOp
| txa_done : TxId -> TxAgentOp
| txa_read : TxId -> K -> V -> TxAgentOp
| txa_write : TxId -> K -> V -> TxAgentOp.

Inductive TxHandlerOp : Set:=
| txh_commit : TxId -> TxHandlerOp
| txh_abort : TxId -> TxHandlerOp.

Inductive TxOp : Set :=
| txa : TxAgentOp -> TxOp
| txh : TxHandlerOp -> TxOp.

Definition Trace := list TxOp.

Definition irrelevant_tx (txId : TxId) (l : Trace) : Prop. Admitted.

Definition irrelevant_key (key : K) (l : Trace) : Prop. Admitted.

Definition irrelevant_tx_key (txId : TxId) (k : K) (l : Trace) : Prop. Admitted.

Local Definition read txId k v := txa (txa_read txId k v).

Definition snapshot_read_isolationP run_system := forall txId k v v' (t0 t1 t2 t3 : Trace),
    irrelevant_tx txId t1 ->
    irrelevant_tx txId t2 ->
    irrelevant_tx txId t3 ->
    (t0 ++ [txa (txa_read txId k v)] ++ t1 ++
        [txa (txa_read txId k v')] ++ t2 ++ [txh txh_commit txId] ++ t3 = run_system) ->
    v = v'.

Definition serialazable_read_isolationP run_system := forall txId1 txId2 k v v' (t0 t1 t2 t3 : Trace),
    irrelevant_tx txId1 t2 ->
    irrelevant_tx txId2 t2 ->
    (t0 ++ [tx_read txId1 k v] ++ t2 ++
        [tx_read txId2 k v'] ++ t3 = run_system) ->
    v = v'.
