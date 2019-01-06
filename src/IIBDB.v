(* Require Import Verdi.Verdi. *)
(* Require Import Verdi.HandlerMonad. *)
Require Import String.
Require Import List.
Import ListNotations.

(*         ------ [(server) ---- (locker) ---- (storage)]
          /
    (tlog) ------ [(server) ---- (locker) ---- (storage)]
          \
           ------ [(server) ---- (locker) ---- (storage)]
 *)

(* Require Import fingroup. *)

Set Implicit Arguments.

Module IIDB.

Definition TabName := String.string.

Module Storage.

Module Type Interface.
  (* Atomic operations that storage should define *)
  Parameter Storage : Type -> Type -> Type.

  (* Parameter Iterator : Type -> Type -> Type. *)

  Parameter new : forall {K V : Type}, Storage K V.

  Parameter put : forall {K V : Type}, K -> V -> Storage K V -> Storage K V.

  Parameter get : forall {K V : Type}, K -> Storage K V -> option V.

  Parameter size : forall {K V : Type}, Storage K V -> nat.

  Parameter delete : forall {K V : Type}, K -> Storage K V -> Storage K V.

  (* Parameter seek_first : forall {K V : Type}, Storage K V -> option (K * Iterator K V). *)

  (* Parameter next : forall {K V : Type}, Iterator K V -> option (K * Iterator K V). *)

  Parameter keys : forall {K V : Type}, Storage K V -> list K.

  Axiom new_empty : forall {K V : Type} k,
      get k (new : Storage K V) = None.

  Axiom keep : forall {K V : Type} (s : Storage K V) (k : K) (v : V),
      get k (put k v s) = Some v.

  Axiom distinct : forall {K V : Type} (s : Storage K V) (k1 : K) (k2 : K) (v2 : V),
      k1 <> k2 ->
      get k1 s = get k1 (put k2 v2 s).

  Axiom delete_none : forall {K V : Type} (s : Storage K V) k,
      get k (delete k s) = None.

  Axiom size_keys_len : forall {K V : Type} (s : Storage K V),
      size s = length (keys s).

  Axiom keys_member_exists : forall {K V : Type} (s : Storage K V) k,
      In k (keys s) -> exists v, get k s = Some v.

  Axiom keys_non_member : forall {K V : Type} (s : Storage K V) k,
      ~ In k (keys s) -> get k s = None.


  (* Axiom iter_empty : forall {K V : Type} (s : Storage K V), *)
  (*     size s = 0 -> *)
  (*     seek_first s = None. *)

  (* Axiom iter_next : forall {K V : Type} (s : Storage K V) k v i, *)
  (*     Some (k, i) = seek_first s -> *)
  (*     (get k s = Some v) /\ (next i = seek_first (delete k s)).e *)

  (* Axiom all_keys_present : forall {K V : Type} (s : Storage K V) k, *)
  (*     member k (keys s) . *)
End Interface.

Module Equality (I : Interface).
  Import I.

  Inductive s_eq {K V} (s1 : Storage K V) (s2 : Storage K V) :=
  | s_eq_ : (forall k, get k s1 = get k s2) -> s_eq s1 s2.

  Lemma new_eq : forall {K V}, s_eq (@new K V) (@new K V).
  Proof.
    intros K V.
    constructor.
    intros k.
    rewrite new_empty.
    reflexivity.
  Qed.

  Lemma put_eq_eq : forall {K V} (s1 s2 : Storage K V) k v,
      (forall k1 k2 : K, {k1 = k2} + {k1 <> k2}) ->
      s_eq s1 s2 ->
      s_eq (put k v s1) (put k v s2).
  Proof.
    intros K V s1 s2 k v Heq_dec Heq.
    constructor.
    intros x.
    destruct (Heq_dec x k) as [H|H].
    - subst. repeat rewrite keep. reflexivity.
    - repeat rewrite <-(@distinct _ _ _ x k v H).
      destruct Heq as [Heq]. apply Heq.
  Qed.

  Lemma put_same : forall {K V} (s : Storage K V) k v,
      (forall k1 k2 : K, {k1 = k2} + {k1 <> k2}) ->
      get k s = Some v ->
      s_eq s (put k v s).
  Proof.
    intros K V s k v Heq_dec Hkv.
    constructor.
    intros x.
    destruct (Heq_dec x k) as [H|H].
    - subst. rewrite keep, Hkv. reflexivity.
    - rewrite <-(@distinct _ _ _ x k v H). reflexivity.
  Qed.
End Equality.

Module Versioned (I : Interface).
  Inductive maybe_dead (A : Type) :=
  | Alive : A -> maybe_dead A
  | Dead : nat -> maybe_dead A.

  Record versioned d := mkVer
                          { version : nat;
                            data : maybe_dead d;
                          }.

  Definition VS K V := I.Storage K (versioned V).

  Definition put {K V} (k : K) (v : V) (s : VS K V) : VS K V :=
    match I.get k s with
    | None => I.put k (mkVer 1 (Alive v)) s
    | Some v0 => I.put k (mkVer (S (version v0)) (Alive v)) s
    end.

  Definition get {K V} (k : K) (s : VS K V) : option V :=
    match I.get k s with
    | None => None
    | Some v => match data v with
               | Alive x => Some x
               | Dead _ _ => None
               end
    end.

  Definition get_v {K V} (k : K) (s : VS K V) : (nat * option V) :=
    match I.get k s with
    | None => (0, None)
    | Some v => match data v with
               | Alive x => (version v, Some x)
               | Dead _ _ => (version v, None)
               end
    end.

  Definition delete {K V} (k : K) (n : nat) (s : VS K V) : VS K V :=
    match I.get k s with
    | None => s
    | Some v0 => I.put k (mkVer (S (version v0)) (Dead V n)) s
    end.

  Definition new {K V} :=
    @I.new K V.
End Versioned.

Module Table (I : Interface).
  Module V := Versioned I.

  Record Table {K V} := mkTable
                    { version : nat;
                      table : V.VS K V
                    }.


End Table.

End Storage.

Module Transaction (I : Storage.Interface).
  Module V := Storage.Versioned I.

  Inductive read_lock {K} :=
  | lk_record : TabName -> K -> read_lock
  | lk_table : TabName -> read_lock.

  Record trans {K V : Type} :=
    mkTrans {
        read_locks : list (@read_lock K);
        writes : list ((TabName * K) * (V * nat));
      }.

  Inductive transaction {K V : Type} :=
  | set : @trans K V -> transaction
  | new_tab : TabName -> transaction
  | del_tab : TabName -> transaction
  .

  Inductive tr_ctxt {K V A : Type} :=
  | tr_ok : A -> @trans K V -> V.versioned -> tr_ctxt
  | tr_fail : tr_ctxt.

  Definition tr_monad {K V A} := @trans K V -> @tr_ctxt K V A.

  (* TODO locker *)
  Definition bind {K V A B : Type}
             (m : @tr_monad K V A)
             (f : A -> @tr_monad K V B) : @tr_monad K V B :=
    fun tr0 =>
      match m tr0 with
      | tr_ok a tr1 => (f a) tr1
      | tr_fail => tr_fail
      end.

  Definition read {K V} (k : K) : @tr_monad K V (option V) :=


  Notation "a <- b ;t c" := (@bind _ _ _ _ b (fun a => c))
                              (at level 100, c at next level, right associativity).

  Notation "e1 ;t e2" := (_ <- e1 ;t e2)
                           (at level 100, right associativity).
End Transaction.

Module Crypto.

Definition plaintext := String.string.

(* Abstract symmetric cypher *)
Module Type Symm.
  Parameter key : Type.

  Parameter cyphertext : Type.

  Parameter encrypt : key -> plaintext -> cyphertext.

  Parameter decrypt : key -> cyphertext -> plaintext.

  Axiom encrypt_decrypt : forall (k : key) (t : plaintext),
      (decrypt k (encrypt k t)) = t.
End Symm.

(* A fake symmetric "cypher" implementation that is used to reason
about the ability to decrypt messages *)
Module Unencrypted <: Symm.
  Definition key := nat.

  Definition beq := beq_nat.

  Definition plaintext := String.string.

  Record withKey := mkWithKey
                      { encryptedWith : key;
                        msg : String.string;
                      }.
  Definition cyphertext := withKey.

  Definition encrypt := mkWithKey.

  Definition decrypt (k : key) (c : cyphertext) : plaintext :=
    if beq (encryptedWith c) k
    then msg c
    else String.EmptyString.

  Lemma encrypt_decrypt : forall (k : key) (t : plaintext),
      (decrypt k (encrypt k t)) = t.
  Proof.
    intros.
    unfold decrypt,beq. simpl. rewrite <-beq_nat_refl. reflexivity.
  Qed.
End Unencrypted.

Module Type DiffieHellman.
  Parameter G : Type.

  Parameter gPow : G -> nat -> G.

  Axiom gPow_comm :

  Parameter pub_key : Type.
  Parameter prv_key : Type.

  Definition pub_key : Set.
  Admitted.

  Definition priv_key : Set.
  Admitted.

  Definition initial_params : Set.
  Admitted.

  Definition key_exchange : Set.
  Admitted.
End DH.

Inductive Name : Set :=
| tlog_serv
| db_clinet : nat -> Name
.

Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
  decide equality.
  apply NPeano.Nat.eq_dec.
Defined.

Definition generation := nat.
Definition key := string.
Definition value := nat.
Definition offset := nat.

Definition generation_eq_dec := Nat.eq_dec.
Definition key_eq_dec := string_dec.
Definition value_eq_dec := Nat.eq_dec.
Definition offset_eq_dec := Nat.eq_dec.

Inductive TLogMsg : Set :=
| Onboard : Name -> DH.pub_key -> TLogMsg (* TODO: HMAC *)
| DH_Init : generation -> DH.initial_params -> TLogMsg
| DH_Ack : generation -> DH.key_exchange -> TLogMsg
|
.

Inductive Msg : Set :=
| tlog_push : list (key * value) -> Msg
| tlog_ack : offset -> Msg
| tlog_poll_req : offset -> nat -> Msg
| tlog_poll_rep : list (key * value) -> Msg
.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
  repeat decide equality.
Defined.

Inductive input : Set :=
| Get : key -> input
| Inc : key -> value -> input
.

Definition input_eq_dec : forall x y : input, {x = y} + {x <> y}.
  repeat decide equality.
Defined.

Inductive output :  Set :=
| Response : key -> option value -> output.

Definition output_eq_dec : forall x y : output, {x = y} + {x <> y}.
  repeat decide equality.
Defined.

Module BlindDB.
