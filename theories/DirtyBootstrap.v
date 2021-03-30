(* LibTx, proofs about distributed systems design
   Copyright (C) 2019-2021  k32

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, version 3 of the License.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)
From LibTx Require Import
     Storage
     Handlers.Deterministic
     SLOT.

From Coq Require Import
     List.
Import ListNotations.

Section defn.
  Context {K V DB} `{@Storage K V DB}.

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

    Definition s_log (s : h_state Handler) : list (@Wlog_elem K V).
      simpl in s. now decompose_state.
    Defined.

    Definition s_db (s : h_state Handler) : DB.
      simpl in s. now decompose_state.
    Defined.
  End boilerplate.

  Definition apply_op (w : @Wlog_elem K V) :=
    match w with
    | wl_write k v => write k v
    | wl_delete k => delete k
    end.

  Let Thread := @Thread req_t ret_t.

  Fixpoint writer_loop (ops : @Wlog K V) : Thread :=
    match ops with
    | [] => t_dead
    | op :: tail =>
      do _ <- apply_op op;
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

From Coq Require Import Logic.Classical.

Require Import Program.

Section props.
  Context K V DB `{@Storage K V DB}.

  Lemma no_op_apply : -{{ fun s => (s_log s) = [] }}
                         dirty_bootstrapper []
                       {{ fun s => s_db s =s= Wlog_apply (s_log s) new }}.
  Proof.
    intros t Ht. unfold_ht.
    unfold dirty_bootstrapper in Ht.
    destruct Ht as [t1 t2 t Hwriter Hagent Ht].
    thread_step Hwriter. apply interleaving_nil in Ht. subst.
    destruct s_begin as [s_db_begin s_log_begin]. destruct s_end as [s_db_end s_log_end]. simpl in *.
    thread_step Hagent.
    clear Heqt0. simpl in *.
    long_step Hls handler_step. destruct Hcr as [? ?]. subst.
    remember (Storage.keys s_db_begin) as kk.
    generalize dependent trace.
    generalize dependent s_db_begin.
    induction kk as [|k rest].
    - intros.
      thread_step Hagent.
      long_step Hls. subst.
      simpl.
      apply empty_keys_eq_new. auto.
    - intros.
      thread_step Hagent.
      simpl in Heqt.
      long_step Hls handler_step.
      destruct Hcr as [? ?]. subst.
      (* Ensure that reading the key now produces result *)
      assert (In k (Storage.keys s_db_begin)).
      { rewrite <-Heqkk. apply in_eq. }
      remember (get k s_db_begin) as val.
      destruct val.
      2:{ apply keys_some in H0. destruct H0. rewrite <-Heqval in H0. discriminate. }
      subst. simpl in *.
      specialize (IHrest rest).

    cbv in s. destruct s as [s_l s_r]. inversion Hcr.
    simpl in H0. destruct H0 as [? [? ?]].


    long_step Hls handler_step.
    destruct Hcr as [Hl Hr]. subst.
    dependent destruction Hr.

    dependent destruction s. Locate "~=".

    remember (Storage.keys s_db_begin) as kk.


    remember (Storage.keys (s_db s_begin)) as kk.

    thread_step Hagent. simpl in *.

    induction ret as [|k rest].
    -
      thread_step Hagent.



    apply canonicalize_ilv with (s := s_begin) (s' := s_end) in Ht.
    2:{ intros. apply classic. }
    2:{ assumption. }
    clear Hls.
    destruct Ht as [t' [Ht' Hls']].
    cbn in Hwriter.
