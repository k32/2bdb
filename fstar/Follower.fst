module Follower
module M = FStar.OrdMap
module MP = FStar.OrdMapProps
open FStar.List.Tot
module S = FStar.OrdSet

type offset = nat
type key = nat
type seqno = int

val nat_order : OrdSet.cmp nat
let nat_order :(f:(nat -> nat -> bool){OrdSet.total_order nat f}) = fun x y -> x <= y
type seqnos = M.ordmap key seqno nat_order

noeq type state =
  | State : s_ws:nat -> s_offset:offset -> s_seqnos:seqnos -> state

let initial_state ws = State ws 0 M.empty

val get_seqno : k:key -> s:state -> Tot seqno
let get_seqno k s =
  match M.select k s.s_seqnos with
  | Some x -> x
  | None -> 0

val next_seqno : k:key -> s:state -> Tot (seqno * state)
let next_seqno k s =
  match s with
  | State ws o sn -> let v = 1 + get_seqno k s in (v, State ws o (M.update k v sn))

type tx =
  | WriteTx : local_tlogn:offset ->
              reads:list (key * offset) ->
              writes:list (key * offset) ->
              tx

type tlog = list tx

val collect_garbage : state -> Tot state
let collect_garbage s =
  match s with
  | State ws o s' ->
    let maybe_clean k v acc = if v > o - ws then acc
                              else M.remove k acc
    in State ws o (MP.fold maybe_clean s' s')

val forall_seqnos : seqnos -> (seqno -> Tot prop) -> Tot prop
let forall_seqnos s p = squash (MP.fold (fun _ v a -> p v /\ a) s True)

val gc_works: s:state -> Lemma (requires True)
                              (ensures (forall_seqnos ((collect_garbage s).s_seqnos)
                                                      (fun x -> True)))


// val seqno_is_positive: s:state -> k:key -> GTot (u:unit{fst (next_seqno k s) > 0})
// let rec seqno_is_positive s k =
//   match s with
//   | State _ _ s' ->
//     match M.contains s' k with
//     | false -> ()
//     | true  -> ()
