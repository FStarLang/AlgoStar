(*
   Ch07 Quicksort Bridge Lemmas — proofs.

   NO admits. NO assumes.
*)
module CLRS.Ch07.Quicksort.C.BridgeLemmas

open CLRS.Common.SortSpec
open CLRS.Ch07.Partition.Lemmas
module Seq  = FStar.Seq
module SeqP = FStar.Seq.Properties
module I32  = FStar.Int32
module Classical = FStar.Classical

// ================================================================
// extract_ints
// ================================================================

let extract_ints (s: Seq.seq (option I32.t)) (len: nat{all_some s len})
  : Tot (r: Seq.seq int{Seq.length r == len /\
    (forall (i: nat). i < len ==> Seq.index r i == I32.v (Some?.v (Seq.index s i)))})
  = Seq.init len (fun (i: nat{i < len}) -> (I32.v (Some?.v (Seq.index s i)) <: int))

// ================================================================
// adjacent_sorted_implies_sorted
// ================================================================

private let rec adj_step (s: Seq.seq int) (i j: nat)
  : Lemma
    (requires (forall (k: nat). k + 1 < Seq.length s ==> Seq.index s k <= Seq.index s (k + 1)))
    (ensures i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j)
    (decreases (j - i))
  = if i >= j || j >= Seq.length s then ()
    else (adj_step s i (j - 1))

private let adj_sorted (s: Seq.seq int)
  : Lemma
    (requires forall (k: nat). k + 1 < Seq.length s ==> Seq.index s k <= Seq.index s (k + 1))
    (ensures sorted s)
  = Classical.forall_intro_2 (Classical.move_requires_2 (adj_step s))

let adjacent_sorted_implies_sorted (s: Seq.seq (option I32.t)) (len: nat)
  = let ints = extract_ints s len in
    assert (forall (k: nat). k + 1 < Seq.length ints ==> Seq.index ints k <= Seq.index ints (k + 1));
    adj_sorted ints

// ================================================================
// swap_extract_permutation
// ================================================================

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"

let swap_extract_permutation
  (s: Seq.seq (option I32.t)) (len: nat) (i j: nat)
  = let s' = Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i) in
    let ints = extract_ints s len in
    let ints' = extract_ints s' len in
    let ints_swapped = Seq.upd (Seq.upd ints i (Seq.index ints j)) j (Seq.index ints i) in
    assert (Seq.equal ints' ints_swapped);
    swap_is_permutation ints i j

#pop-options

// ================================================================
// unchanged_extract_eq
// ================================================================

let unchanged_extract_eq
  (s1 s2: Seq.seq (option I32.t)) (len: nat)
  = let ints1 = extract_ints s1 len in
    let ints2 = extract_ints s2 len in
    assert (forall (k: nat). k < len ==> Seq.index ints1 k == Seq.index ints2 k)

// ================================================================
// c_bounds_implies_between_bounds
// ================================================================

let c_bounds_implies_between_bounds
  (s: Seq.seq (option I32.t)) (len: nat) (lb rb: I32.t)
  = let ints = extract_ints s len in
    assert (forall (k: nat). k < len ==> I32.v lb <= Seq.index ints k /\ Seq.index ints k <= I32.v rb);
    assert (forall (k: int). 0 <= k /\ k < Seq.length ints ==> I32.v lb <= Seq.index ints k);
    assert (forall (k: int). 0 <= k /\ k < Seq.length ints ==> Seq.index ints k <= I32.v rb)

// ================================================================
// subrange_sorted_implies_sorted
// ================================================================

let subrange_sorted_implies_sorted
  (s: Seq.seq (option I32.t)) (lo hi: nat)
  = let sub = Seq.slice s lo hi in
    let ints = extract_ints sub (hi - lo) in
    assert (forall (k: nat). k + 1 < hi - lo ==>
      Seq.index ints k == I32.v (Some?.v (Seq.index sub k)) /\
      Seq.index ints (k + 1) == I32.v (Some?.v (Seq.index sub (k + 1))));
    assert (forall (k: nat). k + 1 < hi - lo ==>
      Seq.index ints k <= Seq.index ints (k + 1));
    adj_sorted ints
