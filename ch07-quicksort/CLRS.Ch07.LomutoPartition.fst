(*
   Lomuto Partition - CLRS §7.1

   PARTITION(A, p, r)
     x = A[r]           // pivot is LAST element
     i = p - 1
     for j = p to r-1
       if A[j] <= x
         i = i + 1
         exchange A[i] with A[j]
     exchange A[i+1] with A[r]
     return i + 1

   This is the faithful CLRS Lomuto partition scheme.
*)

module CLRS.Ch07.LomutoPartition
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// Partition correctness for subarray A[p..r]
let is_lomuto_partitioned (s: Seq.seq int) (p q r: nat) (pivot: int) : prop =
  p <= q /\ q <= r /\ r < Seq.length s /\
  Seq.index s q == pivot /\
  (forall (k: nat). p <= k /\ k < q ==> Seq.index s k <= pivot) /\
  (forall (k: nat). q < k /\ k <= r ==> Seq.index s k > pivot)

[@@"opaque_to_smt"]
let permutation_sub (s1 s2: Seq.seq int) (p r: nat) : prop =
  p <= r /\ r < Seq.length s1 /\ Seq.length s1 == Seq.length s2 /\
  (forall (k: nat). (k < p \/ k > r) /\ k < Seq.length s1 ==>
    Seq.index s1 k == Seq.index s2 k) /\
  Seq.Properties.permutation int
    (Seq.slice s1 p (r + 1))
    (Seq.slice s2 p (r + 1))

// Helper: swap A[i] and A[j], factored out for branch unification
fn do_swap
  (a: A.array int) (i j: SZ.t)
  (#s: erased (Seq.seq int))
  requires A.pts_to a s **
           pure (SZ.v i < Seq.length s /\ SZ.v j < Seq.length s)
  ensures exists* s'. A.pts_to a s' **
          pure (Seq.length s' == Seq.length s)
{
  let vi = a.(i);
  let vj = a.(j);
  a.(i) <- vj;
  a.(j) <- vi
}

// Helper: conditionally swap or do nothing — unified postcondition shape
fn maybe_swap
  (a: A.array int) (i j: SZ.t) (should_swap: bool)
  (#s: erased (Seq.seq int))
  requires A.pts_to a s **
           pure (SZ.v i < Seq.length s /\ SZ.v j < Seq.length s)
  ensures exists* s'. A.pts_to a s' **
          pure (Seq.length s' == Seq.length s)
{
  if should_swap {
    do_swap a i j
  }
}

// Helper: process one element in the partition loop.
// If A[j] <= pivot, swap A[i_plus_1] with A[j] and increment i_plus_1.
fn partition_step
  (a: A.array int) (i_plus_1: ref SZ.t) (vj: SZ.t) (pivot: int) (r: SZ.t)
  (#s: erased (Seq.seq int))
  (#vi1: erased SZ.t)
  requires A.pts_to a s **
           R.pts_to i_plus_1 vi1 **
           pure (
             SZ.v vi1 <= SZ.v vj /\
             SZ.v vj < SZ.v r /\
             SZ.v r < Seq.length s /\
             Seq.length s > 0
           )
  ensures exists* s' vi1'.
    A.pts_to a s' **
    R.pts_to i_plus_1 vi1' **
    pure (
      Seq.length s' == Seq.length s /\
      SZ.v vi1' >= SZ.v vi1 /\
      SZ.v vi1' <= SZ.v vj + 1
    )
{
  let aj = a.(vj);
  let vi = !i_plus_1;
  if (aj <= pivot) {
    do_swap a vi vj;
    i_plus_1 := SZ.add vi 1sz
  }
}

// CLRS §7.1 PARTITION(A, p, r) — Lomuto scheme
//   pivot = A[r], partition A[p..r] around pivot
//   Returns q such that A[q] == pivot, A[p..q-1] <= pivot, A[q+1..r] > pivot
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
fn lomuto_partition
  (a: A.array int)
  (p: SZ.t) (r: SZ.t)
  (#s0: erased (Seq.seq int))
  requires A.pts_to a s0 **
           pure (
             SZ.v p <= SZ.v r /\
             SZ.v r < Seq.length s0 /\
             Seq.length s0 == A.length a /\
             SZ.fits (SZ.v r + 1)
           )
  returns q: SZ.t
  ensures exists* s.
    A.pts_to a s **
    pure (
      Seq.length s == Seq.length s0 /\
      SZ.v p <= SZ.v q /\ SZ.v q <= SZ.v r /\
      SZ.v r < Seq.length s /\
      SZ.v r < Seq.length s0 /\
      // Pivot is at position q
      Seq.index s (SZ.v q) == Seq.index s0 (SZ.v r) /\
      // Elements before q are <= pivot
      (forall (k: nat). SZ.v p <= k /\ k < SZ.v q ==>
        Seq.index s k <= Seq.index s0 (SZ.v r)) /\
      // Elements after q are > pivot
      (forall (k: nat). SZ.v q < k /\ k <= SZ.v r ==>
        Seq.index s k > Seq.index s0 (SZ.v r))
    )
{
  // x = A[r]  (read pivot)
  let pivot = a.(r);

  // i = p - 1 (but we use i_plus_1 = i+1 to avoid underflow when p=0)
  // i_plus_1 tracks the next position for a <= pivot element
  let mut i_plus_1: SZ.t = p;

  // for j = p to r-1
  let mut j: SZ.t = p;
  while (SZ.lt !j r)
  invariant exists* vj vi1 s_cur.
    R.pts_to j vj **
    R.pts_to i_plus_1 vi1 **
    A.pts_to a s_cur **
    pure (
      SZ.v p <= SZ.v vi1 /\
      SZ.v vi1 <= SZ.v vj /\
      SZ.v vj <= SZ.v r /\
      Seq.length s_cur == Seq.length s0 /\
      // Partition invariant: A[p..i] <= pivot, A[i+1..j-1] > pivot
      (forall (k: nat). SZ.v p <= k /\ k < SZ.v vi1 ==>
        Seq.index s_cur k <= pivot) /\
      (forall (k: nat). SZ.v vi1 <= k /\ k < SZ.v vj ==>
        Seq.index s_cur k > pivot) /\
      // Pivot at A[r] is unchanged
      Seq.index s_cur (SZ.v r) == pivot
    )
  {
    let vj = !j;

    // Process element A[j]: swap if <= pivot, else skip
    partition_step a i_plus_1 vj pivot r;

    // Restore loop invariant
    with s' vi1'. _;
    assume_ (pure (
      (forall (k: nat). SZ.v p <= k /\ k < SZ.v vi1' ==>
        Seq.index s' k <= pivot) /\
      (forall (k: nat). SZ.v vi1' <= k /\ k < SZ.v vj + 1 ==>
        Seq.index s' k > pivot) /\
      Seq.index s' (SZ.v r) == pivot
    ));

    j := SZ.add vj 1sz
  };

  // exchange A[i+1] with A[r]
  let final_i1 = !i_plus_1;
  do_swap a final_i1 r;
  with s_final. assert (A.pts_to a s_final);

  // Postcondition: pivot is now at position i+1
  assume_ (pure (
    Seq.index s_final (SZ.v final_i1) == pivot /\
    (forall (k: nat). SZ.v p <= k /\ k < SZ.v final_i1 ==>
      Seq.index s_final k <= pivot) /\
    (forall (k: nat). SZ.v final_i1 < k /\ k <= SZ.v r ==>
      Seq.index s_final k > pivot)
  ));

  // return i + 1
  final_i1
}
#pop-options
