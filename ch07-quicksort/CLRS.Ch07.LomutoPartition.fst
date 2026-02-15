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

// ========== Swap Lemmas ==========

// Lemma: When we swap A[i] with A[j] where A[j] <= pivot and A[i] is in the ">" region,
// the Lomuto invariant is preserved
let lemma_lomuto_swap_small
  (s: Seq.seq int)
  (pivot: int)
  (p i j r: nat)
  (vi vj: int)
  : Lemma
    (requires
      p <= i /\ i <= j /\ j < r /\ r < Seq.length s /\
      Seq.index s i == vi /\
      Seq.index s j == vj /\
      vj <= pivot /\
      (i < j ==> vi > pivot) /\  // If i < j, then vi must be in the ">" region
      (forall (k: nat). p <= k /\ k < i ==> Seq.index s k <= pivot) /\
      (forall (k: nat). i <= k /\ k < j ==> Seq.index s k > pivot) /\
      Seq.index s r == pivot)
    (ensures
      (let s1 = Seq.upd s i vj in
       let s2 = Seq.upd s1 j vi in
       (forall (k: nat). p <= k /\ k < i + 1 ==> Seq.index s2 k <= pivot) /\
       (forall (k: nat). i + 1 <= k /\ k < j + 1 ==> Seq.index s2 k > pivot) /\
       Seq.index s2 r == pivot))
  = ()

// Lemma: When A[j] > pivot, no swap occurs and we just extend the "> pivot" region
let lemma_lomuto_no_swap_large
  (s: Seq.seq int)
  (pivot: int)
  (p i j r: nat)
  (vj: int)
  : Lemma
    (requires
      p <= i /\ i <= j /\ j < r /\ r < Seq.length s /\
      Seq.index s j == vj /\
      vj > pivot /\
      (forall (k: nat). p <= k /\ k < i ==> Seq.index s k <= pivot) /\
      (forall (k: nat). i <= k /\ k < j ==> Seq.index s k > pivot) /\
      Seq.index s r == pivot)
    (ensures
      (forall (k: nat). p <= k /\ k < i ==> Seq.index s k <= pivot) /\
      (forall (k: nat). i <= k /\ k < j + 1 ==> Seq.index s k > pivot) /\
      Seq.index s r == pivot)
  = ()

// Lemma: Final swap of A[i+1] with A[r] (pivot) completes the partition
let lemma_lomuto_final_swap
  (s: Seq.seq int)
  (pivot: int)
  (p i r: nat)
  (vi: int)
  : Lemma
    (requires
      p <= i /\ i <= r /\ r < Seq.length s /\
      Seq.index s i == vi /\
      Seq.index s r == pivot /\
      (forall (k: nat). p <= k /\ k < i ==> Seq.index s k <= pivot) /\
      (forall (k: nat). i <= k /\ k < r ==> Seq.index s k > pivot))
    (ensures
      (let s1 = Seq.upd s i pivot in
       let s2 = Seq.upd s1 r vi in
       Seq.index s2 i == pivot /\
       (forall (k: nat). p <= k /\ k < i ==> Seq.index s2 k <= pivot) /\
       (forall (k: nat). i < k /\ k <= r ==> Seq.index s2 k > pivot)))
  = ()

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
    let vi = !i_plus_1;
    
    // Increment j first (unconditionally)
    j := SZ.add vj 1sz;
    
    with s_before. assert (A.pts_to a s_before);
    
    // Read both values before modification
    let aj = a.(vj);
    let ai = a.(vi);
    
    // Determine if we should swap
    let should_swap = (aj <= pivot);
    
    // Unconditional writes with conditional values
    let new_ai = (if should_swap then aj else ai);
    let new_aj = (if should_swap then ai else aj);
    a.(vi) <- new_ai;
    a.(vj) <- new_aj;
    
    with s_after. assert (A.pts_to a s_after);
    
    // Prove partition invariant is maintained
    if (should_swap) {
      lemma_lomuto_swap_small s_before pivot (SZ.v p) (SZ.v vi) (SZ.v vj) (SZ.v r) ai aj;
      i_plus_1 := SZ.add vi 1sz;
      ()
    } else {
      assert (pure (new_ai == ai /\ new_aj == aj));
      assert (pure (Seq.equal s_after s_before));
      lemma_lomuto_no_swap_large s_before pivot (SZ.v p) (SZ.v vi) (SZ.v vj) (SZ.v r) aj;
      ()
    }
  };

  // exchange A[i+1] with A[r]
  let final_i1 = !i_plus_1;
  with s_before_swap. assert (A.pts_to a s_before_swap);
  
  // Save values before swap
  let vi_val = a.(final_i1);
  let pivot_val = a.(r);
  
  // Swap manually
  a.(final_i1) <- pivot_val;
  a.(r) <- vi_val;
  
  with s_final. assert (A.pts_to a s_final);
  
  // Apply lemma to prove the final swap creates the correct partition
  lemma_lomuto_final_swap s_before_swap pivot (SZ.v p) (SZ.v final_i1) (SZ.v r) vi_val;

  // return i + 1
  final_i1
}
#pop-options
