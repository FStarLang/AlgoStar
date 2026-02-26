(*
   Partition - Verified implementation in Pulse (CLRS Chapter 7)
   
   The partition subroutine rearranges an array so all elements <= pivot come
   before all elements > pivot, using the two-pointer approach from CLRS.
   This is the key building block used by Quicksort.
   
   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Each comparison (one per iteration) gets exactly one ghost tick.
   
   Proves:
   1. Memory safety
   2. Length preservation  
   3. Return value is valid partition point (0 <= result <= n)
   4. Permutation: output is a rearrangement of input
   5. Partition correctness: elements before split <= pivot, after > pivot
   6. Complexity: exactly n comparisons (one per element)
   
   NO admits. NO assumes.
*)

module CLRS.Ch07.Partition
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Classical = FStar.Classical

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Definitions ==========

//SNIPPET_START: is_partitioned
// Partition predicate: all elements before split are <= pivot,
// all elements from split onwards are > pivot
let is_partitioned (s: Seq.seq int) (pivot: int) (split: nat) : prop =
  split <= Seq.length s /\
  (forall (i: nat). i < split ==> Seq.index s i <= pivot) /\
  (forall (i: nat). split <= i /\ i < Seq.length s ==> Seq.index s i > pivot)
//SNIPPET_END: is_partitioned

// ========== Permutation ==========

[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)

let permutation_same_length (s1 s2 : Seq.seq int)
  : Lemma (requires permutation s1 s2)
          (ensures Seq.length s1 == Seq.length s2)
          [SMTPat (permutation s1 s2)]
  = reveal_opaque (`%permutation) (permutation s1 s2);
    Seq.Properties.perm_len s1 s2

let permutation_refl (s: Seq.seq int)
  : Lemma (ensures permutation s s)
    [SMTPat (permutation s s)]
  = reveal_opaque (`%permutation) (permutation s s)

let compose_permutations (s1 s2 s3: Seq.seq int)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
    (ensures permutation s1 s3)
    [SMTPat (permutation s1 s2); SMTPat (permutation s2 s3)]
  = reveal_opaque (`%permutation) (permutation s1 s2);
    reveal_opaque (`%permutation) (permutation s2 s3);
    reveal_opaque (`%permutation) (permutation s1 s3);
    Seq.perm_len s1 s2;
    Seq.perm_len s1 s3;
    Seq.lemma_trans_perm s1 s2 s3 0 (Seq.length s1)

// ========== Swap lemmas ==========

let lemma_swap_is_two_upds (s: Seq.seq int) (i j: nat)
  : Lemma (requires i < Seq.length s /\ j < Seq.length s /\ i <> j)
          (ensures (let vi = Seq.index s i in
                    let vj = Seq.index s j in
                    let s1 = Seq.upd s i vj in
                    let s2 = Seq.upd s1 j vi in
                    Seq.swap s i j == s2))
  = let vi = Seq.index s i in
    let vj = Seq.index s j in
    let s1 = Seq.upd s i vj in
    let s2 = Seq.upd s1 j vi in
    let sw = Seq.swap s i j in
    let aux (k: nat{k < Seq.length s})
      : Lemma (Seq.index s2 k == Seq.index sw k) = ()
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_elim s2 sw

let swap_is_permutation (s: Seq.seq int) (i j: nat)
  : Lemma (requires i < Seq.length s /\ j < Seq.length s)
          (ensures (let s1 = Seq.upd s i (Seq.index s j) in
                    let s2 = Seq.upd s1 j (Seq.index s i) in
                    permutation s s2))
  = let vi = Seq.index s i in
    let vj = Seq.index s j in
    let s1 = Seq.upd s i vj in
    let s2 = Seq.upd s1 j vi in
    reveal_opaque (`%permutation) (permutation s s2);
    if i = j then (
      Seq.lemma_index_upd1 s i vj;
      Seq.lemma_eq_elim s1 s;
      Seq.lemma_index_upd1 s1 j vi;
      Seq.lemma_eq_elim s2 s1
    ) else (
      lemma_swap_is_two_upds s i j;
      if i < j then Seq.Properties.lemma_swap_permutes s i j
      else Seq.Properties.lemma_swap_permutes s j i
    )

// ========== Partition Preservation Lemmas ==========

// Helper lemma: when we swap a[i] and a[j] where a[j] <= pivot,
// the partition property is preserved
let lemma_swap_preserves_partition_less_equal
  (s: Seq.seq int)
  (pivot: int)
  (i j: nat)
  (vi vj: int)
  : Lemma
    (requires
      i <= j /\ j < Seq.length s /\
      Seq.index s i == vi /\
      Seq.index s j == vj /\
      vj <= pivot /\
      (i < j ==> vi > pivot) /\
      (forall (k: nat). k < i ==> Seq.index s k <= pivot) /\
      (forall (k: nat). i <= k /\ k < j ==> Seq.index s k > pivot))
    (ensures
      (let s1 = Seq.upd s i vj in
       let s2 = Seq.upd s1 j vi in
       (forall (k: nat). k < i + 1 ==> Seq.index s2 k <= pivot) /\
       (forall (k: nat). i + 1 <= k /\ k <= j ==> Seq.index s2 k > pivot)))
  = let s1 = Seq.upd s i vj in
    let s2 = Seq.upd s1 j vi in
    ()

// Helper lemma: when a[j] > pivot, no swap happens, partition property is preserved
let lemma_no_swap_preserves_partition
  (s: Seq.seq int)
  (pivot: int)
  (i j: nat)
  (vj: int)
  : Lemma
    (requires
      i <= j /\ j < Seq.length s /\
      Seq.index s j == vj /\
      vj > pivot /\
      (forall (k: nat). k < i ==> Seq.index s k <= pivot) /\
      (forall (k: nat). i <= k /\ k < j ==> Seq.index s k > pivot))
    (ensures
      (forall (k: nat). k < i ==> Seq.index s k <= pivot) /\
      (forall (k: nat). i <= k /\ k <= j ==> Seq.index s k > pivot))
  = ()

// ========== Complexity bound predicate ==========
let complexity_bounded_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n

// ========== Main Algorithm with Complexity ==========

//SNIPPET_START: partition_sig
fn partition
  (a: A.array int)
  (n: SZ.t)
  (pivot: int)
  (#s0: erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
requires
  A.pts_to a s0 ** GR.pts_to ctr c0 **
  pure (
    SZ.v n <= A.length a /\
    SZ.v n == Seq.length s0 /\
    Seq.length s0 == A.length a /\
    (forall (i: nat). i < Seq.length s0 ==> Seq.index s0 i >= 0)
  )
returns result:SZ.t
ensures exists* s (cf: nat).
  A.pts_to a s ** GR.pts_to ctr cf **
  pure (
    Seq.length s == Seq.length s0 /\
    SZ.v result <= SZ.v n /\
    permutation s0 s /\
    is_partitioned s pivot (SZ.v result) /\
    complexity_bounded_linear cf (reveal c0) (SZ.v n)
  )
//SNIPPET_END: partition_sig
{
  let mut i: SZ.t = 0sz;
  let mut j: SZ.t = 0sz;
  
  while (!j <^ n)
  invariant exists* vi vj s_cur (vc: nat).
    R.pts_to i vi **
    R.pts_to j vj **
    A.pts_to a s_cur **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v vj /\
      SZ.v vj <= SZ.v n /\
      SZ.v vi <= SZ.v n /\
      Seq.length s_cur == Seq.length s0 /\
      Seq.length s_cur == A.length a /\
      permutation s0 s_cur /\
      (forall (k: nat). k < SZ.v vi ==> Seq.index s_cur k <= pivot) /\
      (forall (k: nat). SZ.v vi <= k /\ k < SZ.v vj ==> Seq.index s_cur k > pivot) /\
      // Complexity: exactly vj comparisons so far (relative to c0)
      vc == reveal c0 + SZ.v vj
    )
  {
    let vj = !j;
    let vi = !i;
    
    // Always increment j first
    j := vj + 1sz;
    
    with s_before. assert (A.pts_to a s_before);
    
    // Read both values
    let aj = a.(vj);
    let ai = a.(vi);
    
    // Determine if we should swap - THIS IS THE COMPARISON
    let should_swap = (aj <= pivot);
    
    // Tick for the comparison
    tick ctr;
    
    // Unconditional writes with conditional values
    let new_ai = (if should_swap then aj else ai);
    let new_aj = (if should_swap then ai else aj);
    a.(vi) <- new_ai;
    a.(vj) <- new_aj;
    
    with s_after. assert (A.pts_to a s_after);
    
    // Prove partition invariant is maintained
    if (should_swap) {
      swap_is_permutation s_before (SZ.v vi) (SZ.v vj);
      lemma_swap_preserves_partition_less_equal s_before pivot (SZ.v vi) (SZ.v vj) ai aj;
      i := vi + 1sz;
      ()
    } else {
      assert (pure (new_ai == ai /\ new_aj == aj));
      assert (pure (Seq.equal s_after s_before));
      lemma_no_swap_preserves_partition s_before pivot (SZ.v vi) (SZ.v vj) aj;
      ()
    }
  };
  
  // At loop exit: vj == n, so cf == c0 + n
  !i
}
