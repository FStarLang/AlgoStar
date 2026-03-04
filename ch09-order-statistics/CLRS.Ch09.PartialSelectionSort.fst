(*
   Selection Algorithm - Verified implementation in Pulse
   
   Implements the k-th smallest element finder using partial selection sort.
   
   CLRS Chapter 9 presents:
   - RANDOMIZED-SELECT: O(n) expected via randomized partitioning (§9.2)
   - SELECT (median-of-medians): O(n) worst case (§9.3)
   
   This implementation uses partial selection sort: O(nk) worst case.
   For k = O(1), this matches CLRS. For k = n/2 (median), this is O(n²)
   while CLRS algorithms are O(n). See Select.Complexity.fst for analysis.
   
   Algorithm:
   - For each round i from 0 to k-1:
     - Find the index of the minimum element in a[i..n-1]
     - Swap a[i] with the minimum element
   - Return a[k-1]
   
   After k rounds, the first k elements are the k smallest elements in sorted order,
   and a[k-1] contains the k-th smallest element.
   
   Verification Status:
   - NO admits, NO assumes ✓
   - Correctness properties proven:
     * The output array is a permutation of the input ✓
     * sorted_prefix: s_final[0..k-1] is sorted ✓
     * prefix_leq_suffix: all elements in [0,k) are ≤ all in [k,n) ✓
     * Together these imply s_final[k-1] is the k-th smallest element ✓
   
   Limitation: Uses O(nk) partial selection sort instead of CLRS's O(n) algorithms.
   Implementing RANDOMIZED-SELECT requires a random number source.
   Implementing median-of-medians SELECT requires recursive partitioning with
   median-of-5 groups, which is a significant implementation effort.
*)

module CLRS.Ch09.PartialSelectionSort
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Classical = FStar.Classical
module GR = Pulse.Lib.GhostReference

// ========== Definitions ==========

//SNIPPET_START: selection_defs
// Permutation: make opaque for SMT performance
[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)

// Predicate: index i has a minimum value in range [start, len)
let is_min_in_range (s: Seq.seq int) (i: nat) (start: nat) (len: nat) : prop =
  start <= i /\ i < len /\ len <= Seq.length s /\
  (forall (j: nat). start <= j /\ j < len ==> Seq.index s i <= Seq.index s j)

// sorted_prefix: s[0..bound-1] is sorted
let sorted_prefix (s: Seq.seq int) (bound: nat) : prop =
  bound <= Seq.length s /\
  (forall (i j: nat). i < j /\ j < bound ==> Seq.index s i <= Seq.index s j)

// prefix_leq_suffix: all elements in [0,bound) are <= all elements in [bound, len)
let prefix_leq_suffix (s: Seq.seq int) (bound: nat) : prop =
  bound <= Seq.length s /\
  (forall (i j: nat). i < bound /\ bound <= j /\ j < Seq.length s ==>
    Seq.index s i <= Seq.index s j)
//SNIPPET_END: selection_defs


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

// ========== Helper: Find index of minimum in range [start, len) ==========
// Scans the array from start to len-1 and returns the index of an element
// that is <= all other elements in that range.
// Proves: the returned index points to a minimum value in the range.

#push-options "--z3rlimit 50 --ifuel 2 --fuel 2"
fn find_min_index_from
  (#p: perm)
  (a: array int)
  (#s: Ghost.erased (Seq.seq int))
  (start: SZ.t)
  (len: SZ.t)
  requires A.pts_to a #p s
  requires pure (
    SZ.v start < SZ.v len /\
    SZ.v len == Seq.length s /\
    SZ.v len == A.length a
  )
  returns min_idx: SZ.t
  ensures A.pts_to a #p s ** pure (
    SZ.v start <= SZ.v min_idx /\
    SZ.v min_idx < SZ.v len /\
    is_min_in_range s (SZ.v min_idx) (SZ.v start) (SZ.v len)
  )
{
  let mut min_idx: SZ.t = start;
  let mut i: SZ.t = start + 1sz;
  
  while (!i <^ len)
  invariant exists* vi vmin_idx.
    R.pts_to i vi **
    R.pts_to min_idx vmin_idx **
    pure (
      SZ.v vi > SZ.v start /\
      SZ.v vi <= SZ.v len /\
      SZ.v start <= SZ.v vmin_idx /\
      SZ.v vmin_idx < SZ.v len /\
      SZ.v vmin_idx < SZ.v vi /\
      // min_idx is minimum in [start, vi)
      (forall (j: nat). SZ.v start <= j /\ j < SZ.v vi ==>
        Seq.index s (SZ.v vmin_idx) <= Seq.index s j)
    )
  decreases (SZ.v len `Prims.op_Subtraction` SZ.v !i)
  {
    let vi = !i;
    let vmin_idx = !min_idx;
    let curr = a.(vi);
    let min_val = a.(vmin_idx);
    
    if (curr < min_val) {
      min_idx := vi;
    };
    
    i := vi + 1sz;
  };
  
  !min_idx
}
#pop-options

// ========== Main Selection Algorithm ==========
// Uses partial selection sort: perform k rounds of min-finding and swapping.
//
// Proves:
// 1. The output array is a permutation of the input
// 2. The returned result equals the value at position k-1 in the final array
//
// The algorithm is a verified implementation of the selection algorithm from
// CLRS Chapter 9, using the simple O(n²) approach of partial selection sort.

#push-options "--z3rlimit 10 --ifuel 2 --fuel 2"
//SNIPPET_START: select
fn select
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (k: SZ.t)
  requires A.pts_to a s0
  requires pure (
    SZ.v n == Seq.length s0 /\
    SZ.v n == A.length a /\
    SZ.v n > 0 /\
    SZ.v k > 0 /\
    SZ.v k <= SZ.v n
  )
  returns result: int
  ensures exists* s_final.
    A.pts_to a s_final **
    pure (
      Seq.length s_final == Seq.length s0 /\
      permutation s0 s_final /\
      sorted_prefix s_final (SZ.v k) /\
      prefix_leq_suffix s_final (SZ.v k) /\
      SZ.v k > 0 /\
      result == Seq.index s_final (SZ.v k `Prims.op_Subtraction` 1)
    )
//SNIPPET_END: select
{
  let mut round: SZ.t = 0sz;
  
  while (!round <^ k)
  invariant exists* vround s_curr.
    R.pts_to round vround **
    A.pts_to a s_curr **
    pure (
      SZ.v vround <= SZ.v k /\
      Seq.length s_curr == Seq.length s0 /\
      permutation s0 s_curr /\
      sorted_prefix s_curr (SZ.v vround) /\
      prefix_leq_suffix s_curr (SZ.v vround)
    )
  decreases (SZ.v k `Prims.op_Subtraction` SZ.v !round)
  {
    let vround = !round;
    with s_pre. assert (A.pts_to a s_pre);
    
    // Find minimum in range [vround, n)
    let min_idx = find_min_index_from a vround n;
    
    // Swap element at vround with element at min_idx
    let val_round = a.(vround);
    let val_min = a.(min_idx);
    
    a.(vround) <- val_min;
    a.(min_idx) <- val_round;
    
    with s_post. assert (A.pts_to a s_post);
    swap_is_permutation s_pre (SZ.v vround) (SZ.v min_idx);
    
    round := vround + 1sz;
  };
  
  // Return the k-th element (at index k-1)
  let idx = k - 1sz;
  with s_arr. assert (A.pts_to a s_arr);
  let value = a.(idx);
  assert (pure (value == Seq.index s_arr (SZ.v idx)));
  value
}
#pop-options

// ========== Ghost tick for comparison counting ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

let incr_nat_reveal (n: erased nat)
  : Lemma (reveal (incr_nat n) == reveal n + 1)
    [SMTPat (incr_nat n)]
  = ()

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Complexity-tracked find_min_index_from ==========

#push-options "--z3rlimit 50 --ifuel 2 --fuel 2"
fn find_min_index_from_complexity
  (#p: perm)
  (a: array int)
  (#s: Ghost.erased (Seq.seq int))
  (start: SZ.t)
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s ** GR.pts_to ctr c0 **
    pure (
      SZ.v start < SZ.v len /\
      SZ.v len == Seq.length s /\
      SZ.v len == A.length a
    )
  returns min_idx: SZ.t
  ensures exists* (cf: nat).
    A.pts_to a #p s ** GR.pts_to ctr cf **
    pure (
      SZ.v start <= SZ.v min_idx /\
      SZ.v min_idx < SZ.v len /\
      is_min_in_range s (SZ.v min_idx) (SZ.v start) (SZ.v len) /\
      cf >= reveal c0 /\
      cf - reveal c0 == SZ.v len - SZ.v start - 1
    )
{
  let mut min_idx: SZ.t = start;
  let mut i: SZ.t = start + 1sz;
  
  while (!i <^ len)
  invariant exists* vi vmin_idx (vc: nat).
    R.pts_to i vi **
    R.pts_to min_idx vmin_idx **
    GR.pts_to ctr vc **
    A.pts_to a #p s **
    pure (
      SZ.v vi > SZ.v start /\
      SZ.v vi <= SZ.v len /\
      SZ.v start <= SZ.v vmin_idx /\
      SZ.v vmin_idx < SZ.v len /\
      SZ.v vmin_idx < SZ.v vi /\
      (forall (j: nat). SZ.v start <= j /\ j < SZ.v vi ==>
        Seq.index s (SZ.v vmin_idx) <= Seq.index s j) /\
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi - SZ.v start - 1
    )
  decreases (SZ.v len `Prims.op_Subtraction` SZ.v !i)
  {
    let vi = !i;
    let vmin_idx = !min_idx;
    let curr = a.(vi);
    let min_val = a.(vmin_idx);
    
    tick ctr;
    if (curr < min_val) {
      min_idx := vi;
    };
    
    i := vi + 1sz;
  };
  
  !min_idx
}
#pop-options

// ========== Complexity-tracked select ==========

let complexity_bounded_select (cf c0 n k: nat) : prop =
  k > 0 /\ k <= n /\ n > 0 /\
  cf >= c0 /\
  cf - c0 <= op_Multiply k (n - 1)

#push-options "--z3rlimit 20 --ifuel 2 --fuel 2"
fn select_complexity
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (k: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s0 /\
      SZ.v n == A.length a /\
      SZ.v n > 0 /\
      SZ.v k > 0 /\
      SZ.v k <= SZ.v n
    )
  returns result: int
  ensures exists* s_final (cf: nat).
    A.pts_to a s_final ** GR.pts_to ctr cf **
    pure (
      Seq.length s_final == Seq.length s0 /\
      permutation s0 s_final /\
      sorted_prefix s_final (SZ.v k) /\
      prefix_leq_suffix s_final (SZ.v k) /\
      SZ.v k > 0 /\
      result == Seq.index s_final (SZ.v k `Prims.op_Subtraction` 1) /\
      complexity_bounded_select cf (reveal c0) (SZ.v n) (SZ.v k)
    )
{
  let mut round: SZ.t = 0sz;
  
  while (!round <^ k)
  invariant exists* vround s_curr (vc: nat).
    R.pts_to round vround **
    A.pts_to a s_curr **
    GR.pts_to ctr vc **
    pure (
      SZ.v vround <= SZ.v k /\
      Seq.length s_curr == Seq.length s0 /\
      permutation s0 s_curr /\
      sorted_prefix s_curr (SZ.v vround) /\
      prefix_leq_suffix s_curr (SZ.v vround) /\
      vc >= reveal c0 /\
      vc - reveal c0 <= op_Multiply (SZ.v vround) (SZ.v n - 1)
    )
  decreases (SZ.v k `Prims.op_Subtraction` SZ.v !round)
  {
    let vround = !round;
    with s_pre. assert (A.pts_to a s_pre);
    
    let min_idx = find_min_index_from_complexity a vround n ctr;
    
    let val_round = a.(vround);
    let val_min = a.(min_idx);
    
    a.(vround) <- val_min;
    a.(min_idx) <- val_round;
    
    with s_post. assert (A.pts_to a s_post);
    swap_is_permutation s_pre (SZ.v vround) (SZ.v min_idx);
    
    round := vround + 1sz;
  };
  
  let idx = k - 1sz;
  with s_arr. assert (A.pts_to a s_arr);
  let value = a.(idx);
  assert (pure (value == Seq.index s_arr (SZ.v idx)));
  value
}
#pop-options
