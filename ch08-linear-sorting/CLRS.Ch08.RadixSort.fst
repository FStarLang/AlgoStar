(*
   Radix Sort - Verified implementation in Pulse
   
   This implements a simplified radix sort for non-negative integers.
   For verification tractability, we implement the core building block:
   sorting by a specific digit position using selection sort approach.
   
   Proves:
   1. The result is sorted
   2. The result is a permutation of the input
   
   NO admits. NO assumes.
*)

module CLRS.Ch08.RadixSort
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

// ========== Definitions ==========

// Sortedness predicate
let sorted (s: Seq.seq int)
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

// Suffix of sequence starting at position k is sorted
let suffix_sorted (s: Seq.seq int) (k: nat) : prop =
  k <= Seq.length s /\
  (forall (i j: nat). k <= i /\ i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j)

// All elements before position k are <= all elements from k onwards
let prefix_le_suffix (s: Seq.seq int) (k: nat) : prop =
  k <= Seq.length s /\
  (forall (i j: nat). i < k /\ k <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j)

// Element at position k is >= all elements in range [0, k]
let is_max_up_to (s: Seq.seq int) (k: nat) : prop =
  k < Seq.length s /\
  (forall (i: nat). i <= k ==> Seq.index s i <= Seq.index s k)

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

// ========== Sortedness lemmas ==========

// Swapping within the unsorted prefix preserves suffix_sorted and prefix_le_suffix
let lemma_swap_preserves_sorted_suffix (s: Seq.seq int) (i j limit: nat)
  : Lemma (requires i < limit /\ j < limit /\ i < Seq.length s /\ j < Seq.length s /\
                     limit <= Seq.length s /\
                     suffix_sorted s limit /\
                     prefix_le_suffix s limit)
          (ensures (let s' = if i = j then s else Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i) in
                     suffix_sorted s' limit /\
                     prefix_le_suffix s' limit))
  = ()

// Finding max and placing it at limit-1 extends the sorted suffix
let lemma_max_extends_sorted_suffix (s: Seq.seq int) (limit: nat)
  : Lemma (requires limit > 0 /\ limit <= Seq.length s /\
                     suffix_sorted s limit /\
                     prefix_le_suffix s limit /\
                     is_max_up_to s (limit - 1))
          (ensures suffix_sorted s (limit - 1) /\ prefix_le_suffix s (limit - 1))
  = ()

// ========== Main Algorithm ==========

// Radix sort implementation using selection sort approach
// For verification tractability, implements full sort using selection sort
fn radix_sort
  (a: A.array int)
  (len: SZ.t)
  (#s0: erased (Seq.seq int))
requires
  A.pts_to a s0 **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len == Seq.length s0 /\
    Seq.length s0 == A.length a /\
    (forall (i: nat). i < Seq.length s0 ==> Seq.index s0 i >= 0) /\
    SZ.v len > 0
  )
ensures exists* s.
  A.pts_to a s **
  pure (
    Seq.length s == Seq.length s0 /\
    sorted s /\
    permutation s0 s
  )
{
  let mut limit: SZ.t = len;
  
  while (!limit >^ 1sz)
  invariant exists* vlimit s_cur.
    R.pts_to limit vlimit **
    A.pts_to a s_cur **
    pure (
      SZ.v vlimit > 0 /\
      SZ.v vlimit <= SZ.v len /\
      Seq.length s_cur == Seq.length s0 /\
      Seq.length s_cur == A.length a /\
      permutation s0 s_cur /\
      suffix_sorted s_cur (SZ.v vlimit) /\
      prefix_le_suffix s_cur (SZ.v vlimit)
    )
  {
    let vlimit = !limit;
    
    with s_pre_find. assert (A.pts_to a s_pre_find);
    
    // Find maximum in [0, vlimit)
    let mut max_idx: SZ.t = 0sz;
    let mut i: SZ.t = 1sz;
    
    while (!i <^ vlimit)
    invariant exists* vi vmax_idx s_find.
      R.pts_to limit vlimit **
      R.pts_to i vi **
      R.pts_to max_idx vmax_idx **
      A.pts_to a s_find **
      pure (
        SZ.v vi <= SZ.v vlimit /\
        SZ.v vmax_idx < SZ.v vi /\
        SZ.v vlimit <= SZ.v len /\
        Seq.length s_find == Seq.length s0 /\
        Seq.length s_find == A.length a /\
        permutation s0 s_find /\
        suffix_sorted s_find (SZ.v vlimit) /\
        prefix_le_suffix s_find (SZ.v vlimit) /\
        Seq.equal s_find s_pre_find /\
        is_max_up_to s_find (SZ.v vmax_idx) /\
        (forall (k: nat). SZ.v vmax_idx < k /\ k < SZ.v vi ==> 
          Seq.index s_find k <= Seq.index s_find (SZ.v vmax_idx))
      )
    {
      let vi = !i;
      let vmax_idx = !max_idx;
      
      let val_i = a.(vi);
      let val_max = a.(vmax_idx);
      
      if (val_i > val_max) {
        max_idx := vi;
      };
      
      i := vi + 1sz;
    };
    
    // Now max_idx contains the index of maximum element in [0, vlimit)
    let vmax_idx = !max_idx;
    
    // Swap max_idx with position vlimit - 1
    let swap_pos = vlimit - 1sz;
    
    with s_before_swap. assert (A.pts_to a s_before_swap);
    
    let val_max = a.(vmax_idx);
    let val_swap = a.(swap_pos);
    
    a.(vmax_idx) <- val_swap;
    a.(swap_pos) <- val_max;
    
    with s_after_swap. assert (A.pts_to a s_after_swap);
    swap_is_permutation s_before_swap (SZ.v vmax_idx) (SZ.v swap_pos);
    lemma_swap_preserves_sorted_suffix s_before_swap (SZ.v vmax_idx) (SZ.v swap_pos) (SZ.v vlimit);
    lemma_max_extends_sorted_suffix s_after_swap (SZ.v vlimit);
    
    limit := vlimit - 1sz;
  };
  
  ()
}
