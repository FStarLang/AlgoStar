(*
   Radix Sort - Verified implementation in Pulse
   
   CLRS RADIX-SORT (Section 8.3) for d-digit numbers sorts by digit
   using a stable sort subroutine:
   
     RADIX-SORT(A, d)
       for i = 1 to d
         use a stable sort to sort array A on digit i
   
   Two variants:
   1. radix_sort: Single-digit (d=1) using counting_sort_inplace
   2. radix_sort_multidigit: Multi-digit using counting_sort_by_digit
   
   Proves:
   1. The result is sorted
   2. The result is a permutation of the input
   
   NO admits. NO assumes.
*)

module CLRS.Ch08.RadixSort
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module R = Pulse.Lib.Reference
module Impl = CLRS.Ch08.CountingSort.Impl
module S = CLRS.Ch08.CountingSort.Spec
module B = CLRS.Ch08.RadixSort.Base
module Stab = CLRS.Ch08.RadixSort.Stability
module FS = CLRS.Ch08.RadixSort.FullSort
module Bridge = CLRS.Ch08.RadixSort.Bridge

// ========== Single-digit variant ==========

//SNIPPET_START: radix_sort_sig
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
fn radix_sort
  (a: A.array nat)
  (len: SZ.t)
  (k_val: SZ.t)
  (#s0: erased (Seq.seq nat))
requires
  A.pts_to a s0 **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len == Seq.length s0 /\
    Seq.length s0 == A.length a /\
    S.in_range s0 (SZ.v k_val) /\
    SZ.fits (SZ.v k_val + 2) /\
    SZ.fits (SZ.v len + SZ.v k_val + 2)
  )
ensures exists* s.
  A.pts_to a s **
  pure (
    Seq.length s == Seq.length s0 /\
    S.sorted s /\
    S.permutation s0 s
  )
//SNIPPET_END: radix_sort_sig
{
  // d=1: one pass of in-place counting sort
  Impl.counting_sort_inplace a len k_val
}
#pop-options

// ========== Multi-digit variant ==========
// CLRS RADIX-SORT: for i = 1 to d, stable sort on digit i
// Uses counting_sort_by_digit as the stable subroutine.
// Correctness from RadixSort.Stability and RadixSort.FullSort.

//SNIPPET_START: radix_sort_multidigit_sig
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
fn radix_sort_multidigit
  (a: A.array nat)
  (len: SZ.t)
  (base_val: SZ.t)     // Base for digit extraction (>= 2)
  (bigD: SZ.t)          // Number of digits
  (#s0: erased (Seq.seq nat))
requires
  A.pts_to a s0 **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len == Seq.length s0 /\
    Seq.length s0 == A.length a /\
    SZ.v base_val >= 2 /\
    SZ.v bigD > 0 /\
    // All elements fit in bigD digits
    (forall (i: nat). i < Seq.length s0 ==> Seq.index s0 i < B.pow (SZ.v base_val) (SZ.v bigD)) /\
    SZ.fits (SZ.v base_val + 2) /\
    SZ.fits (SZ.v len + SZ.v base_val + 2)
  )
ensures exists* s.
  A.pts_to a s **
  pure (
    Seq.length s == Seq.length s0 /\
    S.sorted s /\
    S.permutation s0 s
  )
//SNIPPET_END: radix_sort_multidigit_sig
{
  if (len = 0sz) {
    // Empty array: trivially sorted and a permutation of itself
    Bridge.base_sorted_implies_l_sorted s0;
    Bridge.base_perm_implies_s_perm s0 s0;
    ()
  } else {
  // Allocate temporary buffer b
  let b = A.alloc (0 <: nat) len;

  // Mutable digit counter
  let d = R.alloc 0sz;

  // Main loop: for d = 0 to bigD - 1
  while (
    let vd = !d;
    (vd <^ bigD)
  )
  invariant exists* vd s_curr sb_curr.
    R.pts_to d vd **
    A.pts_to a s_curr **
    A.pts_to b sb_curr **
    pure (
      SZ.v vd <= SZ.v bigD /\
      Seq.length s_curr == SZ.v len /\
      Seq.length s_curr == A.length a /\
      Seq.length sb_curr == SZ.v len /\
      Seq.length sb_curr == A.length b /\
      A.length b == SZ.v len /\
      B.permutation s0 s_curr /\
      (SZ.v vd = 0 \/ Stab.sorted_up_to_digit s_curr (SZ.v vd - 1) (SZ.v base_val)) /\
      (forall (i: nat). i < Seq.length s_curr ==> Seq.index s_curr i < B.pow (SZ.v base_val) (SZ.v bigD)) /\
      SZ.v len > 0 /\
      SZ.v len <= A.length a /\
      SZ.v len <= A.length b /\
      SZ.v base_val >= 2 /\
      SZ.fits (SZ.v base_val + 2) /\
      SZ.fits (SZ.v len + SZ.v base_val + 2)
    )
  {
    let vd = !d;
    with s_curr. assert (A.pts_to a s_curr);
    with sb_curr. assert (A.pts_to b sb_curr);
    
    // Share a's permission for the read-only call
    A.share a;
    
    // Call counting_sort_by_digit: sorts a into b by digit vd
    Impl.counting_sort_by_digit a b len base_val (SZ.v vd);
    
    // After call: b has stable sort on digit vd
    with sb'. assert (A.pts_to b sb');
    
    // Gather a's permission back to full
    A.gather a;
    
    // Copy b back to a for next iteration
    A.memcpy len b a;
    
    // Now a contains sb' (the sorted result)
    // Extract stability property
    Stab.is_stable_get_perm s_curr sb' (SZ.v vd) (SZ.v base_val);
    
    // Maintain overall permutation: s0 ~perm~ s_curr ~perm~ sb'
    B.permutation_transitive s0 s_curr sb';
    
    // Maintain sorted_up_to_digit invariant
    Stab.lemma_stable_pass_preserves_ordering s_curr sb' (SZ.v vd) (SZ.v base_val);
    
    // Maintain bounds
    B.permutation_preserves_bounds s_curr sb' (B.pow (SZ.v base_val) (SZ.v bigD));
    
    // Increment digit counter
    d := vd +^ 1sz;
  };
  
  // After loop: d == bigD
  with s_final. assert (A.pts_to a s_final);

  // sorted_up_to_digit s_final (bigD-1) base + all elements < pow base bigD
  // => B.sorted s_final
  FS.lemma_sorted_up_to_all_digits_implies_sorted s_final (SZ.v bigD) (SZ.v base_val);
  
  // Bridge to S.sorted and S.permutation
  Bridge.base_sorted_implies_l_sorted s_final;
  Bridge.base_perm_implies_s_perm s0 s_final;
  
  // Free temporary resources
  with sb_final. assert (A.pts_to b sb_final);
  A.free b;
  R.free d;
  ()
  } // else len > 0
}
#pop-options
