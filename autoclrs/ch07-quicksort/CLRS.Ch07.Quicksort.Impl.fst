(*
   CLRS Chapter 7: Quicksort — Pulse Implementation

   Implements the CLRS quicksort algorithm (§7.1) with full
   functional correctness and worst-case O(n²) complexity analysis.

   Key results:
   1. Partition correctness: elements ≤ pivot before split, > pivot after
   2. Quicksort correctness: output is sorted permutation of input
   3. Partition is Θ(n) - exactly n-1 comparisons (all elements except pivot)
   4. Worst-case recurrence: T(n) = T(n-1) + (n-1) when partition is maximally unbalanced
   5. Closed form: T(n) ≤ n(n-1)/2 = O(n²)

   The tick counter is threaded through all recursive calls using GhostReference
   to track cumulative operations without runtime overhead.

   NO admits. NO assumes.
*)
module CLRS.Ch07.Quicksort.Impl
#lang-pulse

open Pulse.Lib.Pervasives
open CLRS.Ch07.Partition.Lemmas
open CLRS.Ch07.Partition.Impl
open CLRS.Ch07.Quicksort.Lemmas
open CLRS.Common.SortSpec
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Internal spec predicates ==========

unfold
let pure_pre_quicksort (a: A.array int) (lo: nat) (hi:(hi:nat{lo <= hi})) (lb rb: int) (s0: Seq.seq int)
  = hi <= A.length a /\
    between_bounds s0 lb rb /\
    Seq.length s0 = hi - lo /\
    lo <= A.length a /\
    lb <= rb

unfold
let pure_post_quicksort (a: A.array int) (lo: nat) (hi:(hi:nat{lo <= hi})) (lb rb: int) (s0 s: Seq.seq int)
  = hi <= A.length a /\
    Seq.length s0 = hi - lo /\
    Seq.length s = hi - lo /\
    sorted s /\
    between_bounds s lb rb /\
    permutation s0 s

// ========== Ghost proof function ==========

ghost
fn quicksort_proof
  (a: A.array int)
  (lo: nat)
  (p: (p:nat{lo <= p}))
  (hi:(hi:nat{p < hi}))
  (lb rb pivot_val: int)
  (#s0: erased (Seq.seq int))
  (s_left s_pivot s_right : Seq.seq int)
  requires
    (exists* s_left'. (A.pts_to_range a lo p s_left' ** pure (pure_post_quicksort a lo p lb pivot_val s_left s_left'))) **
    (exists* s_right'. (A.pts_to_range a (p+1) hi s_right' ** pure (pure_post_quicksort a (p+1) hi pivot_val rb s_right s_right'))) **
    A.pts_to_range a p (p+1) s_pivot **
    pure (Seq.length s0 == hi - lo
          /\ Seq.length s_pivot == 1
          /\ lb <= pivot_val /\ pivot_val <= rb
          /\ Seq.index s_pivot 0 == pivot_val
          /\ permutation s0 (Seq.append s_left (Seq.append s_pivot s_right)))
  ensures
    exists* s.
      A.pts_to_range a lo hi s **
      pure (pure_post_quicksort a lo hi lb rb s0 s)
{
  with s_left'. assert (A.pts_to_range a lo p s_left');
  with s_right'. assert (A.pts_to_range a (p+1) hi s_right');

  pts_to_range_join a p (p+1) hi;
  pts_to_range_join a lo p hi;

  let _ = append_permutations_3_squash s_left s_pivot s_right s_left' s_right' ();
  let _ = lemma_sorted_append_squash s_pivot s_right' pivot_val pivot_val pivot_val rb ();
  let _ = lemma_sorted_append_squash s_left' (Seq.append s_pivot s_right') lb pivot_val pivot_val rb ();
  ()
}

// ========== Quicksort with Tick Counter ==========

//SNIPPET_START: clrs_quicksort_with_ticks_sig
fn rec clrs_quicksort_with_ticks
  (a: A.array int) 
  (lo: nat) 
  (hi:(hi:nat{lo <= hi})) 
  (lb rb: erased int) 
  (#s0: Ghost.erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to_range a lo hi s0 **
    GR.pts_to ctr c0 **
    pure (pure_pre_quicksort a lo hi lb rb s0)
  ensures exists* s (cf: nat).
    A.pts_to_range a lo hi s **
    GR.pts_to ctr cf **
    pure (
      pure_post_quicksort a lo hi lb rb s0 s /\
      complexity_bounded_quadratic cf (reveal c0) (hi - lo)
    )
//SNIPPET_END: clrs_quicksort_with_ticks_sig
{
  if (lo < hi)
  {
    let p = clrs_partition_wrapper_with_ticks a lo hi lb rb ctr;
    
    with s_left. assert (A.pts_to_range a lo p s_left);
    with s_pivot. assert (A.pts_to_range a p (p+1) s_pivot);
    with s_right. assert (A.pts_to_range a (p+1) hi s_right);
    with c_after_partition. assert (GR.pts_to ctr c_after_partition);
    
    // Recursively sort left partition
    clrs_quicksort_with_ticks a lo p lb (hide (Seq.index s_pivot 0)) ctr #c_after_partition;
    
    with c_after_left. assert (GR.pts_to ctr c_after_left);
    
    // Recursively sort right partition
    clrs_quicksort_with_ticks a (p+1) hi (hide (Seq.index s_pivot 0)) rb ctr #c_after_left;
    
    with s_left'. assert (A.pts_to_range a lo p s_left');
    with s_right'. assert (A.pts_to_range a (p+1) hi s_right');
    with c_final. assert (GR.pts_to ctr c_final);
    
    let _ = append_permutations_3_squash s_left s_pivot s_right s_left' s_right' ();

    quicksort_proof a lo p hi lb rb (Seq.index s_pivot 0) #s0 s_left' s_pivot s_right';
    
    // Prove complexity bound
    lemma_quicksort_complexity_bound (hi - lo) (p - lo) (hi - (p + 1)) (hi - lo - 1);
    assert (pure (complexity_bounded_quadratic c_final (reveal c0) (hi - lo)));
    ()
  }
  else
  {
    // Base case: empty range, no operations
    ()
  }
}

// ========== Top-level API ==========

// Internal wrapper: creates ghost counter, calls ticked version, frees counter
fn clrs_quicksort
  (a: A.array int) 
  (lo: nat) 
  (hi:(hi:nat{lo <= hi})) 
  (lb rb: erased int) 
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a lo hi s0 ** pure (pure_pre_quicksort a lo hi lb rb s0)
  ensures exists* s. (A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s))
{
  let ctr = GR.alloc #nat 0;
  clrs_quicksort_with_ticks a lo hi lb rb #s0 ctr #(hide 0);
  with s_out. assert (A.pts_to_range a lo hi s_out);
  with cf_out. assert (GR.pts_to ctr cf_out);
  GR.free ctr
}

// Variant that exposes the worst-case O(n²) complexity bound via ghost counter.
fn quicksort_with_complexity
  (a: A.array int)
  (len: SZ.t)
  (#s0: Ghost.erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a s0 ** GR.pts_to ctr c0
  requires pure (Seq.length s0 == A.length a /\ A.length a == SZ.v len)
  ensures exists* s (cf: nat). (
    A.pts_to a s ** GR.pts_to ctr cf **
    pure (sorted s /\ permutation s0 s /\
          complexity_bounded_quadratic cf (reveal c0) (SZ.v len)))
{
  if (SZ.gt len 1sz) {
    A.pts_to_range_intro a 1.0R s0;
    
    lemma_between_bounds_from_min_max s0;
    lemma_min_le_max s0;
    
    clrs_quicksort_with_ticks a 0 (SZ.v len) (hide (seq_min s0)) (hide (seq_max s0)) ctr;
    
    with s'. assert (A.pts_to_range a 0 (A.length a) s');
    A.pts_to_range_elim a 1.0R s';
    ()
  } else {
    ()
  }
}

fn quicksort 
  (a: A.array int)
  (len: SZ.t)
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to a s0
  requires pure (Seq.length s0 == A.length a /\ A.length a == SZ.v len)
  ensures exists* s. (A.pts_to a s ** pure (sorted s /\ permutation s0 s))
{
  if (SZ.gt len 1sz) {
    A.pts_to_range_intro a 1.0R s0;
    
    lemma_between_bounds_from_min_max s0;
    lemma_min_le_max s0;
    
    clrs_quicksort a 0 (SZ.v len) (hide (seq_min s0)) (hide (seq_max s0));
    
    with s'. assert (A.pts_to_range a 0 (A.length a) s');
    A.pts_to_range_elim a 1.0R s';
    ()
  } else {
    ()
  }
}

fn quicksort_bounded
  (a: A.array int)
  (lo: nat)
  (hi: (hi:nat{lo <= hi}))
  (lb rb: erased int)
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a lo hi s0
  requires pure (
    hi <= A.length a /\
    Seq.length s0 = hi - lo /\
    between_bounds s0 lb rb /\
    lb <= rb
  )
  ensures exists* s. (
    A.pts_to_range a lo hi s **
    pure (sorted s /\ permutation s0 s /\ between_bounds s lb rb)
  )
{
  clrs_quicksort a lo hi lb rb
}
