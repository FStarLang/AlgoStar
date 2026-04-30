(*
   CLRS Chapter 6: Heapsort Implementation in Pulse

   Implements the real CLRS heapsort algorithm:
   1. BUILD-MAX-HEAP: bottom-up heapification
   2. Extract-max loop: swap root (max) to end, shrink heap, MAX-HEAPIFY

   Uses max-heap property on int arrays with parent >= children.
   Heap predicates and sift-down lemmas follow standard max-heap
   conventions from CLRS §6.1–6.4, adapted for 0-based indexing.

   Proves:
   1. The result is sorted
   2. The result is a permutation of the input

   NO admits. NO assumes.
*)

module CLRS.Ch06.Heap.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

open CLRS.Ch06.Heap.Spec
open CLRS.Ch06.Heap.Lemmas

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module Classical = FStar.Classical
module CB = CLRS.Ch06.Heap.CostBound

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

ghost
fn tick2 (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (hide (reveal n + 2))
{
  tick ctr;
  tick ctr
}

// ========== MAX-HEAPIFY (sift_down for max-heap) ==========
// CLRS §6.2: MAX-HEAPIFY(A, i)
//
// The `start` ghost parameter is not in CLRS. It tracks the lower bound of
// the "heaps_from" region, allowing max_heapify to prove correctness when
// called from different starting points: build-heap uses start = idx (only
// the subtree rooted at idx and below is heapified so far), while extract-max
// uses start = 0 (the entire prefix is a heap except at the root).
//
// The `SZ.fits (2 * Seq.length s + 2)` precondition ensures that index
// arithmetic for left_idx (2*i+1) and right_idx (2*i+2) cannot overflow
// SizeT, since the maximum computed index is 2*(n-1)+2 = 2*n for an
// array of length n.
//
// The `ctr` ghost counter tracks comparisons: each non-leaf recursive call
// ticks 2 (for the two child comparisons). The total is bounded by
// max_heapify_bound(heap_size, idx) = 2 * log2_floor(heap_size / (idx+1)).

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
fn rec max_heapify
  (a: A.array int) (idx: SZ.t) (heap_size: SZ.t) (start: Ghost.erased nat)
  (ctr: GR.ref nat)
  (#s: erased (Seq.seq int) {
    SZ.v idx < SZ.v heap_size /\
    SZ.v heap_size <= Seq.length s /\
    Seq.length s == A.length a /\
    SZ.fits (op_Star 2 (Seq.length s) + 2)
  })
  (#c0: erased nat)
requires
  A.pts_to a s **
  GR.pts_to ctr c0 **
  pure (
    SZ.v idx >= start /\
    almost_heaps_from s (SZ.v heap_size) start (SZ.v idx) /\
    (SZ.v idx > 0 /\ parent_idx (SZ.v idx) >= start ==>
      (left_idx (SZ.v idx) < SZ.v heap_size ==>
        Seq.index s (parent_idx (SZ.v idx)) >= Seq.index s (left_idx (SZ.v idx))) /\
      (right_idx (SZ.v idx) < SZ.v heap_size ==>
        Seq.index s (parent_idx (SZ.v idx)) >= Seq.index s (right_idx (SZ.v idx))))
  )
ensures exists* s' (cf: nat).
  A.pts_to a s' **
  GR.pts_to ctr cf **
  pure (
    Seq.length s' == Seq.length s /\
    heaps_from s' (SZ.v heap_size) start /\
    permutation s s' /\
    (forall (k:nat). SZ.v heap_size <= k /\ k < Seq.length s ==> Seq.index s' k == Seq.index s k) /\
    cf >= reveal c0 /\
    cf - reveal c0 <= CB.max_heapify_bound (SZ.v heap_size) (SZ.v idx)
  )
{
  let left = SZ.add (SZ.mul 2sz idx) 1sz;
  if (SZ.gte left heap_size) {
    // Leaf: heap_down_at trivially holds, no ticks needed (bound >= 0)
    almost_to_full s (SZ.v heap_size) start (SZ.v idx);
    ()
  } else {
    let right = SZ.add (SZ.mul 2sz idx) 2sz;
    let cur = a.(idx);
    let lv = a.(left);
    if (SZ.lt right heap_size) {
      // Two children
      let rv = a.(right);
      if (lv >= rv) {
        if (lv > cur) {
          sift_down_swap_lemma_from s (SZ.v heap_size) start (SZ.v idx) (SZ.v left);
          grandparent_after_swap_from s (SZ.v heap_size) start (SZ.v idx) (SZ.v left);
          left_idx_inj (SZ.v idx) (SZ.v left);
          let vi = a.(idx);
          let vl = a.(left);
          a.(idx) <- vl;
          a.(left) <- vi;
          with s_after. assert (A.pts_to a s_after);
          swap_is_permutation s (SZ.v idx) (SZ.v left);
          swap_length s (SZ.v idx) (SZ.v left);
          swap_index_i s (SZ.v idx) (SZ.v left);
          tick2 ctr;
          CB.max_heapify_bound_left (SZ.v heap_size) (SZ.v idx);
          max_heapify a left heap_size start ctr #(swap_seq s (SZ.v idx) (SZ.v left))
        } else {
          almost_to_full s (SZ.v heap_size) start (SZ.v idx);
          ()
        }
      } else {
        if (rv > cur) {
          sift_down_swap_lemma_from s (SZ.v heap_size) start (SZ.v idx) (SZ.v right);
          grandparent_after_swap_from s (SZ.v heap_size) start (SZ.v idx) (SZ.v right);
          right_idx_inj (SZ.v idx) (SZ.v right);
          let vi = a.(idx);
          let vr = a.(right);
          a.(idx) <- vr;
          a.(right) <- vi;
          with s_after. assert (A.pts_to a s_after);
          swap_is_permutation s (SZ.v idx) (SZ.v right);
          swap_length s (SZ.v idx) (SZ.v right);
          swap_index_i s (SZ.v idx) (SZ.v right);
          tick2 ctr;
          CB.max_heapify_bound_right (SZ.v heap_size) (SZ.v idx);
          max_heapify a right heap_size start ctr #(swap_seq s (SZ.v idx) (SZ.v right))
        } else {
          almost_to_full s (SZ.v heap_size) start (SZ.v idx);
          ()
        }
      }
    } else {
      // Only left child
      if (lv > cur) {
        sift_down_swap_lemma_from s (SZ.v heap_size) start (SZ.v idx) (SZ.v left);
        grandparent_after_swap_from s (SZ.v heap_size) start (SZ.v idx) (SZ.v left);
        left_idx_inj (SZ.v idx) (SZ.v left);
        let vi = a.(idx);
        let vl = a.(left);
        a.(idx) <- vl;
        a.(left) <- vi;
        with s_after. assert (A.pts_to a s_after);
        swap_is_permutation s (SZ.v idx) (SZ.v left);
        swap_length s (SZ.v idx) (SZ.v left);
        swap_index_i s (SZ.v idx) (SZ.v left);
        tick2 ctr;
        CB.max_heapify_bound_left (SZ.v heap_size) (SZ.v idx);
        max_heapify a left heap_size start ctr #(swap_seq s (SZ.v idx) (SZ.v left))
      } else {
        almost_to_full s (SZ.v heap_size) start (SZ.v idx);
        ()
      }
    }
  }
}
#pop-options

// ========== BUILD-MAX-HEAP ==========

#restart-solver

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
fn build_max_heap
  (a: A.array int)
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#s0: erased (Seq.seq int) {
    SZ.v n > 0 /\
    SZ.v n <= A.length a /\
    Seq.length s0 == A.length a /\
    SZ.fits (op_Star 2 (Seq.length s0) + 2)
  })
  (#c0: erased nat)
requires
  A.pts_to a s0 **
  GR.pts_to ctr c0
ensures exists* s (cf: nat).
  A.pts_to a s **
  GR.pts_to ctr cf **
  pure (
    Seq.length s == Seq.length s0 /\
    SZ.v n <= Seq.length s /\
    is_max_heap s (SZ.v n) /\
    permutation s0 s /\
    (forall (k:nat). SZ.v n <= k /\ k < Seq.length s ==> Seq.index s k == Seq.index s0 k) /\
    SZ.fits (op_Star 2 (Seq.length s) + 2) /\
    cf >= reveal c0 /\
    cf - reveal c0 <= CB.build_cost_bound (SZ.v n)
  )
{
  let half = SZ.div n 2sz;
  let mut i: SZ.t = half;
  
  while (!i >^ 0sz)
  invariant exists* vi s_cur (vc: nat).
    R.pts_to i vi **
    A.pts_to a s_cur **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v half /\
      Seq.length s_cur == Seq.length s0 /\
      Seq.length s_cur == A.length a /\
      permutation s0 s_cur /\
      (forall (k:nat). SZ.v n <= k /\ k < Seq.length s_cur ==> Seq.index s_cur k == Seq.index s0 k) /\
      SZ.fits (2 * Seq.length s0 + 2) /\
      heaps_from s_cur (SZ.v n) (SZ.v vi) /\
      vc >= reveal c0 /\
      vc - reveal c0 <= op_Star (SZ.v half - SZ.v vi) (CB.max_heapify_bound (SZ.v n) 0)
    )
  decreases (SZ.v !i)
  {
    let vi = !i;
    let idx = vi - 1sz;
    i := idx;
    with s_cur. assert (A.pts_to a s_cur);
    heaps_from_to_almost s_cur (SZ.v n) (SZ.v idx) (SZ.v idx);
    CB.max_heapify_bound_le_root (SZ.v n) (SZ.v idx);
    max_heapify a idx n (SZ.v idx) ctr #s_cur;
    ()
  };
  
  with s_built. assert (A.pts_to a s_built);
  heaps_from_zero s_built (SZ.v n);
  ()
}
#pop-options

#restart-solver

// ========== Main HeapSort ==========
// CLRS §6.4: HEAPSORT(A)
// Phase 1: BUILD-MAX-HEAP (standalone function, see CLRS §6.3)
// Phase 2: Extract-max loop
//
// Requires SZ.fits(2*n+2) to prevent SizeT overflow in child index
// computation (see max_heapify comment above).

#push-options "--z3rlimit 70 --fuel 1 --ifuel 1"
fn heapsort
  (a: A.array int)
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#s0: erased (Seq.seq int) {
    SZ.v n <= A.length a /\
    Seq.length s0 == A.length a /\
    SZ.fits (op_Star 2 (Seq.length s0) + 2)
  })
  (#c0: erased nat)
requires
  A.pts_to a s0 **
  GR.pts_to ctr c0
ensures exists* s (cf: nat).
  A.pts_to a s **
  GR.pts_to ctr cf **
  pure (
    Seq.length s == Seq.length s0 /\
    sorted_upto s (SZ.v n) /\
    permutation s0 s /\
    (forall (k:nat). SZ.v n <= k /\ k < Seq.length s ==> Seq.index s k == Seq.index s0 k) /\
    cf >= reveal c0 /\
    cf - reveal c0 <= CB.heapsort_cost_bound (SZ.v n)
  )
{
  if (n = 0sz) {
    // Empty prefix: trivially sorted, identity permutation, zero cost
    ()
  } else {
  // Phase 1: BUILD-MAX-HEAP
  build_max_heap a n ctr;
  
  //SNIPPET_START: extract_max_loop
  // Phase 2: Extract-max loop
  let mut heap_sz: SZ.t = n;
  
  while (!heap_sz >^ 1sz)
  invariant exists* vsz s_cur (vc: nat).
    R.pts_to heap_sz vsz **
    A.pts_to a s_cur **
    GR.pts_to ctr vc **
    pure (
      SZ.v vsz > 0 /\
      SZ.v vsz <= SZ.v n /\
      Seq.length s_cur == Seq.length s0 /\
      Seq.length s_cur == A.length a /\
      permutation s0 s_cur /\
      (forall (k:nat). SZ.v n <= k /\ k < Seq.length s_cur ==> Seq.index s_cur k == Seq.index s0 k) /\
      SZ.fits (2 * Seq.length s0 + 2) /\
      is_max_heap s_cur (SZ.v vsz) /\
      suffix_sorted_upto s_cur (SZ.v vsz) (SZ.v n) /\
      prefix_le_suffix_upto s_cur (SZ.v vsz) (SZ.v n) /\
      vc >= reveal c0 /\
      vc - reveal c0 <= CB.build_cost_bound (SZ.v n) +
                         op_Star (SZ.v n - SZ.v vsz) (CB.max_heapify_bound (SZ.v n) 0)
    )
  //SNIPPET_END: extract_max_loop
  decreases (SZ.v !heap_sz)
  {
    let vsz = !heap_sz;
    with s_cur. assert (A.pts_to a s_cur);
    
    // vsz > 1 from loop condition, so last >= 1
    let last = vsz - 1sz;
    let v0 = a.(0sz);
    let vl = a.(last);
    a.(0sz) <- vl;
    a.(last) <- v0;
    
    with s_swapped. assert (A.pts_to a s_swapped);
    swap_is_permutation s_cur 0 (SZ.v last);
    swap_length s_cur 0 (SZ.v last);
    extract_extends_sorted_upto s_cur (SZ.v vsz) (SZ.v n);
    
    let new_sz = vsz - 1sz;
    extract_almost_heaps s_cur (SZ.v vsz);
    let zero : Ghost.erased nat = 0;
    CB.max_heapify_bound_monotone (SZ.v new_sz) (SZ.v n) 0;
    max_heapify a 0sz new_sz zero ctr #(swap_seq s_cur 0 (SZ.v last));
    with s_heapified. assert (A.pts_to a s_heapified);
    with vc_after. assert (GR.pts_to ctr vc_after);
    // Help SMT: (n-vsz)*m + m = (n-vsz+1)*m by distributivity
    FStar.Math.Lemmas.distributivity_add_left (SZ.v n - SZ.v vsz) 1 (CB.max_heapify_bound (SZ.v n) 0);
    heaps_from_zero s_heapified (SZ.v new_sz);
    perm_preserves_sorted_suffix_upto (swap_seq s_cur 0 (SZ.v last)) s_heapified (SZ.v new_sz) (SZ.v n);
    
    heap_sz := new_sz;
  };
  
  with s_final. assert (A.pts_to a s_final);
  sorted_upto_from_parts s_final (SZ.v n);
  ()
  } // else n > 0
}
#pop-options
