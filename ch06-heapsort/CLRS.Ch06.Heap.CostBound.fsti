(*
   CLRS Chapter 6: Heapsort — Cost Bound Interface

   Exports max_heapify cost bound definitions and lemmas connecting
   the ghost-tick counter to the Complexity module.
*)

module CLRS.Ch06.Heap.CostBound

open FStar.Mul
open CLRS.Ch06.Heap.Spec
open CLRS.Ch06.Heap.Complexity

val heap_div_pos (heap_size: pos) (idx: nat{idx < heap_size})
  : Lemma (heap_size / (idx + 1) >= 1)

/// Cost bound for max_heapify: 2 * log2_floor(heap_size / (idx + 1))
val max_heapify_bound (heap_size: pos) (idx: nat{idx < heap_size}) : nat

val max_heapify_bound_root (heap_size: pos)
  : Lemma (max_heapify_bound heap_size 0 == 2 * log2_floor heap_size)

val max_heapify_bound_left (heap_size: pos) (idx: nat{idx < heap_size})
  : Lemma (requires left_idx idx < heap_size)
          (ensures max_heapify_bound heap_size idx >= 
                   2 + max_heapify_bound heap_size (left_idx idx))

val max_heapify_bound_right (heap_size: pos) (idx: nat{idx < heap_size})
  : Lemma (requires right_idx idx < heap_size)
          (ensures max_heapify_bound heap_size idx >= 
                   2 + max_heapify_bound heap_size (right_idx idx))

val max_heapify_bound_monotone (hs1 hs2: pos) (idx: nat{idx < hs1 /\ idx < hs2})
  : Lemma (requires hs1 <= hs2) (ensures max_heapify_bound hs1 idx <= max_heapify_bound hs2 idx)
