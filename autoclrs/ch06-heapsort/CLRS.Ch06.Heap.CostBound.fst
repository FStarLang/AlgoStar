module CLRS.Ch06.Heap.CostBound

/// Helper definitions and lemmas connecting max_heapify's cost
/// to the Complexity module. Separate from the Pulse file to avoid
/// BoundedIntegers typeclass interference.

open FStar.Math.Lemmas
open CLRS.Ch06.Heap.Complexity

// ========== Heap index functions (mirrored for use in cost bounds) ==========

let left_idx (i:nat) : nat = 2 * i + 1
let right_idx (i:nat) : nat = 2 * i + 2

// ========== max_heapify cost bound ==========

// heap_size / (idx + 1) is positive when idx < heap_size
let heap_div_pos (heap_size: pos) (idx: nat{idx < heap_size})
  : Lemma (heap_size / (idx + 1) >= 1)
  = let ip : pos = idx + 1 in
    lemma_div_le ip heap_size ip;
    lemma_div_plus 0 1 ip

// Cost bound for max_heapify at index idx in heap of size heap_size:
// 2 * log2_floor(heap_size / (idx + 1))
// At the root (idx=0): 2 * log2_floor(heap_size)
let max_heapify_bound (heap_size: pos) (idx: nat{idx < heap_size}) : nat =
  heap_div_pos heap_size idx;
  2 * log2_floor (heap_size / (idx + 1))

// Division is non-increasing in the divisor: a/c <= a/b when b <= c
let div_anti_monotone (a: nat) (b c: pos)
  : Lemma (requires b <= c) (ensures a / c <= a / b)
  = lemma_div_mod a b;
    lemma_div_mod a c

// max_heapify_bound at root matches 2 * log2_floor(heap_size)
let max_heapify_bound_root (heap_size: pos)
  : Lemma (max_heapify_bound heap_size 0 == 2 * log2_floor heap_size)
  = heap_div_pos heap_size 0

// When a node is not a leaf, its bound is >= 2 + the bound of the left child
let max_heapify_bound_left (heap_size: pos) (idx: nat{idx < heap_size})
  : Lemma (requires left_idx idx < heap_size)
          (ensures max_heapify_bound heap_size idx >= 
                   2 + max_heapify_bound heap_size (left_idx idx))
  = heap_div_pos heap_size idx;
    heap_div_pos heap_size (left_idx idx);
    let ip : pos = idx + 1 in
    let m : pos = heap_size / ip in
    assert (heap_size >= 2 * ip);
    lemma_div_le (2 * ip) heap_size ip;
    lemma_div_plus 0 2 ip;
    assert (m >= 2);
    division_multiplication_lemma heap_size ip 2;
    assert (heap_size / (2 * ip) == m / 2);
    assert (heap_size / (left_idx idx + 1) == m / 2);
    log2_floor_half m;
    ()

// When a node has a right child, its bound is >= 2 + the bound of the right child
#push-options "--z3rlimit 10"
let max_heapify_bound_right (heap_size: pos) (idx: nat{idx < heap_size})
  : Lemma (requires right_idx idx < heap_size)
          (ensures max_heapify_bound heap_size idx >= 
                   2 + max_heapify_bound heap_size (right_idx idx))
  = max_heapify_bound_left heap_size idx;
    heap_div_pos heap_size (right_idx idx);
    heap_div_pos heap_size (left_idx idx);
    div_anti_monotone heap_size (left_idx idx + 1) (right_idx idx + 1);
    log2_floor_monotonic (heap_size / (right_idx idx + 1)) (heap_size / (left_idx idx + 1));
    ()
#pop-options

// max_heapify_bound is monotone in heap_size (larger heap = larger bound)
let max_heapify_bound_monotone (hs1 hs2: pos) (idx: nat{idx < hs1 /\ idx < hs2})
  : Lemma (requires hs1 <= hs2) (ensures max_heapify_bound hs1 idx <= max_heapify_bound hs2 idx)
  = heap_div_pos hs1 idx;
    heap_div_pos hs2 idx;
    lemma_div_le hs1 hs2 (idx + 1);
    log2_floor_monotonic (hs1 / (idx + 1)) (hs2 / (idx + 1))

// max_heapify_bound is largest at the root (idx=0)
// Proof: larger idx means larger divisor, so smaller quotient, so smaller log
let max_heapify_bound_le_root (heap_size: pos) (idx: nat{idx < heap_size})
  : Lemma (ensures max_heapify_bound heap_size idx <= max_heapify_bound heap_size 0)
  = heap_div_pos heap_size idx;
    heap_div_pos heap_size 0;
    div_anti_monotone heap_size 1 (idx + 1);
    log2_floor_monotonic (heap_size / (idx + 1)) (heap_size / 1)

// Cost bounds (definitions are in the .fsti, these are for reference)
// build_cost_bound n = (n / 2) * max_heapify_bound n 0
// extract_cost_bound n = (n - 1) * max_heapify_bound n 0
// heapsort_cost_bound n = build_cost_bound n + extract_cost_bound n

// Heapsort cost is O(n log n)
// Proof: (n/2)*m + (n-1)*m <= n*m + n*m = 2*n*m where m = max_heapify_bound(n,0) = 2*log2_floor(n)
//        so total <= 2*n*2*log2_floor(n) = 4*n*log2_floor(n)
#push-options "--z3rlimit 10"
let heapsort_cost_nlogn (n: pos)
  : Lemma (ensures heapsort_cost_bound n <= 4 * n * log2_floor n)
  = max_heapify_bound_root n;
    let lg = log2_floor n in
    assert (n > 0);
    assert (max_heapify_bound n 0 == 2 * lg);
    assert (build_cost_bound n == (n / 2) * (2 * lg));
    assert (extract_cost_bound n == (n - 1) * (2 * lg));
    ()
#pop-options

// ========== Bridge: connect Complexity.heapsort_ops to CostBound.heapsort_cost_bound ==========

// Extract-max: use the root-bound lemma from Complexity
let extract_max_ops_le_extract_cost (n: pos)
  : Lemma (ensures extract_max_ops n <= extract_cost_bound n)
  = extract_max_ops_le_root_bound n;
    heap_div_pos n 0

// Build-heap: use the root-bound lemma from Complexity
let build_heap_ops_le_build_cost (n: pos)
  : Lemma (ensures build_heap_ops n <= build_cost_bound n)
  = build_heap_ops_le_root_bound n;
    heap_div_pos n 0

// Bridge: combine build and extract bounds
let heapsort_ops_le_cost_bound (n: pos)
  : Lemma (ensures heapsort_ops n <= heapsort_cost_bound n)
  = build_heap_ops_le_build_cost n;
    extract_max_ops_le_extract_cost n;
    heapsort_ops_def n
