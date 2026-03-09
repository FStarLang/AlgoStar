(*
   CLRS Chapter 6: Heapsort — Complexity Analysis Interface

   Signatures for complexity theorems following CLRS §6.3–6.4:
   - BUILD-MAX-HEAP is O(n) (Theorem 6.3)
   - HEAPSORT is O(n lg n) (§6.4)
*)

module CLRS.Ch06.Heap.Complexity

open FStar.Mul

/// Floor of logarithm base 2
val log2_floor (n: pos) : nat

/// Height of a node at index i in a heap of size n (CLRS §6.1)
val height_at_index (i: pos) (n: pos{i <= n}) : nat

/// MAX-HEAPIFY operations: at most 2 * height (CLRS §6.2)
val max_heapify_ops (height: nat) : nat

/// Bounded summation
val sum_from_to (f: nat -> nat) (i: nat) (j: nat) : nat

/// Nodes at height h in a heap of size n (CLRS §6.3, Exercise 6.3-3)
val nodes_at_height (n: pos) (h: nat) : nat

/// BUILD-MAX-HEAP operations: sum over heights
val build_heap_ops (n: pos) : nat

/// Extract-max loop operations (CLRS §6.4)
val extract_max_ops (n: nat) : nat

/// HEAPSORT total operations (CLRS §6.4)
val heapsort_ops (n: pos) : nat

// ========== Key theorems ==========

val log2_floor_bound (n: pos)
  : Lemma (ensures log2_floor n < n)

val log2_floor_monotonic (m n: pos)
  : Lemma (requires m <= n)
          (ensures log2_floor m <= log2_floor n)

val log2_floor_half (n: pos)
  : Lemma (requires n > 1)
          (ensures log2_floor (n / 2) = log2_floor n - 1)

val log2_floor_tight (n: pos)
  : Lemma (ensures log2_floor n <= n - 1)

val log2_floor_positive (n: pos{n > 1})
  : Lemma (ensures log2_floor n > 0)

val log2_floor_pow2 (k: nat)
  : Lemma (ensures log2_floor (pow2 k) = k)

val log2_floor_upper_bound (n: pos) (k: nat)
  : Lemma (requires log2_floor n <= k)
          (ensures n < pow2 (k + 1))

val log2_floor_lower_bound (n: pos)
  : Lemma (ensures pow2 (log2_floor n) <= n)

//SNIPPET_START: build_heap_ops_linear
/// BUILD-MAX-HEAP is O(n) — CLRS Theorem 6.3
val build_heap_ops_linear (n: pos)
  : Lemma (ensures build_heap_ops n <= 4 * n)
//SNIPPET_END: build_heap_ops_linear

//SNIPPET_START: heapsort_ops_simplified
/// HEAPSORT is O(n lg n) with constant 6
val heapsort_ops_simplified (n: pos)
  : Lemma (ensures heapsort_ops n <= op_Multiply (op_Multiply 6 n) (1 + log2_floor n))
//SNIPPET_END: heapsort_ops_simplified

/// Tighter practical bound: 2n·log₂n + 4n
val heapsort_practical_bound (n: pos)
  : Lemma (ensures heapsort_ops n <= op_Multiply (op_Multiply 2 n) (log2_floor n) + op_Multiply 4 n)

/// Asymptotic: 3n·log₂n for n ≥ 16
val heapsort_asymptotic (n: pos{n >= 16})
  : Lemma (ensures heapsort_ops n <= op_Multiply (op_Multiply 3 n) (log2_floor n))

//SNIPPET_START: heapsort_better_than_quadratic
/// Heapsort beats quadratic for n ≥ 11
val heapsort_better_than_quadratic (n: pos{n >= 11})
  : Lemma (ensures heapsort_ops n < op_Multiply n n)
//SNIPPET_END: heapsort_better_than_quadratic
