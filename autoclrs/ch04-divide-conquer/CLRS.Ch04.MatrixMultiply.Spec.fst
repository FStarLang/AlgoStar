(*
   Matrix Multiply — Pure Specification (CLRS §4.2, pp. 75–76)

   Contains the pure definitions used by the matrix multiply implementation:
   - flat_index: Row-major index computation
   - dot_product_spec: Specification of dot product over flat arrays
   - mat_mul_correct: Full correctness predicate
   - mat_mul_partial_k / mat_mul_partial_ij: Partial result predicates
   - complexity_bounded_cubic: O(n³) complexity predicate
   - index_bounds_lemma: Arithmetic helper

   NO admits. NO assumes.
*)

module CLRS.Ch04.MatrixMultiply.Spec
open FStar.Seq
module Seq = FStar.Seq

// Flat index for row-major n×n matrix
let flat_index (n i j: nat) : nat = i * n + j

// Arithmetic helper
let index_bounds_lemma (n: nat{n > 0}) (i j k: nat) : Lemma
  (requires i < n /\ j < n /\ k < n)
  (ensures flat_index n i k < n * n /\ flat_index n k j < n * n /\ flat_index n i j < n * n) =
  ()

// Dot product spec: sum of a[i][k] * b[k][j] for k in [0, limit)
let rec dot_product_spec (sa sb: Seq.seq int) (n i j: nat) (limit: nat)
  : Tot int (decreases limit)
  = if limit = 0 || i >= n || j >= n || n = 0 then 0
    else if limit > n then dot_product_spec sa sb n i j n
    else let k = limit - 1 in
         if flat_index n i k >= Seq.length sa || flat_index n k j >= Seq.length sb then 0
         else dot_product_spec sa sb n i j (limit - 1) +
              Seq.index sa (flat_index n i k) * Seq.index sb (flat_index n k j)

// Result correctness: c[i][j] == dot_product_spec for all computed positions
let mat_mul_correct (sa sb sc: Seq.seq int) (n: nat) : prop =
  Seq.length sc == n * n /\
  (forall (i j: nat). i < n /\ j < n ==> 
    Seq.index sc (flat_index n i j) == dot_product_spec sa sb n i j n)

// Partial result: for position (i,j), partial dot product up to k is correct
let mat_mul_partial_k (sa sb sc: Seq.seq int) (n i j k: nat) : prop =
  Seq.length sc == n * n /\ i < n /\ j < n /\ k <= n /\
  Seq.index sc (flat_index n i j) == dot_product_spec sa sb n i j k

// All positions in rows < ri, plus positions (ri, col) for col < cj, are correct
let mat_mul_partial_ij (sa sb sc: Seq.seq int) (n ri cj: nat) : prop =
  Seq.length sc == n * n /\
  (forall (i j: nat). (i < ri \/ (i == ri /\ j < cj)) /\ i < n /\ j < n ==> 
    Seq.index sc (flat_index n i j) == dot_product_spec sa sb n i j n)

// Complexity bound predicate
let complexity_bounded_cubic (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n * n * n
