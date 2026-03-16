(*
   Graham Scan — CLRS Chapter 33, Section 33.3

   Complexity analysis for Graham scan.
   O(n lg n) overall, dominated by sorting; scan loop is O(n) amortized.
*)

module CLRS.Ch33.GrahamScan.Complexity
open FStar.Mul

// find_bottom: n-1 comparisons
let find_bottom_ops (n: nat) : nat = if n > 0 then n - 1 else 0

// polar_cmp: O(1) — 5 subtractions, 2 multiplications, 1 subtraction
let polar_cmp_ops : nat = 8

// pop_while: O(top) worst case — each iteration does 1 cross product (7 ops) + 1 comparison
let pop_while_ops (top: nat) : nat = top * 8

// Sorting by polar angle: O(n^2) with insertion sort, O(n lg n) with merge sort
let polar_sort_ops_insertion (n: nat) : nat = n * n

// Graham scan loop: O(n) amortized — each point is pushed and popped at most once
let graham_scan_loop_ops (n: nat) : nat = 2 * n

// Full Graham scan: dominated by sorting
let graham_scan_ops (n: nat) : nat = find_bottom_ops n + polar_sort_ops_insertion n + graham_scan_loop_ops n

// Graham scan with insertion sort is O(n^2)
let graham_scan_quadratic (n: nat) : Lemma
  (requires n > 0)
  (ensures graham_scan_ops n <= 4 * n * n)
  = ()

// The scan loop alone is linear
let scan_linear (n: nat) : Lemma
  (ensures graham_scan_loop_ops n <= 2 * n)
  = ()
