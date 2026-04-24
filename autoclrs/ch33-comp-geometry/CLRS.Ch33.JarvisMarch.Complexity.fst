(*
   Jarvis's March (Gift Wrapping) — CLRS Chapter 33, Section 33.3

   Complexity analysis for Jarvis march.
   O(nh) where n = input points, h = hull vertices; O(n^2) worst case.
*)

module CLRS.Ch33.JarvisMarch.Complexity

// find_leftmost: n-1 comparisons for n points
let find_leftmost_ops (n: nat) : nat = if n > 0 then n - 1 else 0

// find_next: at most n-1 cross-product evaluations (skip current)
let find_next_ops (n: nat) : nat = if n > 1 then n - 1 else 0

// Full Jarvis march: 1 find_leftmost + h find_next calls
let jarvis_march_ops (n h: nat) : nat = find_leftmost_ops n + h * find_next_ops n

// Jarvis march is O(nh): bounded by n^2 in the worst case
let jarvis_march_quadratic_bound (n h: nat) : Lemma
  (requires n > 1 /\ h <= n)
  (ensures jarvis_march_ops n h <= n * n)
  = ()

// Each helper is O(n)
let helpers_linear (n: nat) : Lemma
  (requires n > 1)
  (ensures find_leftmost_ops n <= n /\ find_next_ops n <= n)
  = ()
