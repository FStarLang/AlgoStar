(*
   Dijkstra's Algorithm — Complexity Interface

   Re-exports complexity bounds from CLRS.Ch24.Dijkstra.

   CLRS §24.3: With adjacency matrix and array-based min-priority queue:
   - n EXTRACT-MIN: O(n) each → O(n²) total
   - n × n relaxations → O(n²) total
   - Overall: O(V²)

   Bound: n + 2n² ≤ 3n²

   NOTE: The complexity proof is integrated into the main dijkstra function
   in CLRS.Ch24.Dijkstra / CLRS.Ch24.Dijkstra.Impl. This module re-exports
   the pure complexity bounds.
*)

module CLRS.Ch24.Dijkstra.Complexity

open FStar.Mul

module D = CLRS.Ch24.Dijkstra

/// Total iteration count: n + 2n²
let dijkstra_iterations = D.dijkstra_iterations

/// Complexity predicate connecting pure math to ghost counter
let dijkstra_complexity_bounded = D.dijkstra_complexity_bounded

/// Quadratic bound: n + 2n² ≤ 3n²
val dijkstra_quadratic_bound (n: nat) : Lemma
  (ensures dijkstra_iterations n <= 3 * n * n)

/// O(V²) bound via complexity predicate
val dijkstra_complexity_is_quadratic (cf c0 n: nat) : Lemma
  (requires dijkstra_complexity_bounded cf c0 n)
  (ensures cf - c0 <= 3 * n * n)
