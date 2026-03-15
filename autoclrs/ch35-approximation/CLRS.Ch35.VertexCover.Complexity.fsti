module CLRS.Ch35.VertexCover.Complexity

(**
 * Complexity analysis for APPROX-VERTEX-COVER.
 *
 * The implementation uses a nested loop over all vertex pairs (u, v) with u < v,
 * yielding O(V²) time complexity. This is correct for the adjacency-matrix
 * representation used. CLRS achieves O(V+E) with adjacency lists.
 *
 * partial_iterations tracks per-row accumulation for linking to the Pulse
 * implementation via ghost counters.
 *)

open FStar.Mul

(*** Complexity definitions ***)

// The number of iterations of the nested loop for a graph with v vertices.
// The outer loop runs v times; the inner loop runs up to v-1 times per outer iteration.
// Total iterations: v*(v-1)/2, bounded above by v*v.
val vertex_cover_iterations (v: nat) : nat

// The vertex cover algorithm runs in O(V²) time with adjacency-matrix representation
val vertex_cover_quadratic (v: nat)
  : Lemma (ensures vertex_cover_iterations v <= v * v)

(*** Partial iteration counts for Pulse linking ***)

// Cumulative inner-loop iterations after processing rows 0..(rows_done-1).
// Row k contributes (n - k - 1) iterations (v from k+1 to n-1).
val partial_iterations (n: nat) (rows_done: nat) : nat

val partial_iterations_zero (n: nat)
  : Lemma (ensures partial_iterations n 0 = 0)

val partial_iterations_step (n: nat) (k: nat)
  : Lemma (requires k < n)
          (ensures partial_iterations n (k + 1) = partial_iterations n k + (n - k - 1))

val partial_iterations_total (n: nat)
  : Lemma (ensures partial_iterations n n = vertex_cover_iterations n)
