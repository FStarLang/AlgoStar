module CLRS.Ch35.VertexCover.Complexity

(**
 * Complexity analysis for APPROX-VERTEX-COVER.
 *
 * The implementation uses a nested loop over all vertex pairs (u, v) with u < v,
 * yielding O(V²) time complexity. This is correct for the adjacency-matrix
 * representation used. CLRS achieves O(V+E) with adjacency lists.
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
