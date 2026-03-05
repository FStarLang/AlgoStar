module CLRS.Ch35.VertexCover.Complexity

(**
 * Complexity analysis for APPROX-VERTEX-COVER.
 *
 * The implementation uses a nested loop over all vertex pairs (u, v) with u < v,
 * yielding O(V²) time complexity. This is correct for the adjacency-matrix
 * representation used. CLRS achieves O(V+E) with adjacency lists.
 *)

open FStar.Mul

(*** Complexity definitions and proofs ***)

// Exact iteration count: v*(v-1)/2 for the nested loop over (u,v) with u < v
let vertex_cover_iterations (v: nat) : nat = v * (v - 1) / 2

// The nested loop performs at most v*v iterations
let vertex_cover_quadratic (v: nat)
  : Lemma (ensures vertex_cover_iterations v <= v * v)
  = ()

// Tighter bound: iterations are at most v*(v-1)/2
let vertex_cover_tight_bound (v: nat)
  : Lemma (ensures vertex_cover_iterations v <= v * v / 2)
  = ()
