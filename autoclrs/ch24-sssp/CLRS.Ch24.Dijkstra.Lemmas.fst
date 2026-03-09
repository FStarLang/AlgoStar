module CLRS.Ch24.Dijkstra.Lemmas

(*
   Dijkstra Lemmas — Re-export Module

   Consolidates the two lemma files for Dijkstra into the rubric-required
   `Lemmas` module:

   - CLRS.Ch24.Dijkstra.Correctness:
       CLRS Theorem 24.6 (Greedy Choice Property): when a vertex u is extracted
       as the minimum unvisited vertex, dist[u] = δ(s,u).

   - CLRS.Ch24.Dijkstra.TriangleInequality:
       Proof that Dijkstra's relaxation process establishes triangle inequality
       after all vertices are processed.
*)

module DC  = CLRS.Ch24.Dijkstra.Correctness
module DTI = CLRS.Ch24.Dijkstra.TriangleInequality

/// ===== Re-exports from Correctness =====

/// CLRS Theorem 24.6: Greedy choice property
let greedy_choice_invariant = DC.greedy_choice_invariant

/// Relaxation establishes triangle inequality for settled edges
let relax_establishes_triangle_inequality = DC.relax_establishes_triangle_inequality

/// ===== Re-exports from TriangleInequality =====

/// After processing all vertices, triangle inequality holds
let dijkstra_algorithm_establishes_triangle = DTI.dijkstra_algorithm_establishes_triangle

/// Processing a vertex extends the triangle inequality
let dijkstra_establishes_triangle_inequality = DTI.dijkstra_establishes_triangle_inequality
