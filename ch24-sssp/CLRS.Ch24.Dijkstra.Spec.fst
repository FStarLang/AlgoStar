module CLRS.Ch24.Dijkstra.Spec

(*
   Dijkstra Spec — Shared Specification

   Dijkstra's algorithm shares its pure shortest-path specification with
   Bellman-Ford via the common module CLRS.Ch24.ShortestPath.Spec.

   This module re-exports the shared specification to satisfy the rubric
   requirement for a per-algorithm Spec file.  The key definitions are:

   - sp_dist_k: shortest-path distance using at most k edges
   - sp_dist:   shortest-path distance (sp_dist_k with k = n-1)
   - has_triangle_inequality: triangle inequality predicate
   - triangle_ineq_implies_upper_bound: CLRS Corollary 24.3

   Dijkstra-specific requirement: all edge weights must be non-negative.
*)

module SP = CLRS.Ch24.ShortestPath.Spec

/// Infinity sentinel
let inf = SP.inf

/// Shortest-path distance using at most k edges
let sp_dist_k = SP.sp_dist_k

/// Shortest-path distance (unbounded, uses n-1 edges)
let sp_dist = SP.sp_dist

/// Triangle inequality predicate on distance vector
let has_triangle_inequality = SP.has_triangle_inequality

/// CLRS Corollary 24.3: triangle inequality implies upper bound on distances
let triangle_ineq_implies_upper_bound = SP.triangle_ineq_implies_upper_bound

/// No negative cycles (required for correctness — vacuously true for
/// non-negative weights, which Dijkstra requires)
let no_neg_cycles_flat = SP.no_neg_cycles_flat

/// Triangle inequality for shortest-path distances (CLRS Lemma 24.10)
let sp_dist_triangle_flat = SP.sp_dist_triangle_flat
