module CLRS.Ch24.BellmanFord.Lemmas

(*
   Bellman-Ford Lemmas — Re-export Module

   Consolidates the two lemma files for Bellman-Ford into the rubric-required
   `Lemmas` module:

   - CLRS.Ch24.BellmanFord.SpecBridge:
       Bridge between flat-weight (ShortestPath.Spec) and adj-matrix (BellmanFord.Spec)
       formulations.  Main result: sp_dist_k_equiv / sp_dist_equiv.

   - CLRS.Ch24.BellmanFord.TriangleInequality:
       Proof that Bellman-Ford's relaxation fixpoint implies triangle inequality.
       Main results: stable_distances_have_triangle,
       bellman_ford_stable_establishes_triangle.
*)

module SB  = CLRS.Ch24.BellmanFord.SpecBridge
module BTI = CLRS.Ch24.BellmanFord.TriangleInequality

/// ===== Re-exports from SpecBridge =====

/// Flatten adjacency matrix to row-major flat weight sequence
let flatten_adj = SB.flatten_adj

/// Correspondence predicate between option int and sentinel int
let option_int_correspond = SB.option_int_correspond

/// Boundedness precondition for equivalence
let well_bounded = SB.well_bounded

/// sp_dist_k equivalence between flat-weight and adj-matrix formulations
let sp_dist_k_equiv = SB.sp_dist_k_equiv

/// sp_dist equivalence (wrapper for n-1)
let sp_dist_equiv = SB.sp_dist_equiv

/// ===== Re-exports from TriangleInequality =====

/// Relaxation fixpoint implies triangle inequality
let stable_distances_have_triangle = BTI.stable_distances_have_triangle

/// No violations implies triangle inequality
let no_violations_implies_triangle = BTI.no_violations_implies_triangle

/// After n-1 rounds, if stable, triangle inequality holds
let bellman_ford_stable_establishes_triangle = BTI.bellman_ford_stable_establishes_triangle
