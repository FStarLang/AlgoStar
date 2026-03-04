module CLRS.Ch24.BellmanFord.Lemmas

(*
   Interface for Bellman-Ford lemmas.

   Re-exports key results from:
   - CLRS.Ch24.BellmanFord.SpecBridge  (flat-weight ↔ adj-matrix equivalence)
   - CLRS.Ch24.BellmanFord.TriangleInequality  (relaxation fixpoint ⇒ triangle)
*)

open FStar.Mul

module SB  = CLRS.Ch24.BellmanFord.SpecBridge
module BTI = CLRS.Ch24.BellmanFord.TriangleInequality
module BFS = CLRS.Ch24.BellmanFord.Spec
module SP  = CLRS.Ch24.ShortestPath.Spec

/// Flatten adjacency matrix to row-major flat weight sequence
val flatten_adj (#n: nat) (adj: BFS.adj_matrix n)
  : s:FStar.Seq.seq int{FStar.Seq.length s == n * n}

/// Correspondence between option int (BFS) and sentinel int (SP)
val option_int_correspond (o: option int) (i: int) : prop

/// Boundedness precondition for equivalence
val well_bounded (#n: nat) (adj: BFS.adj_matrix n) (src: nat{src < n}) (k: nat) : prop

/// sp_dist_k equivalence (CLRS Lemma 24.2 bridge)
val sp_dist_k_equiv
  (#n: nat) (adj: BFS.adj_matrix n) (src dst: nat{src < n /\ dst < n}) (k: nat)
  : Lemma
    (requires SB.well_bounded adj src k)
    (ensures  SB.option_int_correspond
                (BFS.sp_dist_k adj src dst k)
                (SP.sp_dist_k (SB.flatten_adj adj) n src dst k))

/// sp_dist equivalence wrapper
val sp_dist_equiv
  (#n: nat) (adj: BFS.adj_matrix n) (src dst: nat{src < n /\ dst < n})
  : Lemma
    (requires n > 0 /\ SB.well_bounded adj src (n - 1))
    (ensures (
      let flat = SB.flatten_adj adj in
      match BFS.sp_dist adj src dst with
      | None   -> SP.sp_dist flat n src dst == SP.inf
      | Some d -> SP.sp_dist flat n src dst == d /\ d < SP.inf))

/// Relaxation fixpoint implies triangle inequality (main theorem)
val stable_distances_have_triangle
  (#n: nat) (dist: BTI.dist_vec n) (weights: BTI.weight_matrix n)
  : Lemma
    (requires FStar.Seq.equal (BTI.bf_round dist weights) dist)
    (ensures BTI.triangle_inequality dist weights)

/// No violations implies triangle inequality
val no_violations_implies_triangle
  (#n: nat) (dist: BTI.dist_vec n) (weights: BTI.weight_matrix n)
  : Lemma
    (requires (
      forall (u v: nat). u < n /\ v < n ==>
        (let d_u = FStar.Seq.index dist u in
         let d_v = FStar.Seq.index dist v in
         let w = FStar.Seq.index weights (u * n + v) in
         w >= BTI.inf \/ d_u >= BTI.inf \/ d_v <= d_u + w)))
    (ensures BTI.triangle_inequality dist weights)

/// After n-1 rounds, if stable, triangle inequality holds
val bellman_ford_stable_establishes_triangle
  (#n: nat) (dist: BTI.dist_vec n) (weights: BTI.weight_matrix n)
  : Lemma
    (requires
      n >= 1 /\
      FStar.Seq.equal (BTI.bf_k_rounds dist weights n) (BTI.bf_k_rounds dist weights (n - 1)))
    (ensures BTI.triangle_inequality (BTI.bf_k_rounds dist weights (n - 1)) weights)
