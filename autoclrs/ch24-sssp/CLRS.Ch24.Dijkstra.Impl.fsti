(*
   Dijkstra's Single-Source Shortest Paths — Implementation Interface

   Pulse function signature for the verified Dijkstra algorithm,
   providing both full correctness and O(V²) complexity guarantees
   in a single function via ghost tick counting.

   Uses adjacency matrix representation (n×n flat array, SP.inf = no edge/∞).
   Requires non-negative weights and weights_in_range (each finite weight w
   satisfies w*(n-1) < inf, ensuring all simple-path weights are representable).

   Postcondition guarantees:
   - Shortest-path equality: dist[v] == sp_dist(source, v) for all v
   - Predecessor tree: pred encodes a shortest-path tree (stated in terms of sp_dist)
   - Unreachability: sp_dist == inf ⟹ ¬reachable (proved lemma)
   - O(V²) complexity bound via ghost counter

   NOTE: The core Pulse implementation lives in CLRS.Ch24.Dijkstra.fst because
   a Pulse elaboration bug prevents renaming that module. This Impl module
   re-exports the public interface under the rubric-required naming convention.

   NO admits. NO assumes.
*)

module CLRS.Ch24.Dijkstra.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Vec
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = CLRS.Ch24.ShortestPath.Spec
module D = CLRS.Ch24.Dijkstra

/// All weights are non-negative
let all_weights_non_negative = D.all_weights_non_negative

/// Weights in range: each finite edge weight w satisfies |w| * (n-1) < inf,
/// ensuring all simple-path weights are representable (< inf).
let weights_in_range = SP.weights_in_range

/// Predecessor consistency: pred values consistent with dist array
let pred_consistent = D.pred_consistent

//SNIPPET_START: shortest_path_tree
/// Shortest-path tree: pred encodes actual shortest-path predecessors.
///
/// Two-sided characterization (under weights_in_range + non-negative weights):
///   Reachable (sp_dist < inf):  pred[v] < n ∧ δ(s,v) = δ(s, pred[v]) + w(pred[v], v)
///   Unreachable (sp_dist = inf): no valid path from source to v exists
///     (proved separately by sp_dist_inf_means_unreachable below)
///
/// Under weights_in_range, sp_dist < inf ⟺ reachable (see SP.sp_dist_iff_reachable).
let shortest_path_tree (spred: Seq.seq SZ.t) (sweights: Seq.seq int)
  (n source: nat) : prop =
  Seq.length spred == n /\
  Seq.length sweights >= n * n /\
  source < n /\
  SZ.v (Seq.index spred source) == source /\
  (forall (v: nat). v < n /\ v <> source /\ SP.sp_dist sweights n source v < SP.inf ==>
    (let p = SZ.v (Seq.index spred v) in
     p < n /\
     SP.sp_dist sweights n source v ==
       SP.sp_dist sweights n source p + Seq.index sweights (p * n + v)))
//SNIPPET_END: shortest_path_tree

//SNIPPET_START: sp_dist_inf_means_unreachable
/// Converse: if sp_dist(s,v) == inf under weights_in_range + non-negative weights,
/// then no valid path from source to v exists.
val sp_dist_inf_means_unreachable
  (sweights: Seq.seq int) (n source v: nat)
  : Lemma
    (requires
      weights_in_range sweights n /\
      n > 0 /\ source < n /\ v < n /\
      Seq.length sweights == n * n /\
      all_weights_non_negative sweights /\
      SP.sp_dist sweights n source v == SP.inf)
    (ensures ~(SP.reachable sweights n source v))
//SNIPPET_END: sp_dist_inf_means_unreachable

// ========== Complexity Bounds ==========

/// Total iteration count for Dijkstra with adjacency matrix
let dijkstra_iterations = D.dijkstra_iterations

/// Complexity bound predicate: connects ghost counter to iteration count
let dijkstra_complexity_bounded = D.dijkstra_complexity_bounded

/// O(n²) bound: total iterations ≤ 3n²
val dijkstra_complexity_is_quadratic (cf c0 n: nat) : Lemma
  (requires dijkstra_complexity_bounded cf c0 n)
  (ensures cf - c0 <= 3 * n * n)

// ========== Algorithm: Correctness + Complexity ==========

//SNIPPET_START: dijkstra_sig
/// Dijkstra SSSP — correctness + O(V²) complexity + shortest-path predecessor tree
fn dijkstra
  (weights: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (dist: A.array int)
  (pred: A.array SZ.t)
  (ctr: GR.ref nat)
  (#sweights: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#spred: erased (Seq.seq SZ.t))
  (#c0: erased nat)
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist **
    A.pts_to pred spred **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      Seq.length sdist == SZ.v n /\
      Seq.length spred == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      all_weights_non_negative sweights /\
      weights_in_range sweights (SZ.v n)
    )
  ensures exists* sdist' spred' (cf: nat).
    A.pts_to weights sweights **
    A.pts_to dist sdist' **
    A.pts_to pred spred' **
    GR.pts_to ctr cf **
    pure (
      Seq.length sdist' == SZ.v n /\
      (forall (v: nat). v < SZ.v n ==>
        Seq.index sdist' v == SP.sp_dist sweights (SZ.v n) (SZ.v source) v) /\
      shortest_path_tree spred' sweights (SZ.v n) (SZ.v source) /\
      dijkstra_complexity_bounded cf (reveal c0) (SZ.v n)
    )
//SNIPPET_END: dijkstra_sig
