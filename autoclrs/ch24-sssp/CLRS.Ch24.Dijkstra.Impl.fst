(*
   Dijkstra's Single-Source Shortest Paths — Implementation

   Thin wrapper that re-exports CLRS.Ch24.Dijkstra.dijkstra under
   the rubric-required Impl naming convention, and strengthens the
   postcondition from pred_consistent (relates pred to dist) to
   shortest_path_tree (relates pred to sp_dist directly).

   The core Dijkstra algorithm in CLRS.Ch24.Dijkstra.fst provides both
   full functional correctness (dist[v] = δ(s,v) for all v), a predecessor
   array (pred_consistent), and O(V²) complexity in a single function via
   ghost tick counting.

   This wrapper chains: pred_consistent + (dist == sp_dist) ⟹ shortest_path_tree.

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

/// Bridge: pred_consistent + dist==sp_dist ⟹ shortest_path_tree
let pred_consistent_implies_spt
  (spred: Seq.seq SZ.t) (sdist sweights: Seq.seq int) (n source: nat)
  : Lemma
    (requires
      pred_consistent spred sdist sweights n source /\
      source < n /\
      (forall (v: nat). v < n ==> Seq.index sdist v == SP.sp_dist sweights n source v))
    (ensures shortest_path_tree spred sweights n source)
  = ()

/// Converse: sp_dist == inf ⟹ not reachable (under weights_in_range)
let sp_dist_inf_means_unreachable
  (sweights: Seq.seq int) (n source v: nat)
  : Lemma
    (requires
      weights_in_range sweights n /\
      n > 0 /\ source < n /\ v < n /\
      Seq.length sweights == n * n /\
      all_weights_non_negative sweights /\
      SP.sp_dist sweights n source v == SP.inf)
    (ensures ~(SP.reachable sweights n source v))
  = Classical.move_requires (SP.reachable_implies_sp_dist_finite sweights n source) v

let dijkstra_complexity_is_quadratic (cf c0 n: nat) : Lemma
  (requires dijkstra_complexity_bounded cf c0 n)
  (ensures cf - c0 <= 3 * n * n)
  =
  D.dijkstra_complexity_is_quadratic cf c0 n

#push-options "--z3rlimit 20"
//SNIPPET_START: dijkstra_sig
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
{
  // Core Dijkstra: gives pred_consistent + dist == sp_dist
  D.dijkstra weights n source dist pred ctr;
  // Chain: pred_consistent + dist == sp_dist ⟹ shortest_path_tree
  with sdist'. assert (A.pts_to dist sdist');
  with spred'. assert (A.pts_to pred spred');
  pred_consistent_implies_spt spred' sdist' sweights (SZ.v n) (SZ.v source);
}
#pop-options
