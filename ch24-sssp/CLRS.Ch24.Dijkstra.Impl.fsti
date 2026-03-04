(*
   Dijkstra's Single-Source Shortest Paths — Implementation Interface

   Pulse function signature for the verified Dijkstra algorithm.
   Uses adjacency matrix representation (n×n flat array, 1000000 = no edge/∞).
   Requires non-negative weights.

   Postcondition guarantees:
   - dist[source] == 0
   - All distances non-negative and bounded [0, 1000000]
   - Triangle inequality for all edges
   - Shortest-path equality: dist[v] == sp_dist(source, v) for all v
*)

module CLRS.Ch24.Dijkstra.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Vec
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = CLRS.Ch24.ShortestPath.Spec
module D = CLRS.Ch24.Dijkstra

/// All weights are non-negative
let all_weights_non_negative = D.all_weights_non_negative

/// All distances are non-negative
let all_non_negative = D.all_non_negative

/// All distances bounded: 0 ≤ d ≤ 1000000
let all_bounded = D.all_bounded

/// Triangle inequality: for all finite edges, dist[v] <= dist[u] + w
let triangle_inequality = D.triangle_inequality

//SNIPPET_START: dijkstra_sig
/// Dijkstra SSSP algorithm (imperative, adjacency matrix, non-negative weights)
fn dijkstra
  (weights: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (dist: A.array int)
  (#sweights: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      Seq.length sdist == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      all_weights_non_negative sweights
    )
  ensures exists* sdist'.
    A.pts_to weights sweights **
    A.pts_to dist sdist' **
    pure (
      Seq.length sdist' == SZ.v n /\
      SZ.v source < Seq.length sdist' /\
      Seq.index sdist' (SZ.v source) == 0 /\
      all_non_negative sdist' /\
      all_bounded sdist' /\
      triangle_inequality sweights sdist' (SZ.v n) /\
      (forall (v: nat). v < SZ.v n ==>
        Seq.index sdist' v == SP.sp_dist sweights (SZ.v n) (SZ.v source) v)
    )
//SNIPPET_END: dijkstra_sig
