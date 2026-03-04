(*
   Bellman-Ford Single-Source Shortest Paths — Implementation Interface

   Pulse function signature for the verified Bellman-Ford algorithm.
   Uses adjacency matrix representation (n×n flat array, 1000000 = no edge/∞).

   Postcondition guarantees:
   - dist[source] == 0
   - Valid distances (< 1000000 or == 1000000)
   - If no negative cycle: triangle inequality + upper bound (CLRS Cor 24.3)
   - Negative-cycle detection (CLRS Cor 24.5)
   - Shortest-path equality under no negative cycles (CLRS Thm 24.4)
*)

module CLRS.Ch24.BellmanFord.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = CLRS.Ch24.ShortestPath.Spec
module BF = CLRS.Ch24.BellmanFord

/// Triangle inequality: for each edge (u,v), dist[v] <= dist[u] + w(u,v) when finite
let triangle_inequality = BF.triangle_inequality

/// All distances are either finite (< 1000000) or equal to 1000000 (unreachable)
let valid_distances = BF.valid_distances

/// Exists a violating edge: some edge (u,v) has dist[v] > dist[u] + w(u,v)
let exists_violation = BF.exists_violation

/// Lower bound invariant: dist[v] >= sp_dist[v] for all v
let lower_bound_inv = BF.lower_bound_inv

//SNIPPET_START: bellman_ford_sig
/// Bellman-Ford SSSP algorithm (imperative, adjacency matrix)
fn bellman_ford
  (weights: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (dist: A.array int)
  (result: R.ref bool)
  (#sweights: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#sresult: erased bool)
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist **
    R.pts_to result sresult **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      Seq.length sdist == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  ensures exists* sdist' no_neg_cycle.
    A.pts_to weights sweights **
    A.pts_to dist sdist' **
    R.pts_to result no_neg_cycle **
    pure (
      Seq.length sdist' == SZ.v n /\
      SZ.v source < Seq.length sdist' /\
      Seq.index sdist' (SZ.v source) == 0 /\
      valid_distances sdist' (SZ.v n) /\
      (no_neg_cycle == true ==> triangle_inequality sdist' sweights (SZ.v n)) /\
      (no_neg_cycle == true ==>
        (forall (v: nat). v < SZ.v n ==>
          Seq.index sdist' v <= SP.sp_dist sweights (SZ.v n) (SZ.v source) v)) /\
      (no_neg_cycle == false ==> exists_violation sdist' sweights (SZ.v n)) /\
      (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
        lower_bound_inv sdist' sweights (SZ.v n) (SZ.v source)) /\
      (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) /\ no_neg_cycle == true ==>
        (forall (v: nat). v < SZ.v n ==>
          Seq.index sdist' v == SP.sp_dist sweights (SZ.v n) (SZ.v source) v))
    )
//SNIPPET_END: bellman_ford_sig
