(*
   Dijkstra's Single-Source Shortest Paths — Implementation

   Re-exports from CLRS.Ch24.Dijkstra.fst (core Pulse implementation)
   under rubric naming. A Pulse elaboration bug prevents direct module rename.

   Includes both the verified algorithm and O(V²) complexity proof.

   NO admits. NO assumes.
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
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = CLRS.Ch24.ShortestPath.Spec
module D = CLRS.Ch24.Dijkstra

let dijkstra_complexity_is_quadratic (cf c0 n: nat) : Lemma
  (requires dijkstra_complexity_bounded cf c0 n)
  (ensures cf - c0 <= 3 * n * n)
  =
  D.dijkstra_complexity_is_quadratic cf c0 n

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
{
  D.dijkstra weights n source dist
}

/// Dijkstra with ghost tick counting for O(V²) complexity proof
fn dijkstra_complexity
  (weights: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (dist: A.array int)
  (#sweights: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      Seq.length sdist == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      all_weights_non_negative sweights
    )
  ensures exists* sdist' (cf: nat).
    A.pts_to weights sweights **
    A.pts_to dist sdist' **
    GR.pts_to ctr cf **
    pure (
      Seq.length sdist' == SZ.v n /\
      SZ.v source < Seq.length sdist' /\
      Seq.index sdist' (SZ.v source) == 0 /\
      all_non_negative sdist' /\
      all_bounded sdist' /\
      dijkstra_complexity_bounded cf (reveal c0) (SZ.v n)
    )
{
  D.dijkstra_complexity weights n source dist ctr
}
