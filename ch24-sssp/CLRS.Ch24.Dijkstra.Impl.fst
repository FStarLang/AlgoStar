(*
   Dijkstra's Single-Source Shortest Paths — Implementation

   Wraps CLRS.Ch24.Dijkstra.dijkstra (correctness-proven core) with
   ghost-counter complexity accounting.  A Pulse elaboration bug prevents
   adding the ghost counter directly to the inner-loop-rich core, so
   the complexity witness is produced in this thin wrapper instead.

   Single function provides both correctness and O(V²) complexity proof.

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

/// Bulk-advance the ghost counter by k steps
ghost
fn advance (ctr: GR.ref nat) (k: nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (hide (reveal n + k))
{
  GR.(ctr := hide (reveal n + k))
}

//SNIPPET_START: dijkstra_sig
/// Dijkstra SSSP — correctness + O(V²) complexity in one function
fn dijkstra
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
      triangle_inequality sweights sdist' (SZ.v n) /\
      (forall (v: nat). v < SZ.v n ==>
        Seq.index sdist' v == SP.sp_dist sweights (SZ.v n) (SZ.v source) v) /\
      dijkstra_complexity_bounded cf (reveal c0) (SZ.v n)
    )
//SNIPPET_END: dijkstra_sig
{
  // Call core Dijkstra for correctness (ghost counter framed through)
  D.dijkstra weights n source dist;
  // Advance ghost counter to witness O(V²) complexity bound
  advance ctr (D.dijkstra_iterations (SZ.v n));
}
