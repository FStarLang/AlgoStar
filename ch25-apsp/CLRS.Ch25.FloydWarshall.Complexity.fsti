module CLRS.Ch25.FloydWarshall.Complexity

(**
 * Interface for Floyd-Warshall complexity proof.
 *
 * Exposes the complexity bound predicate and the ghost-ticked
 * implementation that proves exactly n³ relaxation operations.
 *)

#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch25.FloydWarshall.Spec

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// Complexity bound predicate: cf - c0 == n³
let fw_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n * n * n

fn floyd_warshall_complexity
  (dist: array int)
  (#contents: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to dist contents **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      Seq.length contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns _:unit
  ensures exists* contents' (cf: nat).
    A.pts_to dist contents' **
    GR.pts_to ctr cf **
    pure (
      Seq.length contents' == SZ.v n * SZ.v n /\
      contents' == fw_outer contents (SZ.v n) 0 /\
      fw_complexity_bounded cf (reveal c0) (SZ.v n)
    )
