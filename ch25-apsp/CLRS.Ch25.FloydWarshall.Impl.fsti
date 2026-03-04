module CLRS.Ch25.FloydWarshall.Impl

(**
 * Interface for the Floyd-Warshall Pulse implementation.
 *
 * The imperative entry point: given an n×n distance matrix, computes
 * all-pairs shortest paths in-place and proves the result equals the
 * pure specification fw_outer.
 *)

#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch25.FloydWarshall.Spec

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq

fn floyd_warshall
  (dist: array int)
  (#contents: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires 
    A.pts_to dist contents **
    pure (
      SZ.v n > 0 /\
      Seq.length contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns _:unit
  ensures exists* contents'. 
    A.pts_to dist contents' **
    pure (
      Seq.length contents' == SZ.v n * SZ.v n /\
      contents' == fw_outer contents (SZ.v n) 0
    )
