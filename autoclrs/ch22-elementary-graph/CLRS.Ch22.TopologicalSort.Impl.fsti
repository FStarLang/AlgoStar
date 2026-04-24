(*
 * CLRS Chapter 22 — Topological Sort Implementation Interface
 *
 * Exposes Kahn's algorithm for topological sorting (CLRS §22.4).
 *)
module CLRS.Ch22.TopologicalSort.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.WithPure
open CLRS.Ch22.TopologicalSort.Spec
open CLRS.Ch22.TopologicalSort.Impl.Defs

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

fn topological_sort
  (adj: A.array int)
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#sadj: erased (Seq.seq int))
  (#c0: erased nat)
  requires
    A.pts_to adj sadj **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      ~(has_cycle sadj (SZ.v n))
    )
  returns output: V.vec int
  ensures exists* sout (cf: nat).
    A.pts_to adj sadj **
    V.pts_to output sout **
    GR.pts_to ctr cf **
    pure (
      V.is_full_vec output /\
      Seq.length sout == SZ.v n /\
      // All vertices in output are valid indices
      (forall (i: nat). i < SZ.v n ==> Seq.index sout i < SZ.v n) /\
      // 1. All elements are non-negative (can be viewed as nat)
      (forall (i: nat). i < Seq.length sout ==> Seq.index sout i >= 0) /\
      // 2. All elements are distinct
      all_distinct (seq_int_to_nat sout) /\
      // 3. Output is a valid topological order
      is_topological_order sadj (SZ.v n) (seq_int_to_nat sout) /\
      // Complexity: at most n² ticks
      cf >= reveal c0 /\
      cf - reveal c0 <= SZ.v n * SZ.v n
    )
