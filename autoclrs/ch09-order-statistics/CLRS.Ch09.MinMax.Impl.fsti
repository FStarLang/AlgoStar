(*
   CLRS Chapter 9.1: MINIMUM / MAXIMUM — Implementation Interface

   Public signatures for find_minimum and find_maximum.
   Both prove:
   1. The returned value exists in the array
   2. The returned value is the minimum/maximum (universally bounded)
   3. Exactly (n - 1) comparisons — Θ(n)
*)
module CLRS.Ch09.MinMax.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers
open CLRS.Ch09.MinMax.Spec

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// Find the minimum element. Proves correctness and Θ(n) complexity.
fn find_minimum
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len > 0 /\
      SZ.v len == A.length a
    )
  returns min_val: int
  ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == min_val) /\
      (forall (k:nat). k < Seq.length s0 ==> min_val <= Seq.index s0 k) /\
      complexity_bounded_min cf (reveal c0) (SZ.v len)
    )

/// Find the maximum element. Proves correctness and Θ(n) complexity.
fn find_maximum
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len > 0 /\
      SZ.v len == A.length a
    )
  returns max_val: int
  ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == max_val) /\
      (forall (k:nat). k < Seq.length s0 ==> max_val >= Seq.index s0 k) /\
      complexity_bounded_max cf (reveal c0) (SZ.v len)
    )
