(*
   CLRS Chapter 9.1: Simultaneous Min and Max — Implementation Interface
*)
module CLRS.Ch09.SimultaneousMinMax.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers
open CLRS.Ch09.SimultaneousMinMax.Spec

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module GR = Pulse.Lib.GhostReference

fn find_minmax
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len >= 1 /\
      SZ.v len == A.length a
    )
  returns result: minmax_result
  ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k) /\
      complexity_bounded_minmax cf (reveal c0) (SZ.v len)
    )

fn find_minmax_pairs
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      SZ.v len >= 1 /\
      SZ.v len == A.length a
    )
  returns result: minmax_result
  ensures exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf **
    pure (
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
      (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
      (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k) /\
      complexity_bounded_minmax_pairs cf (reveal c0) (SZ.v len)
    )
