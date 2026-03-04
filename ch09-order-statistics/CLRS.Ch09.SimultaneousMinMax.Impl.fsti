(*
   CLRS Chapter 9.1: Simultaneous Min and Max — Implementation Interface

   Public signatures for all four variants:
   - find_minmax: simple scan (2(n-1) comparisons)
   - find_minmax_pairs: CLRS pair-processing (⌊3n/2⌋ comparisons)
   - find_minmax_complexity: simple scan with ghost tick proof
   - find_minmax_pairs_complexity: pair-processing with ghost tick proof
*)
module CLRS.Ch09.SimultaneousMinMax.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open CLRS.Ch09.SimultaneousMinMax.Spec
open CLRS.Ch09.SimultaneousMinMax.Complexity

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// Simple linear scan — finds both min and max in one pass
fn find_minmax
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to a #p s0
  requires pure (
    SZ.v len == Seq.length s0 /\
    SZ.v len >= 1 /\
    SZ.v len == A.length a
  )
  returns result: minmax_result
  ensures A.pts_to a #p s0 ** pure (
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
    (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
    (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k)
  )

/// CLRS pair-processing — ⌊3n/2⌋ comparisons
fn find_minmax_pairs
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to a #p s0
  requires pure (
    SZ.v len == Seq.length s0 /\
    SZ.v len >= 1 /\
    SZ.v len == A.length a
  )
  returns result: minmax_result
  ensures A.pts_to a #p s0 ** pure (
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.min_val) /\
    (forall (k:nat). k < Seq.length s0 ==> result.min_val <= Seq.index s0 k) /\
    (exists (k:nat). k < Seq.length s0 /\ Seq.index s0 k == result.max_val) /\
    (forall (k:nat). k < Seq.length s0 ==> result.max_val >= Seq.index s0 k)
  )

/// Simple scan with complexity tracking — proves 2(n-1) comparisons
fn find_minmax_complexity
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

/// CLRS pair-processing with complexity tracking — proves ⌊3n/2⌋ comparisons
fn find_minmax_pairs_complexity
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
