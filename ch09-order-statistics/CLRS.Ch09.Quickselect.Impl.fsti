(*
   CLRS Chapter 9.2: Quickselect — Pulse Implementation Interface

   Public API for quickselect and partition operations.
*)
module CLRS.Ch09.Quickselect.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module QSpec = CLRS.Ch09.Quickselect.Spec
module PSSSpec = CLRS.Ch09.PartialSelectionSort.Spec
module GR = Pulse.Lib.GhostReference
module QC = CLRS.Ch09.Quickselect.Complexity

let permutation = QSpec.permutation
let unchanged_outside = QSpec.unchanged_outside
let partition_ordered = QSpec.partition_ordered

fn partition_in_range
  (a: A.array int)
  (#s0: Ghost.erased (Seq.seq int))
  (lo: SZ.t)
  (hi: SZ.t)
  requires A.pts_to a s0
  requires pure (
    SZ.v lo < SZ.v hi /\
    SZ.v hi <= Seq.length s0 /\
    Seq.length s0 == A.length a
  )
  returns pivot_pos: SZ.t
  ensures exists* s1.
    A.pts_to a s1 **
    pure (
      Seq.length s1 == Seq.length s0 /\
      SZ.v lo <= SZ.v pivot_pos /\
      SZ.v pivot_pos < SZ.v hi /\
      permutation s0 s1 /\
      partition_ordered s1 (SZ.v lo) (SZ.v pivot_pos) (SZ.v hi) /\
      unchanged_outside s0 s1 (SZ.v lo) (SZ.v hi)
    )

fn quickselect
  (a: A.array int)
  (#s0: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (k: SZ.t)
  requires A.pts_to a s0
  requires pure (
    SZ.v n == Seq.length s0 /\
    SZ.v n == A.length a /\
    SZ.v n > 0 /\
    SZ.v k < SZ.v n
  )
  returns result: int
  ensures exists* s_final.
    A.pts_to a s_final **
    pure (
      Seq.length s_final == Seq.length s0 /\
      permutation s0 s_final /\
      SZ.v k < Seq.length s_final /\
      result == Seq.index s_final (SZ.v k) /\
      (forall (i: nat). i < SZ.v k /\ i < Seq.length s_final ==>
        Seq.index s_final i <= result) /\
      (forall (i: nat). SZ.v k < i /\ i < Seq.length s_final ==>
        result <= Seq.index s_final i) /\
      result == PSSSpec.select_spec s0 (SZ.v k)
    )

val complexity_bounded_quickselect (cf c0 n: nat) : prop

fn quickselect_complexity
  (a: A.array int)
  (#s0: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (k: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s0 /\
      SZ.v n == A.length a /\
      SZ.v n > 0 /\
      SZ.v k < SZ.v n
    )
  returns result: int
  ensures exists* s_final (cf: nat).
    A.pts_to a s_final ** GR.pts_to ctr cf **
    pure (
      Seq.length s_final == Seq.length s0 /\
      permutation s0 s_final /\
      SZ.v k < Seq.length s_final /\
      result == Seq.index s_final (SZ.v k) /\
      (forall (i: nat). i < SZ.v k /\ i < Seq.length s_final ==>
        Seq.index s_final i <= result) /\
      (forall (i: nat). SZ.v k < i /\ i < Seq.length s_final ==>
        result <= Seq.index s_final i) /\
      result == PSSSpec.select_spec s0 (SZ.v k) /\
      complexity_bounded_quickselect cf (reveal c0) (SZ.v n)
    )
