(*
   CLRS Chapter 6: Heapsort — Public interface for imperative implementations

   Pulse function signatures for:
   - MAX-HEAPIFY (CLRS §6.2)
   - BUILD-MAX-HEAP (CLRS §6.3)
   - HEAPSORT (CLRS §6.4)
*)

module CLRS.Ch06.Heap.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

open CLRS.Ch06.Heap.Spec

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module CB = CLRS.Ch06.Heap.CostBound

//SNIPPET_START: max_heapify_sig
fn max_heapify
  (a: A.array int) (idx: SZ.t) (heap_size: SZ.t) (start: Ghost.erased nat)
  (ctr: GR.ref nat)
  (#s: erased (Seq.seq int) {
    SZ.v idx < SZ.v heap_size /\
    SZ.v heap_size <= Seq.length s /\
    Seq.length s == A.length a /\
    SZ.fits (op_Multiply 2 (Seq.length s) + 2)
  })
  (#c0: erased nat)
requires
  A.pts_to a s **
  GR.pts_to ctr c0 **
  pure (
    SZ.v idx >= start /\
    almost_heaps_from s (SZ.v heap_size) start (SZ.v idx) /\
    (SZ.v idx > 0 /\ parent_idx (SZ.v idx) >= start ==>
      (left_idx (SZ.v idx) < SZ.v heap_size ==>
        Seq.index s (parent_idx (SZ.v idx)) >= Seq.index s (left_idx (SZ.v idx))) /\
      (right_idx (SZ.v idx) < SZ.v heap_size ==>
        Seq.index s (parent_idx (SZ.v idx)) >= Seq.index s (right_idx (SZ.v idx))))
  )
ensures exists* s' (cf: nat).
  A.pts_to a s' **
  GR.pts_to ctr cf **
  pure (
    Seq.length s' == Seq.length s /\
    heaps_from s' (SZ.v heap_size) start /\
    permutation s s' /\
    (forall (k:nat). SZ.v heap_size <= k /\ k < Seq.length s ==> Seq.index s' k == Seq.index s k) /\
    cf >= reveal c0 /\
    cf - reveal c0 <= CB.max_heapify_bound (SZ.v heap_size) (SZ.v idx)
  )
//SNIPPET_END: max_heapify_sig

//SNIPPET_START: build_max_heap_sig
fn build_max_heap
  (a: A.array int)
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#s0: erased (Seq.seq int) {
    SZ.v n > 0 /\
    SZ.v n <= A.length a /\
    Seq.length s0 == A.length a /\
    SZ.fits (op_Multiply 2 (Seq.length s0) + 2)
  })
  (#c0: erased nat)
requires
  A.pts_to a s0 **
  GR.pts_to ctr c0
ensures exists* s (cf: nat).
  A.pts_to a s **
  GR.pts_to ctr cf **
  pure (
    Seq.length s == Seq.length s0 /\
    SZ.v n <= Seq.length s /\
    is_max_heap s (SZ.v n) /\
    permutation s0 s /\
    SZ.fits (op_Multiply 2 (Seq.length s) + 2) /\
    cf >= reveal c0 /\
    cf - reveal c0 <= CB.build_cost_bound (SZ.v n)
  )
//SNIPPET_END: build_max_heap_sig

//SNIPPET_START: heapsort_sig
fn heapsort
  (a: A.array int)
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#s0: erased (Seq.seq int) {
    SZ.v n <= A.length a /\
    SZ.v n == Seq.length s0 /\
    Seq.length s0 == A.length a /\
    SZ.v n > 0 /\
    SZ.fits (op_Multiply 2 (Seq.length s0) + 2)
  })
  (#c0: erased nat)
requires
  A.pts_to a s0 **
  GR.pts_to ctr c0
ensures exists* s (cf: nat).
  A.pts_to a s **
  GR.pts_to ctr cf **
  pure (
    Seq.length s == Seq.length s0 /\
    sorted s /\
    permutation s0 s /\
    cf >= reveal c0 /\
    cf - reveal c0 <= CB.heapsort_cost_bound (SZ.v n)
  )
//SNIPPET_END: heapsort_sig
