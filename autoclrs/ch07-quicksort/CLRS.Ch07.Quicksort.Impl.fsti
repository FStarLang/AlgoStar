(*
   CLRS Chapter 7: Quicksort — Implementation Interface

   Public API signatures for the verified quicksort implementation.
   All functions guarantee sorted output that is a permutation of the input.
*)
module CLRS.Ch07.Quicksort.Impl
#lang-pulse

open Pulse.Lib.Pervasives
open CLRS.Ch07.Partition.Lemmas
open CLRS.Ch07.Quicksort.Lemmas
open CLRS.Common.SortSpec
module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

//SNIPPET_START: quicksort_sig
/// Top-level quicksort: sorts entire array, proving sorted + permutation.
fn quicksort
  (a: A.array int)
  (len: SZ.t)
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to a s0
  requires pure (Seq.length s0 == A.length a /\ A.length a == SZ.v len)
  ensures exists* s. (A.pts_to a s ** pure (sorted s /\ permutation s0 s))
//SNIPPET_END: quicksort_sig

/// Quicksort with complexity: exposes worst-case O(n²) bound via ghost counter.
fn quicksort_with_complexity
  (a: A.array int)
  (len: SZ.t)
  (#s0: Ghost.erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a s0 ** GR.pts_to ctr c0
  requires pure (Seq.length s0 == A.length a /\ A.length a == SZ.v len)
  ensures exists* s (cf: nat). (
    A.pts_to a s ** GR.pts_to ctr cf **
    pure (sorted s /\ permutation s0 s /\
          complexity_bounded_quadratic cf (reveal c0) (SZ.v len)))

/// Sub-range quicksort: sorts A[lo..hi) with caller-provided bounds.
fn quicksort_bounded
  (a: A.array int)
  (lo: nat)
  (hi: (hi:nat{lo <= hi}))
  (lb rb: erased int)
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a lo hi s0
  requires pure (
    hi <= A.length a /\
    Seq.length s0 = hi - lo /\
    between_bounds s0 lb rb /\
    lb <= rb
  )
  ensures exists* s. (
    A.pts_to_range a lo hi s **
    pure (sorted s /\ permutation s0 s /\ between_bounds s lb rb)
  )
