(*
   CLRS Chapter 7: Partition — Implementation Interface

   Public signature for the partition wrapper that splits array ownership
   into three regions (left, pivot, right) for recursive quicksort.
*)
module CLRS.Ch07.Partition.Impl
#lang-pulse

open Pulse.Lib.Pervasives
open CLRS.Ch07.Partition.Lemmas
open CLRS.Common.SortSpec
module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// Ghost increment for tick counter
val incr_nat (n: erased nat) : erased nat

/// Partition wrapper that splits ownership into three regions (left, pivot, right)
/// for use by recursive quicksort.
fn clrs_partition_wrapper_with_ticks
  (a: A.array int)
  (lo: nat)
  (hi:(hi:nat{lo < hi}))
  (lb rb: erased int)
  (#s0: Ghost.erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires (
    A.pts_to_range a lo hi s0 **
    GR.pts_to ctr c0 **
    pure (
      hi <= A.length a /\
      Seq.length s0 = hi - lo /\
      between_bounds s0 lb rb
      )
  )
  returns p: nat
  ensures exists* s1 s_pivot s2 (cf: nat). (
    A.pts_to_range a lo   p     s1 **
    A.pts_to_range a p    (p+1) s_pivot **
    A.pts_to_range a (p+1) hi   s2 **
    GR.pts_to ctr cf **
    pure (
      lo <= p /\ p < hi /\ hi <= A.length a /\
      Seq.length s1 == p - lo /\ Seq.length s_pivot == 1 /\ Seq.length s2 == hi - (p+1) /\
      lb <= Seq.index s_pivot 0 /\ Seq.index s_pivot 0 <= rb /\
      between_bounds s1 lb (Seq.index s_pivot 0) /\
      between_bounds s2 (Seq.index s_pivot 0) rb /\
      strictly_larger_than s2 (Seq.index s_pivot 0) /\
      permutation s0 (Seq.append s1 (Seq.append s_pivot s2)) /\
      complexity_exact_linear cf (reveal c0) (hi - lo - 1)
   ))