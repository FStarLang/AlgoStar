module CLRS.Ch06.Heap.Rubric
#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module CB = CLRS.Ch06.Heap.CostBound
module MR = Pulse.Lib.MonotonicGhostRef
module SC = CLRS.Common.Complexity.Sorting.Class
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TO = Pulse.Lib.TotalOrder

fn heapsort_sort (#a: eqtype)
  (arr: A.array a)
  (len: SZ.t)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#s0: erased (Seq.seq a))
  (#i: erased nat)
requires arr |-> s0 ** pure (A.length arr == SZ.v len) ** MR.pts_to ctr #1.0R i
ensures exists* s' ticks.
  arr |-> s' **
  MR.pts_to ctr #1.0R ticks **
  pure (SC.sorted #a #ord s' /\
        SC.permutation s0 s' /\
        ticks <= reveal i + CB.heapsort_cost_bound (Seq.length s0))
