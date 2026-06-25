module CLRS.Ch06.Heap.Rubric
#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module HC = CLRS.Ch06.Heap.Complexity
module MR = Pulse.Lib.MonotonicGhostRef
module SC = CLRS.Common.Complexity.Sorting.Class
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TO = Pulse.Lib.TotalOrder

fn heapsort_sort (a: Type0)
  (arr: A.array a)
  (len: SZ.t)
  (ctr: SC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: SC.instrumented_total_order a ord ctr)
  (#s0: erased (Seq.seq a))
  (#i: erased nat)
  norewrite
requires arr |-> s0 ** pure (A.length arr == SZ.v len) ** MR.pts_to ctr #1.0R i
ensures exists* s' (ticks: nat).
  arr |-> s' **
  MR.pts_to ctr #1.0R ticks **
  pure (SC.sorted #a #ord s' /\
        SC.permutation s0 s' /\
        ticks <= reveal i +
          (let n = Seq.length s0 in
           if n > 0 then
             (n / 2) * (2 * HC.log2_floor n) +
             (n - 1) * (2 * HC.log2_floor n)
           else 0))
