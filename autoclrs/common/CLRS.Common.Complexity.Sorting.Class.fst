module CLRS.Common.Complexity.Sorting.Class
open Pulse
#lang-pulse
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module TC = FStar.Tactics.Typeclasses
module TO = Pulse.Lib.TotalOrder
module MR = Pulse.Lib.MonotonicGhostRef
open FStar.Order

let rec count (#t:Type) (x:t) (s:Seq.seq t)
: GTot nat (decreases Seq.length s)
= if Seq.length s = 0 then 0
  else if Seq.head s == x
  then 1 + count x (Seq.tail s)
  else count x (Seq.tail s)

let permutation 
      (#t:Type)
      (s0 s1:Seq.seq t)
= forall (x:t). count x s0 == count x s1
    
let sorted 
      (#t:Type)
      {| TO.total_order t |}
      (s:Seq.seq t)
= let open TO in
  forall (i j:nat).{:pattern (Seq.index s i); (Seq.index s j)}
  i <= j /\ j < Seq.length s ==> Seq.index s i <=? Seq.index s j

let preorder_nat : FStar.Preorder.preorder nat = (fun (x y:nat) -> b2t (x <= y))

let ticks_t = MR.mref #nat preorder_nat

let instrumented_total_order (a:Type) (ord:Pulse.Lib.TotalOrder.total_order a) (ctr:ticks_t) =
  fn (x y:a) (#i:erased nat)
  requires MR.pts_to ctr #1.0R i
  returns o:order
  ensures MR.pts_to ctr #1.0R (i + 1)
  ensures pure (o == x `ord.TO.compare` y)

class array_sort (a:Type) (f: nat -> nat) = {
  sort: (fn (arr:A.array a)
            (len:SZ.t) 
            (ctr:ticks_t)
            (#ord:erased (TO.total_order a))
            (iord:instrumented_total_order a ord ctr)
            (#s:erased (Seq.seq a)) (#i:erased nat)
         requires arr |-> s ** pure (A.length arr == SZ.v len) ** MR.pts_to ctr #1.0R i
         ensures exists* s' ticks. 
           arr |-> s' **
           MR.pts_to ctr #1.0R ticks **
           pure (sorted #_ #ord s' /\ permutation s s' /\ ticks <= i + f (Seq.length s)))
}