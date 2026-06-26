(*
   CLRS Chapter 4: binary search as an instance of the shared
   divide-and-conquer complexity rubric.
*)

module CLRS.Ch04.BinarySearch.Rubric
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open CLRS.Ch04.BinarySearch.Spec
open CLRS.Ch04.BinarySearch.Lemmas

module A = Pulse.Lib.Array
module DC = CLRS.Common.Complexity.DivideConquer.Class
module MR = Pulse.Lib.MonotonicGhostRef
module O = FStar.Order
module R = Pulse.Lib.Reference
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TO = Pulse.Lib.TotalOrder

let sorted_lt_excludes_prefix (#a:Type) (ord:erased (TO.total_order a))
  (s:Seq.seq a) (key:a) (mid:nat)
  : Lemma
    (requires DC.sorted ord s /\ mid < Seq.length s /\
              O.lt (Seq.index s mid `ord.TO.compare` key))
    (ensures forall (i:nat). i <= mid /\ i < Seq.length s ==> Seq.index s i =!= key)
  = ()

let sorted_gt_excludes_suffix (#a:Type) (ord:erased (TO.total_order a))
  (s:Seq.seq a) (key:a) (mid:nat)
  : Lemma
    (requires DC.sorted ord s /\ mid < Seq.length s /\
              O.gt (Seq.index s mid `ord.TO.compare` key))
    (ensures forall (i:nat). mid <= i /\ i < Seq.length s ==> Seq.index s i =!= key)
  = ()

#set-options "--z3rlimit 10"

fn binary_search_poly
  (a: Type0)
  (#p: perm)
  (arr: array a)
  (len: SZ.t)
  (key: a)
  (ctr: DC.ticks_t)
  (#ord: erased (TO.total_order a))
  (iord: DC.instrumented_total_order a ord ctr)
  (#s0: Ghost.erased (Seq.seq a))
  (#c0: erased nat)
  requires A.pts_to arr #p s0 ** MR.pts_to ctr #1.0R c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      Seq.length s0 <= A.length arr /\
      DC.sorted ord s0
    )
  returns result: SZ.t
  ensures exists* (cf: nat). A.pts_to arr #p s0 ** MR.pts_to ctr #1.0R cf **
    pure (
      DC.binary_search_correct s0 key (SZ.v result) /\
      cf <= reveal c0 + log2f (SZ.v len) + 1
    )
{
  if (len = 0sz) {
    len
  } else {
  let mut lo: SZ.t = 0sz;
  let mut hi: SZ.t = len;
  let mut found: bool = false;
  let mut result_idx: SZ.t = len;

  while (!lo <^ !hi && not !found)
  invariant exists* vlo vhi vfound vresult (vc : nat).
    R.pts_to lo vlo **
    R.pts_to hi vhi **
    R.pts_to found vfound **
    R.pts_to result_idx vresult **
    MR.pts_to ctr #1.0R vc **
    A.pts_to arr #p s0 **
    pure (
      DC.sorted ord s0 /\

      SZ.v vlo <= SZ.v vhi /\
      SZ.v vhi <= SZ.v len /\

      (vfound ==> (
        SZ.v vresult < SZ.v len /\
        SZ.v vresult < Seq.length s0 /\
        Seq.index s0 (SZ.v vresult) == key
      )) /\
      (not vfound ==> (
        SZ.v vresult == SZ.v len /\
        (forall (i:nat). i < SZ.v vlo /\ i < Seq.length s0 ==> Seq.index s0 i =!= key) /\
        (forall (i:nat). i >= SZ.v vhi /\ i < Seq.length s0 ==> Seq.index s0 i =!= key) /\
        (forall (i:nat). i < Seq.length s0 /\ Seq.index s0 i == key ==>
          SZ.v vlo <= i /\ i < SZ.v vhi)
      )) /\

      vc >= reveal c0 /\
      vc - reveal c0 <= log2f (SZ.v len) + 1 /\
      (not vfound /\ SZ.v vhi > SZ.v vlo ==>
        (vc - reveal c0) + log2f (SZ.v vhi - SZ.v vlo) <= log2f (SZ.v len))
    )
  decreases ((if not !found then 1 else 0) `Prims.op_Addition` (SZ.v !hi `Prims.op_Subtraction` SZ.v !lo))
  {
    let vlo = !lo;
    let vhi = !hi;

    let diff : SZ.t = vhi -^ vlo;
    let half : SZ.t = diff /^ 2sz;
    let mid : SZ.t = vlo +^ half;

    let mid_val : a = arr.(mid);
    let cmp = iord mid_val key;

    if (O.eq cmp) {
      found := true;
      result_idx := mid;
      ()
    } else if (O.lt cmp) {
      lo := mid +^ 1sz;
      sorted_lt_excludes_prefix ord s0 key (SZ.v mid);

      lemma_log2f_step (SZ.v vhi - SZ.v vlo) (SZ.v vhi - (SZ.v mid + 1));
      ()
    } else {
      hi := mid;
      sorted_gt_excludes_suffix ord s0 key (SZ.v mid);

      lemma_log2f_step (SZ.v vhi - SZ.v vlo) (SZ.v mid - SZ.v vlo);
      assert (pure (SZ.v mid - SZ.v vlo >= 1 ==>
        log2f (SZ.v mid - SZ.v vlo) + 1 <= log2f (SZ.v vhi - SZ.v vlo)));
      ()
    }
  };

  let vresult = !result_idx;
  vresult
  }
}

fn binary_search_poly_instance (a:Type0)
  (#p:perm)
  (arr:A.array a)
  (len:SZ.t)
  (key:a)
  (ctr:DC.ticks_t)
  (#ord:erased (TO.total_order a))
  (iord:DC.instrumented_total_order a ord ctr)
  (#s0:erased (Seq.seq a))
  (#c0:erased nat)
  preserves A.pts_to arr #p s0
  requires MR.pts_to ctr #1.0R c0 **
    pure (SZ.v len == Seq.length s0 /\ Seq.length s0 <= A.length arr /\ DC.sorted ord s0)
  returns result:SZ.t
  ensures exists* ticks.
    MR.pts_to ctr #1.0R ticks **
    pure (DC.binary_search_correct s0 key (SZ.v result) /\
          ticks <= reveal c0 + (fun n -> log2f n + 1) (Seq.length s0))
{
  let result = binary_search_poly a #p arr len key ctr #ord iord #s0 #c0;
  result
}

instance binary_search_array_search : DC.array_binary_search (fun n -> log2f n + 1) =
  Pulse.Lib.Core.slprop_equivs ();
  {
    search = binary_search_poly_instance
  }
