(*
   Binary Search - Verified Divide-and-Conquer Algorithm (CLRS Chapter 4)
   
   Proves:
   1. For a sorted array, binary_search returns an index where the key
      is found, or n if the key is not in the array.
   2. O(log n) comparison complexity: at most floor(log2(n)) + 1 comparisons.

   Uses GhostReference.ref nat for the tick counter -- fully erased at runtime.

   NO admits. NO assumes.
*)

module CLRS.Ch04.BinarySearch
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Pure helper: log2 floor ==========

let rec log2f (n: int) : Tot nat (decreases (if n > 0 then n else 0)) =
  if Prims.op_LessThanOrEqual n 1 then 0
  else Prims.op_Addition 1 (log2f (Prims.op_Division n 2))

let rec lemma_log2f_mono (a b: int)
  : Lemma (requires a >= 1 /\ b >= 1 /\ a <= b)
          (ensures log2f a <= log2f b)
          (decreases (if a > 0 then a else 0))
  = if Prims.op_LessThanOrEqual a 1 then ()
    else if Prims.op_LessThanOrEqual b 1 then ()
    else (
      FStar.Math.Lemmas.lemma_div_le a b 2;
      lemma_log2f_mono (Prims.op_Division a 2) (Prims.op_Division b 2)
    )

let lemma_log2f_step (old_range new_range: int)
  : Lemma (requires old_range >= 1 /\ new_range >= 0 /\ new_range <= old_range / 2)
          (ensures (new_range >= 1 ==> log2f new_range + 1 <= log2f old_range) /\
                   (new_range == 0 ==> 1 <= log2f old_range + 1))
  = if new_range >= 1 then
      lemma_log2f_mono new_range (Prims.op_Division old_range 2)
    else ()

// ========== Definitions ==========

let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i < j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

// ========== Complexity bound predicate ==========

let complexity_bounded_log (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= log2f n + 1

// ========== Binary Search with Complexity Bound ==========

#set-options "--z3rlimit 20"

//SNIPPET_START: binary_search_sig
fn binary_search
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (key: int)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v len == Seq.length s0 /\
      Seq.length s0 <= A.length a /\
      SZ.v len > 0 /\
      is_sorted s0
    )
  returns result: SZ.t
  ensures exists* (cf: nat). A.pts_to a s0 ** GR.pts_to ctr cf **
    pure (
      SZ.v result <= SZ.v len /\
      (SZ.v result < SZ.v len ==> (
        SZ.v result < Seq.length s0 /\
        Seq.index s0 (SZ.v result) == key
      )) /\
      (SZ.v result == SZ.v len ==> (
        forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i =!= key
      )) /\
      // Complexity: at most floor(log2(n)) + 1 comparisons = O(log n)
      complexity_bounded_log cf (reveal c0) (SZ.v len)
    )
//SNIPPET_END: binary_search_sig
{
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
    GR.pts_to ctr vc **
    A.pts_to a s0 **
    pure (
      (forall (i j: nat). {:pattern Seq.index s0 i; Seq.index s0 j}
        i < j /\ j < Seq.length s0 ==> Seq.index s0 i <= Seq.index s0 j) /\
      
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
      
      // Complexity: overall bound and remaining budget (relative to c0)
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
    
    let mid_val : int = a.(mid);
    
    // Count the comparison
    tick ctr;
    
    if (mid_val = key) {
      found := true;
      result_idx := mid;
      ()
    } else if (mid_val < key) {
      lo := mid +^ 1sz;
      
      lemma_log2f_step (SZ.v vhi - SZ.v vlo) (SZ.v vhi - (SZ.v mid + 1));
      ()
    } else {
      hi := mid;
      
      lemma_log2f_step (SZ.v vhi - SZ.v vlo) (SZ.v mid - SZ.v vlo);
      ()
    }
  };
  
  let vfound = !found;
  let vresult = !result_idx;
  
  vresult
}

