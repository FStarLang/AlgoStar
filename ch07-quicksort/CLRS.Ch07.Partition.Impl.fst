(*
   CLRS Chapter 7: Partition — Pulse Implementation

   Implements the CLRS Lomuto partition scheme (§7.1) with full
   functional correctness and exact complexity counting via ghost ticks.

   Key results:
   - Partition correctness: elements ≤ pivot before split, > pivot after
   - Permutation preservation
   - Exact complexity: hi-lo-1 comparisons (all elements except pivot)

   NO admits. NO assumes.
*)
module CLRS.Ch07.Partition.Impl
#lang-pulse

open Pulse.Lib.Pervasives
open CLRS.Ch07.Partition.Lemmas
open CLRS.Common.SortSpec
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Ghost tick increment ==========

let incr_nat (n: erased nat) : erased nat = hide (reveal n + 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Array access helpers ==========

// Partition loop invariant predicate (internal to this module)
let clrs_partition_pred (s:Seq.seq int) (lo:nat) (j:nat) (i_plus_1: nat) (pivot: int)
: prop
= forall (k:nat). {:pattern (Seq.index s k)}
   k < Seq.length s ==> (
    let kk = k + lo in
    (lo <= kk /\ kk < i_plus_1 ==> Seq.index s k <= pivot) /\
    (i_plus_1 <= kk /\ kk < j   ==> Seq.index s k > pivot))

// ========== Array access via pts_to_range ==========

let op_Array_Access
  (#t: Type)
  (a: A.array t)
  (i: SZ.t)
  (#l: nat{l <= SZ.v i})
  (#r: nat{SZ.v i < r})
  (#s: Ghost.erased (Seq.seq t))
  (#p: perm)
: stt t
    (requires A.pts_to_range a l r #p s)
    (ensures fun res ->
      A.pts_to_range a l r #p s **
      pure (Seq.length s == r - l /\
            res == Seq.index s (SZ.v i - l)))
= pts_to_range_index a i #l #r #s #p

let op_Array_Assignment
  (#t: Type)
  (a: A.array t)
  (i: SZ.t)
  (v: t)
  (#l: nat{l <= SZ.v i})
  (#r: nat{SZ.v i < r})
  (#s0: Ghost.erased (Seq.seq t))
: stt unit
    (requires A.pts_to_range a l r s0)
    (ensures fun _ -> 
      exists* s.
        A.pts_to_range a l r s **
        pure(
          Seq.length s0 == r - l /\ s == Seq.upd s0 (SZ.v i - l) v
        ))
= pts_to_range_upd a i v #l #r

// ========== Swap with permutation proof ==========

fn swap (a: A.array int) (i j: nat) (#l:nat{l <= i /\ l <= j}) (#r:nat{i < r /\ j < r})
  (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a l r s0
  ensures
    exists* s. 
      A.pts_to_range a l r s **
      pure (Seq.length s0 = r - l /\
            s == seq_swap s0 (i - l) (j - l) /\
            permutation s0 s)
{
  A.pts_to_range_prop a;
  let vi = a.(SZ.uint_to_t i);
  let vj = a.(SZ.uint_to_t j);
  (a.(SZ.uint_to_t i) <- vj);
  (a.(SZ.uint_to_t j) <- vi);
  ()
}

// ========== CLRS Partition with Tick Counter ==========

fn clrs_partition_with_ticks
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
  ensures exists* s (cf: nat).
    A.pts_to_range a lo hi s **
    GR.pts_to ctr cf **
    pure (
      Seq.length s = hi - lo /\ Seq.length s0 = hi - lo /\
      lo <= p /\ p < hi /\ hi <= A.length a /\
      (forall (k:nat). k < Seq.length s ==> (
         let kk = k + lo in
         (lo <= kk /\ kk < p ==> Seq.index s k <= Seq.index s (p - lo)) /\
         (kk == p                ==> Seq.index s k == Seq.index s (p - lo)) /\
         (p < kk /\ kk < hi      ==> Seq.index s k > Seq.index s (p - lo))
       )) /\
      lb <= Seq.index s (p - lo) /\ Seq.index s (p - lo) <= rb /\
      between_bounds s lb rb /\
      permutation s0 s /\
      complexity_exact_linear cf (reveal c0) (hi - lo - 1)
    )
{
  let pivot = a.(SZ.uint_to_t (hi - 1));
  let mut i_plus_1 = lo;
  let mut j = lo;
  
  while (let vj = !j; (vj < hi - 1))
    invariant exists* s (vc: nat). (
      A.pts_to_range a lo hi s **
      GR.pts_to ctr vc **
      live i_plus_1 ** live j **
      pure (
        lo <= !j /\ !j <= hi - 1 /\
        lo <= !i_plus_1 /\ !i_plus_1 <= !j /\
        lb <= pivot /\ pivot <= rb /\
        Seq.length s = hi - lo /\
        Seq.index s (hi - 1 - lo) = pivot /\
        clrs_partition_pred s lo (!j) (!i_plus_1) pivot /\
        permutation s0 s /\
        between_bounds s lb rb /\
        vc == reveal c0 + (!j - lo)
      ))
  decreases (hi - !j)
  { 
    let vj = !j;
    let aj = a.(SZ.uint_to_t vj);
    
    tick ctr;
    
    if (aj <= pivot) {
      let vi_plus_1 = !i_plus_1;
      swap a vi_plus_1 vj;
      i_plus_1 := vi_plus_1 + 1;
      j := vj + 1;
    } else {
      j := vj + 1;
    };
  };
  
  let vi_plus_1 = !i_plus_1;
  swap a vi_plus_1 (hi - 1);
  
  vi_plus_1
}

// ========== Partition wrapper with tick counter ==========

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
      permutation s0 (Seq.append s1 (Seq.append s_pivot s2)) /\
      complexity_exact_linear cf (reveal c0) (hi - lo - 1)
   ))
{
  let p = clrs_partition_with_ticks a lo hi lb rb ctr #c0;
  with s. assert (A.pts_to_range a lo hi s);
  with cf_partition. assert (GR.pts_to ctr cf_partition);

  pts_to_range_split a lo p hi;
  with s_left. assert (A.pts_to_range a lo p s_left);
  with s_right_plus. assert (A.pts_to_range a p hi s_right_plus);
  
  pts_to_range_split a p (p+1) hi;
  with s_pivot. assert (A.pts_to_range a p (p+1) s_pivot);
  with s_right. assert (A.pts_to_range a (p+1) hi s_right);

  transfer_smaller_slice s lo lo p (Seq.index s_pivot 0);
  transfer_larger_slice s lo lo p lb;
  
  transfer_smaller_slice s lo (p+1) hi rb;
  transfer_larger_slice s lo (p+1) hi (Seq.index s_pivot 0);
  
  p
}
