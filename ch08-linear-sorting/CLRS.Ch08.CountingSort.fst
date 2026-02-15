(*
   Counting Sort - Verified implementation in Pulse
   
   This implements CLRS counting sort for non-negative integers bounded by k.
   Phase 1: Count occurrences of each value in a count array C[0..k]
   Phase 2: Write values back into the array in sorted order using counts
   
   Proves:
   1. The result is sorted
   2. The result is a permutation of the input
   
   NO admits. NO assumes.
*)

module CLRS.Ch08.CountingSort
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module L = CLRS.Ch08.CountingSort.Lemmas

// ========== Main Algorithm ==========

#push-options "--z3rlimit 120 --fuel 1 --ifuel 1"
fn counting_sort
  (a: A.array int)
  (len: SZ.t)
  (k_val: SZ.t)
  (#s0: erased (Seq.seq int))
requires
  A.pts_to a s0 **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len == Seq.length s0 /\
    Seq.length s0 == A.length a /\
    L.in_range s0 (SZ.v k_val) /\
    SZ.v len > 0 /\
    SZ.fits (SZ.v k_val + 2) /\
    SZ.fits (SZ.v len + SZ.v k_val + 2)
  )
ensures exists* s.
  A.pts_to a s **
  pure (
    Seq.length s == Seq.length s0 /\
    L.sorted s /\
    L.permutation s0 s
  )
{
  let n = len;
  let k = SZ.v k_val;
  let k1 = k_val + 1sz;

  // Phase 1: Build count array C where C[v] = count of v in s0
  let c_arr = V.alloc 0 k1;
  
  let mut j: SZ.t = 0sz;
  while (!j <^ n)
  invariant exists* vj sc.
    R.pts_to j vj **
    V.pts_to c_arr sc **
    A.pts_to a s0 **
    pure (
      SZ.v vj <= SZ.v n /\
      Seq.length sc == SZ.v k1 /\
      V.length c_arr == SZ.v k1 /\
      V.is_full_vec c_arr /\
      L.counts_match_prefix sc s0 k (SZ.v vj)
    )
  {
    let vj = !j;
    with sc. assert (V.pts_to c_arr sc);
    let val_j = a.(vj);
    let idx : SZ.t = SZ.uint_to_t val_j;
    let old_count = V.op_Array_Access c_arr idx;
    V.op_Array_Assignment c_arr idx (old_count + 1);
    with sc'. assert (V.pts_to c_arr sc');
    L.count_phase_step s0 sc sc' (SZ.v vj) k val_j;
    j := vj + 1sz;
  };
  
  // Phase 2: Write sorted values back
  // For each value v = 0..k, write count(v, s0) copies of v into a
  let mut pos: SZ.t = 0sz;
  let mut cur_v: SZ.t = 0sz;
  let mut cur_v_int: int = 0;
  
  while (!cur_v <=^ k_val)
  invariant exists* vcv vpos vcvi sc sa.
    R.pts_to j n **
    R.pts_to cur_v vcv **
    R.pts_to cur_v_int vcvi **
    R.pts_to pos vpos **
    V.pts_to c_arr sc **
    A.pts_to a sa **
    pure (
      SZ.v vcv <= SZ.v k_val + 1 /\
      vcvi == SZ.v vcv /\
      SZ.v vpos <= SZ.v n /\
      Seq.length sc == SZ.v k1 /\
      Seq.length sa == Seq.length s0 /\
      V.length c_arr == SZ.v k1 /\
      V.is_full_vec c_arr /\
      L.phase2_inv sa s0 (SZ.v vpos) (SZ.v vcv) k /\
      L.counts_match sc s0 k
    )
  {
    let vcv = !cur_v;
    let vpos = !pos;
    let vcvi = !cur_v_int;
    with sc sa. assert (V.pts_to c_arr sc ** A.pts_to a sa);
    
    // Read count for current value
    let cnt = V.op_Array_Access c_arr vcv;
    // cnt = count(vcv, s0) which is >= 0 and <= n
    L.count_bounded s0 (SZ.v vcv);
    L.phase2_pos_bound sa s0 (SZ.v vpos) (SZ.v vcv) k;
    let cnt_sz : SZ.t = SZ.uint_to_t cnt;
    
    // Write cnt copies of vcvi at positions [vpos, vpos+cnt)
    let mut w: SZ.t = 0sz;
    
    while (!w <^ cnt_sz)
    invariant exists* vw sa_inner.
      R.pts_to j n **
      R.pts_to cur_v vcv **
      R.pts_to cur_v_int vcvi **
      R.pts_to pos vpos **
      R.pts_to w vw **
      V.pts_to c_arr sc **
      A.pts_to a sa_inner **
      pure (
        SZ.v vw <= SZ.v cnt_sz /\
        SZ.v vpos + SZ.v cnt_sz <= SZ.v n /\
        Seq.length sa_inner == Seq.length s0 /\
        V.length c_arr == SZ.v k1 /\
        V.is_full_vec c_arr /\
        (forall (i:nat). SZ.v vpos <= i /\ i < SZ.v vpos + SZ.v vw ==> 
          Seq.index sa_inner i == vcvi) /\
        (forall (i:nat). i < SZ.v vpos ==> Seq.index sa_inner i == Seq.index sa i) /\
        (forall (i:nat). SZ.v vpos + SZ.v vw <= i /\ i < Seq.length sa_inner ==>
          Seq.index sa_inner i == Seq.index sa i)
      )
    {
      let vw = !w;
      with sa_w. assert (A.pts_to a sa_w);
      let write_pos = vpos + vw;
      assert (pure (SZ.v write_pos == SZ.v vpos + SZ.v vw));
      a.(write_pos) <- vcvi;
      with sa_new. assert (A.pts_to a sa_new);
      assert (pure (Seq.index sa_new (SZ.v write_pos) == vcvi));
      assert (pure (forall (j:nat). j < Seq.length sa_new /\ j <> SZ.v write_pos ==>
        Seq.index sa_new j == Seq.index sa_w j));
      w := vw + 1sz;
    };
    
    // After inner loop: sa_after has cnt copies of vcvi at [vpos, vpos+cnt)
    with sa_after. assert (A.pts_to a sa_after);
    L.phase2_step sa sa_after s0 (SZ.v vpos) (SZ.v cnt_sz) (SZ.v vcv) k;
    
    pos := vpos + cnt_sz;
    cur_v := vcv + 1sz;
    cur_v_int := vcvi + 1;
  };
  
  with vcv_f vpos_f vcvi_f sc_f sa_f.
    assert (R.pts_to j n ** R.pts_to cur_v vcv_f ** R.pts_to cur_v_int vcvi_f **
            R.pts_to pos vpos_f ** V.pts_to c_arr sc_f ** A.pts_to a sa_f);
  L.final_perm s0 sa_f k (SZ.v vpos_f);
  V.free c_arr;
  ()
}
#pop-options
