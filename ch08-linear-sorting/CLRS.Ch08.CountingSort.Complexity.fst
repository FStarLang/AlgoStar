(*
   Counting Sort with Complexity Bound
   
   Proves O(n + k) complexity for counting sort where n is the array length
   and k is the maximum value. Specifically: at most 2*n + k + 1 operations.
   
   Phase 1 (counting): n operations
   Phase 2 (write-back): k+1 outer iterations + n total writes = n + k + 1
   Total: 2*n + k + 1
   
   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Also proves functional correctness (sorted + permutation).
   
   NO admits. NO assumes.
*)

module CLRS.Ch08.CountingSort.Complexity
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
module SeqP = FStar.Seq.Properties
module L = CLRS.Ch08.CountingSort.Lemmas

// ========== Ghost tick ==========

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (reveal n + 1)
{
  GR.(ctr := reveal n + 1)
}

// ========== Main Algorithm with Complexity ==========

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
fn counting_sort_complexity
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
  let ctr = GR.alloc #nat 0;

  // Phase 1: Build count array
  let c_arr = A.alloc 0 k1;
  
  let mut j: SZ.t = 0sz;
  while (!j <^ n)
  invariant exists* vj sc (vc: erased nat).
    R.pts_to j vj **
    A.pts_to c_arr sc **
    A.pts_to a s0 **
    GR.pts_to ctr vc **
    pure (
      SZ.v vj <= SZ.v n /\
      Seq.length sc == SZ.v k1 /\
      A.length c_arr == SZ.v k1 /\
      is_full_array c_arr /\
      L.counts_match_prefix sc s0 k (SZ.v vj) /\
      reveal vc == SZ.v vj
    )
  {
    let vj = !j;
    with sc. assert (A.pts_to c_arr sc);
    let val_j = a.(vj);
    let idx : SZ.t = SZ.uint_to_t val_j;
    let old_count = c_arr.(idx);
    c_arr.(idx) <- old_count + 1;
    with sc'. assert (A.pts_to c_arr sc');
    L.count_phase_step s0 sc sc' (SZ.v vj) k val_j;
    tick ctr;
    j := vj + 1sz;
  };
  
  // After Phase 1: vc == n ticks
  
  // Phase 2: Write sorted values back
  let mut pos: SZ.t = 0sz;
  let mut cur_v: SZ.t = 0sz;
  let mut cur_v_int: int = 0;
  
  while (!cur_v <=^ k_val)
  invariant exists* vcv vpos vcvi sc sa (vc: erased nat).
    R.pts_to j n **
    R.pts_to cur_v vcv **
    R.pts_to cur_v_int vcvi **
    R.pts_to pos vpos **
    A.pts_to c_arr sc **
    A.pts_to a sa **
    GR.pts_to ctr vc **
    pure (
      SZ.v vcv <= SZ.v k_val + 1 /\
      vcvi == SZ.v vcv /\
      SZ.v vpos <= SZ.v n /\
      Seq.length sc == SZ.v k1 /\
      Seq.length sa == Seq.length s0 /\
      A.length c_arr == SZ.v k1 /\
      is_full_array c_arr /\
      L.phase2_inv sa s0 (SZ.v vpos) (SZ.v vcv) k /\
      L.counts_match sc s0 k /\
      reveal vc == SZ.v n + SZ.v vpos + SZ.v vcv
    )
  {
    let vcv = !cur_v;
    let vpos = !pos;
    let vcvi = !cur_v_int;
    with sc sa. assert (A.pts_to c_arr sc ** A.pts_to a sa);
    
    let cnt = c_arr.(vcv);
    L.count_bounded s0 (SZ.v vcv);
    L.phase2_pos_bound sa s0 (SZ.v vpos) (SZ.v vcv) k;
    let cnt_sz : SZ.t = SZ.uint_to_t cnt;
    
    // Inner loop: write cnt copies of vcvi
    let mut w: SZ.t = 0sz;
    
    while (!w <^ cnt_sz)
    invariant exists* vw sa_inner (vc_inner: erased nat).
      R.pts_to j n **
      R.pts_to cur_v vcv **
      R.pts_to cur_v_int vcvi **
      R.pts_to pos vpos **
      R.pts_to w vw **
      A.pts_to c_arr sc **
      A.pts_to a sa_inner **
      GR.pts_to ctr vc_inner **
      pure (
        SZ.v vw <= SZ.v cnt_sz /\
        SZ.v vpos + SZ.v cnt_sz <= SZ.v n /\
        Seq.length sa_inner == Seq.length s0 /\
        A.length c_arr == SZ.v k1 /\
        is_full_array c_arr /\
        (forall (i:nat). SZ.v vpos <= i /\ i < SZ.v vpos + SZ.v vw ==> 
          Seq.index sa_inner i == vcvi) /\
        (forall (i:nat). i < SZ.v vpos ==> Seq.index sa_inner i == Seq.index sa i) /\
        (forall (i:nat). SZ.v vpos + SZ.v vw <= i /\ i < Seq.length sa_inner ==>
          Seq.index sa_inner i == Seq.index sa i) /\
        reveal vc_inner == SZ.v n + SZ.v vpos + SZ.v vcv + SZ.v vw
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
      tick ctr;
      let new_w = vw + 1sz;
      assert (pure (SZ.v new_w == SZ.v vw + 1));
      w := new_w;
    };
    
    with sa_after. assert (A.pts_to a sa_after);
    with vc_after_inner. assert (GR.pts_to ctr vc_after_inner);

    L.phase2_step sa sa_after s0 (SZ.v vpos) (SZ.v cnt_sz) (SZ.v vcv) k;
    
    // Tick for outer loop iteration
    tick ctr;
    
    let new_pos = vpos + cnt_sz;
    let new_vcv = vcv + 1sz;
    let new_vcvi = vcvi + 1;
    
    pos := new_pos;
    cur_v := new_vcv;
    cur_v_int := new_vcvi;
  };
  
  with vcv_f vpos_f vcvi_f sc_f sa_f vc_f.
    assert (R.pts_to j n ** R.pts_to cur_v vcv_f ** R.pts_to cur_v_int vcvi_f **
            R.pts_to pos vpos_f ** A.pts_to c_arr sc_f ** A.pts_to a sa_f **
            GR.pts_to ctr vc_f);

  // Total ticks: n + vpos_f + (k+1) <= n + n + k + 1 = 2n + k + 1
  assert (pure (reveal vc_f == SZ.v n + SZ.v vpos_f + (SZ.v k_val + 1)));
  
  L.final_perm s0 sa_f k (SZ.v vpos_f);
  
  GR.free ctr;
  A.free c_arr;
  ()
}
#pop-options
