(*
   Counting Sort - CLRS faithful implementation with separate output array
   
   This implements CLRS COUNTING-SORT (§8.2) exactly:
   - Separate input array A (read-only) and output array B (written)
   - Phase 1: Initialize C[0..k] = 0
   - Phase 2: Count occurrences C[A[j]]++
   - Phase 3: Prefix sum C[i] = C[i] + C[i-1] for cumulative counts
   - Phase 4: Place elements backwards A[n..1] into B for stability
   
   NO admits. NO assumes.
*)

module CLRS.Ch08.CountingSort.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module S = CLRS.Ch08.CountingSort.Spec
module L = CLRS.Ch08.CountingSort.Lemmas
module SL = CLRS.Ch08.CountingSort.StableLemmas
module B = CLRS.Ch08.RadixSort.Base
module DL = CLRS.Ch08.CountingSort.DigitSortLemmas
module Stab = CLRS.Ch08.RadixSort.Stability

// sorted, permutation, in_range are defined in Spec.fst (module S)

// ========== Main Algorithm ==========

#push-options "--z3rlimit 120 --fuel 1 --ifuel 1"
//SNIPPET_START: counting_sort_impl_sig
```pulse
fn counting_sort_impl
  (a: A.array nat)     // Input array (read-only)
  (b: A.array nat)     // Output array (will be written)
  (len: SZ.t)          // Length of arrays
  (k_val: SZ.t)        // Maximum value in array
  (#sa: erased (Seq.seq nat))
  (#sb: erased (Seq.seq nat))
requires
  A.pts_to a #0.5R sa **
  A.pts_to b sb **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len <= A.length b /\
    SZ.v len == Seq.length sa /\
    SZ.v len == Seq.length sb /\
    Seq.length sa == A.length a /\
    Seq.length sb == A.length b /\
    S.in_range sa (SZ.v k_val) /\
    SZ.fits (SZ.v k_val + 2) /\
    SZ.fits (SZ.v len + SZ.v k_val + 2)
  )
ensures exists* sb'.
  A.pts_to a #0.5R sa **
  A.pts_to b sb' **
  pure (
    Seq.length sb' == Seq.length sa /\
    S.sorted sb' /\
    S.permutation sa sb' /\
    S.in_range sb' (SZ.v k_val)
  )
//SNIPPET_END: counting_sort_impl_sig
{
  if (len = 0sz) {
    L.empty_sorted_perm sb sa;
    L.empty_sorted_perm sa sb;
    ()
  } else {
  let k_plus_1 = k_val +^ 1sz;
  
  // Allocate count array C[0..k]
  let c : V.vec int = V.alloc 0 k_plus_1;
  
  // ========== Phase 1: Initialize C[0..k] = 0 ==========
  // Already done by alloc
  
  // ========== Phase 2: Count occurrences ==========
  // for j = 0 to len-1: C[A[j]]++
  
  let mut j : SZ.t = 0sz;
  
  // Seq.length sa == SZ.v len > 0 from precondition
  assert (pure (Seq.length sa > 0));
  
  while (
    let vj = !j;
    vj <^ len
  )
  invariant exists* vj sc.
    R.pts_to j vj **
    A.pts_to a #0.5R sa **
    A.pts_to b sb **
    V.pts_to c sc **
    pure (
      SZ.v vj <= SZ.v len /\
      Seq.length sc == SZ.v k_val + 1 /\
      L.counts_match_prefix sc sa (SZ.v k_val) (SZ.v vj)
    )
  decreases (SZ.v len - SZ.v !j)
  {
    let vj = !j;
    
    with sc. assert (V.pts_to c sc);
    
    // Read A[j]
    let val_j = A.op_Array_Access a vj;
    
    // Read C[val_j]
    let count_old = V.op_Array_Access c (SZ.uint_to_t val_j);
    
    // C[val_j] = C[val_j] + 1
    V.op_Array_Assignment c (SZ.uint_to_t val_j) (count_old + 1);
    
    with sc'. assert (V.pts_to c sc');
    
    // Establish new invariant using lemma
    L.count_phase_step sa sc sc' (SZ.v vj) (SZ.v k_val) val_j;
    
    // j++
    j := vj +^ 1sz;
  };
  
  // After phase 2: C contains counts
  with sc_after_phase2. assert (V.pts_to c sc_after_phase2);
  assert (pure (L.counts_match sc_after_phase2 sa (SZ.v k_val)));
  
  // Initialize prefix sum tracking
  SL.prefix_sum_inv_init sc_after_phase2 sa (SZ.v k_val);
  
  // ========== Phase 3: Prefix sum ==========
  // for i = 1 to k: C[i] = C[i] + C[i-1]
  // This transforms C[i] from count to cumulative count
  
  let mut i : SZ.t = 1sz;
  
  while (
    let vi = !i;
    vi <=^ k_val
  )
  invariant exists* vi sc.
    R.pts_to i vi **
    A.pts_to a #0.5R sa **
    A.pts_to b sb **
    V.pts_to c sc **
    pure (
      SZ.v vi >= 1 /\
      SZ.v vi <= SZ.v k_val + 1 /\
      Seq.length sc == SZ.v k_val + 1 /\
      SL.prefix_sum_inv sc sa (SZ.v k_val) (SZ.v vi)
    )
  decreases (SZ.v k_val + 1 - SZ.v !i)
  {
    let vi = !i;
    
    with sc. assert (V.pts_to c sc);
    
    // From loop invariant: SZ.v vi >= 1 and loop guard: vi <=^ k_val
    assert (pure (SZ.v vi >= 1 /\ SZ.v vi <= SZ.v k_val));
    
    let vi_minus_1 = vi -^ 1sz;
    
    // Read C[i-1]
    let prev_count = V.op_Array_Access c vi_minus_1;
    
    // Read C[i]
    let curr_count = V.op_Array_Access c vi;
    
    // C[i] = C[i] + C[i-1]
    V.op_Array_Assignment c vi (curr_count + prev_count);
    
    with sc'. assert (V.pts_to c sc');
    SL.prefix_sum_step sc sc' sa (SZ.v k_val) (SZ.v vi);
    
    // i++
    i := vi +^ 1sz;
  };
  
  // ========== Phase 4: Place elements (backwards) ==========
  // for j = len-1 downto 0:
  //   B[C[A[j]]] = A[j]
  //   C[A[j]]--
  // Backwards traversal ensures stability
  
  // After phase 3: establish cumulative counts
  with sc_after_phase3. assert (V.pts_to c sc_after_phase3);
  SL.prefix_sum_complete sc_after_phase3 sa (SZ.v k_val);
  
  // Initialize phase 4 tracking invariants
  SL.phase4_c_inv_init sc_after_phase3 sa (SZ.v k_val);
  SL.phase4_b_inv_init sc_after_phase3 sa sb (SZ.v k_val);
  
  // Start from len-1 (last element)
  let mut j_back : SZ.t = len -^ 1sz;
  let mut done : bool = false;
  
  while (
    let vdone = !done;
    not vdone
  )
  invariant exists* vj_back vdone sc sb_curr.
    R.pts_to j_back vj_back **
    R.pts_to done vdone **
    A.pts_to a #0.5R sa **
    V.pts_to c sc **
    A.pts_to b sb_curr **
    pure (
      Seq.length sc == SZ.v k_val + 1 /\
      Seq.length sb_curr == Seq.length sb /\
      (not vdone ==> SZ.v vj_back < SZ.v len) /\
      SL.phase4_c_inv sc sa (SZ.v k_val) (SZ.v len) (if vdone then 0 else SZ.v vj_back + 1) /\
      SL.phase4_b_inv sc sa sb_curr (SZ.v k_val) (SZ.v len)
    )
  decreases %[(if !done then 0 else 1); SZ.v !j_back]
  {
    let vj_back = !j_back;
    
    with sc. assert (V.pts_to c sc);
    with sb_curr. assert (A.pts_to b sb_curr);
    
    // From loop invariant: not vdone ==> SZ.v vj_back < SZ.v len
    assert (pure (SZ.v vj_back < SZ.v len));
    
    // Read A[j_back]
    let val_j = A.op_Array_Access a vj_back;
    
    // From precondition in_range sa (SZ.v k_val) and vj_back < len
    assert (pure (val_j <= SZ.v k_val));
    
    // Read C[val_j]
    let pos = V.op_Array_Access c (SZ.uint_to_t val_j);
    
    // Prove pos >= 1 /\ pos <= len from tracking invariant
    SL.phase4_c_pos_bounds sc sa (SZ.v k_val) (SZ.v len) (SZ.v vj_back + 1) val_j;
    
    // B[C[A[j]]-1] = A[j]  (CLRS uses 1-based, we use 0-based)
    A.op_Array_Assignment b (SZ.uint_to_t (pos - 1)) val_j;
    
    with sb_curr'. assert (A.pts_to b sb_curr');
    
    // C[A[j]]--
    V.op_Array_Assignment c (SZ.uint_to_t val_j) (pos - 1);
    
    with sc'. assert (V.pts_to c sc');
    
    // Step the tracking invariants
    SL.phase4_c_step sc sc' sa (SZ.v k_val) (SZ.v len) (SZ.v vj_back + 1) val_j;
    SL.phase4_b_step sc sc' sa sb_curr sb_curr' (SZ.v k_val) (SZ.v len) (SZ.v vj_back + 1) val_j;
    
    // Check if we're done (j_back == 0)
    if (vj_back = 0sz) {
      done := true;
    } else {
      // j_back--
      j_back := vj_back -^ 1sz;
    };
  };
  
  // Free count array
  with sc_final. assert (V.pts_to c sc_final);
  with sb_final. assert (A.pts_to b sb_final);
  
  // Prove sorted and permutation from completed invariants
  SL.phase4_final_sorted sc_final sa sb_final (SZ.v k_val) (SZ.v len);
  SL.phase4_final_perm sc_final sa sb_final (SZ.v k_val) (SZ.v len);
  // Flip permutation direction (phase4_final_perm proves sb'→sa, we need sa→sb')
  L.permutation_symmetric sb_final sa;
  // Prove output in_range from permutation + input in_range
  L.permutation_preserves_in_range sa sb_final (SZ.v k_val);
  
  V.free c;
  ()
  } // else len > 0
}
```
#pop-options

// ========== In-place Counting Sort (2-phase variant used by RadixSort) ==========

open Pulse.Lib.BoundedIntegers

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1 --split_queries always"
```pulse
fn counting_sort_inplace
  (a: A.array nat)
  (len: SZ.t)
  (k_val: SZ.t)
  (#s0: erased (Seq.seq nat))
requires
  A.pts_to a s0 **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len == Seq.length s0 /\
    Seq.length s0 == A.length a /\
    S.in_range s0 (SZ.v k_val) /\
    SZ.fits (SZ.v k_val + 2) /\
    SZ.fits (SZ.v len + SZ.v k_val + 2)
  )
ensures exists* s.
  A.pts_to a s **
  pure (
    Seq.length s == Seq.length s0 /\
    S.sorted s /\
    S.permutation s0 s /\
    S.in_range s (SZ.v k_val)
  )
{
  if (len = 0sz) {
    L.empty_sorted_perm s0 s0;
    ()
  } else {
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
  decreases (SZ.v n `Prims.op_Subtraction` SZ.v !j)
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
  let mut pos: SZ.t = 0sz;
  let mut cur_v: SZ.t = 0sz;
  let mut cur_v_nat: nat = 0;
  
  while (!cur_v <=^ k_val)
  invariant exists* vcv vpos vcvn sc sa.
    R.pts_to j n **
    R.pts_to cur_v vcv **
    R.pts_to cur_v_nat vcvn **
    R.pts_to pos vpos **
    V.pts_to c_arr sc **
    A.pts_to a sa **
    pure (
      SZ.v vcv <= SZ.v k_val + 1 /\
      vcvn == SZ.v vcv /\
      SZ.v vpos <= SZ.v n /\
      Seq.length sc == SZ.v k1 /\
      Seq.length sa == Seq.length s0 /\
      V.length c_arr == SZ.v k1 /\
      V.is_full_vec c_arr /\
      L.phase2_inv sa s0 (SZ.v vpos) (SZ.v vcv) k /\
      L.counts_match sc s0 k
    )
  decreases (Prims.op_Addition (SZ.v k_val) 1 `Prims.op_Subtraction` SZ.v !cur_v)
  {
    let vcv = !cur_v;
    let vpos = !pos;
    let vcvn = !cur_v_nat;
    with sc sa. assert (V.pts_to c_arr sc ** A.pts_to a sa);
    
    let cnt = V.op_Array_Access c_arr vcv;
    L.count_bounded s0 (SZ.v vcv);
    L.phase2_pos_bound sa s0 (SZ.v vpos) (SZ.v vcv) k;
    let cnt_sz : SZ.t = SZ.uint_to_t cnt;
    
    let mut w: SZ.t = 0sz;
    
    while (!w <^ cnt_sz)
    invariant exists* vw sa_inner.
      R.pts_to j n **
      R.pts_to cur_v vcv **
      R.pts_to cur_v_nat vcvn **
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
          Seq.index sa_inner i == vcvn) /\
        (forall (i:nat). i < SZ.v vpos ==> Seq.index sa_inner i == Seq.index sa i) /\
        (forall (i:nat). SZ.v vpos + SZ.v vw <= i /\ i < Seq.length sa_inner ==>
          Seq.index sa_inner i == Seq.index sa i)
      )
    decreases (SZ.v cnt_sz `Prims.op_Subtraction` SZ.v !w)
    {
      let vw = !w;
      with sa_w. assert (A.pts_to a sa_w);
      let write_pos = vpos + vw;
      assert (pure (SZ.v write_pos == SZ.v vpos + SZ.v vw));
      a.(write_pos) <- vcvn;
      with sa_new. assert (A.pts_to a sa_new);
      assert (pure (Seq.index sa_new (SZ.v write_pos) == vcvn));
      assert (pure (forall (j:nat). j < Seq.length sa_new /\ j <> SZ.v write_pos ==>
        Seq.index sa_new j == Seq.index sa_w j));
      w := vw + 1sz;
    };
    
    with sa_after. assert (A.pts_to a sa_after);
    L.phase2_step sa sa_after s0 (SZ.v vpos) (SZ.v cnt_sz) (SZ.v vcv) k;
    
    pos := vpos + cnt_sz;
    cur_v := vcv + 1sz;
    cur_v_nat := vcvn + 1;
  };
  
  with vcv_f vpos_f vcvn_f sc_f sa_f.
    assert (R.pts_to j n ** R.pts_to cur_v vcv_f ** R.pts_to cur_v_nat vcvn_f **
            R.pts_to pos vpos_f ** V.pts_to c_arr sc_f ** A.pts_to a sa_f);
  L.final_perm s0 sa_f k (SZ.v vpos_f);
  // Prove output in_range from permutation + input in_range
  L.permutation_preserves_in_range s0 sa_f (SZ.v k_val);
  V.free c_arr;
  ()
  } // else len > 0
}
```
#pop-options

// ========== Digit-keyed Counting Sort (for multi-digit RadixSort) ==========

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries always"
```pulse
fn counting_sort_by_digit
  (a: A.array nat)     // Input array (read-only)
  (b: A.array nat)     // Output array (will be written)
  (len: SZ.t)          // Length of arrays
  (base_val: SZ.t)     // Base for digit extraction
  (d: nat)             // Digit position
  (#sa: erased (Seq.seq nat))
  (#sb: erased (Seq.seq nat))
requires
  A.pts_to a #0.5R sa **
  A.pts_to b sb **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len <= A.length b /\
    SZ.v len == Seq.length sa /\
    SZ.v len == Seq.length sb /\
    Seq.length sa == A.length a /\
    Seq.length sb == A.length b /\
    SZ.v base_val >= 2 /\
    SZ.fits (SZ.v base_val + 2) /\
    SZ.fits (SZ.v len + SZ.v base_val + 2)
  )
ensures exists* sb'.
  A.pts_to a #0.5R sa **
  A.pts_to b sb' **
  pure (
    Seq.length sb' == Seq.length sa /\
    Stab.is_stable_sort_on_digit sa sb' d (SZ.v base_val)
  )
{
  if (len = 0sz) {
    DL.empty_is_stable_on_digit sa sb d (SZ.v base_val);
    ()
  } else {
  // Allocate count array C[0..base-1]
  let c : V.vec int = V.alloc 0 base_val;

  // ========== Phase 1: Initialize C[0..base-1] = 0 ==========
  // Already done by alloc

  // ========== Phase 2: Count occurrences by digit ==========
  // for j = 0 to len-1: key = digit(A[j], d, base); C[key]++

  let mut j : SZ.t = 0sz;

  assert (pure (Seq.length sa > 0));

  while (
    let vj = !j;
    vj <^ len
  )
  invariant exists* vj sc.
    R.pts_to j vj **
    A.pts_to a #0.5R sa **
    A.pts_to b sb **
    V.pts_to c sc **
    pure (
      SZ.v vj <= SZ.v len /\
      Seq.length sc == SZ.v base_val /\
      DL.digit_counts_match_prefix sc sa d (SZ.v base_val) (SZ.v vj)
    )
  decreases (SZ.v len `Prims.op_Subtraction` SZ.v !j)
  {
    let vj = !j;

    with sc. assert (V.pts_to c sc);

    // Read A[j]
    let val_j = A.op_Array_Access a vj;

    // Compute digit key
    let key = B.digit val_j d (SZ.v base_val);
    B.digit_bound val_j d (SZ.v base_val);

    // Read C[key]
    let count_old = V.op_Array_Access c (SZ.uint_to_t key);

    // C[key] = C[key] + 1
    V.op_Array_Assignment c (SZ.uint_to_t key) (count_old + 1);

    with sc'. assert (V.pts_to c sc');

    // Establish new invariant using lemma
    DL.digit_count_phase_step sa sc sc' (SZ.v vj) d (SZ.v base_val) key;

    // j++
    j := vj +^ 1sz;
  };

  // After phase 2: C contains digit counts
  with sc_after_phase2. assert (V.pts_to c sc_after_phase2);
  assert (pure (DL.digit_counts_match sc_after_phase2 sa d (SZ.v base_val)));

  // Initialize prefix sum tracking
  DL.digit_prefix_sum_init sc_after_phase2 sa d (SZ.v base_val);

  // ========== Phase 3: Prefix sum ==========
  // for i = 1 to base-1: C[i] = C[i] + C[i-1]

  let mut i : SZ.t = 1sz;

  while (
    let vi = !i;
    vi <^ base_val
  )
  invariant exists* vi sc.
    R.pts_to i vi **
    A.pts_to a #0.5R sa **
    A.pts_to b sb **
    V.pts_to c sc **
    pure (
      SZ.v vi >= 1 /\
      SZ.v vi <= SZ.v base_val /\
      Seq.length sc == SZ.v base_val /\
      DL.digit_prefix_sum_inv sc sa d (SZ.v base_val) (SZ.v vi)
    )
  decreases (SZ.v base_val `Prims.op_Subtraction` SZ.v !i)
  {
    let vi = !i;

    with sc. assert (V.pts_to c sc);

    let vi_minus_1 = vi -^ 1sz;

    // Read C[i-1]
    let prev_count = V.op_Array_Access c vi_minus_1;

    // Read C[i]
    let curr_count = V.op_Array_Access c vi;

    // C[i] = C[i] + C[i-1]
    V.op_Array_Assignment c vi (curr_count + prev_count);

    with sc'. assert (V.pts_to c sc');
    DL.digit_prefix_sum_step sc sc' sa d (SZ.v base_val) (SZ.v vi);

    // i++
    i := vi +^ 1sz;
  };

  // ========== Phase 4: Place elements (backwards) ==========

  // After phase 3: establish cumulative digit counts
  with sc_after_phase3. assert (V.pts_to c sc_after_phase3);
  DL.digit_prefix_sum_complete sc_after_phase3 sa d (SZ.v base_val);

  // Initialize phase 4 tracking invariants
  DL.phase4_c_inv_init sc_after_phase3 sa d (SZ.v base_val);
  DL.phase4_b_inv_init sc_after_phase3 sa sb d (SZ.v base_val);
  DL.phase4_content_inv_init sc_after_phase3 sa sb d (SZ.v base_val);

  // Start from len-1 (last element)
  let mut j_back : SZ.t = len -^ 1sz;
  let mut done : bool = false;

  while (
    let vdone = !done;
    not vdone
  )
  invariant exists* vj_back vdone sc sb_curr.
    R.pts_to j_back vj_back **
    R.pts_to done vdone **
    A.pts_to a #0.5R sa **
    V.pts_to c sc **
    A.pts_to b sb_curr **
    pure (
      Seq.length sc == SZ.v base_val /\
      Seq.length sb_curr == Seq.length sb /\
      (not vdone ==> SZ.v vj_back < SZ.v len) /\
      DL.phase4_c_inv sc sa d (SZ.v base_val) (SZ.v len) (if vdone then 0 else SZ.v vj_back + 1) /\
      DL.phase4_b_inv sc sa sb_curr d (SZ.v base_val) (SZ.v len) /\
      DL.phase4_content_inv sc sa sb_curr d (SZ.v base_val) (SZ.v len) (if vdone then 0 else SZ.v vj_back + 1)
    )
  decreases %[(if !done then 0 else 1); SZ.v !j_back]
  {
    let vj_back = !j_back;

    with sc. assert (V.pts_to c sc);
    with sb_curr. assert (A.pts_to b sb_curr);

    // From loop invariant: not vdone ==> SZ.v vj_back < SZ.v len
    assert (pure (SZ.v vj_back < SZ.v len));

    // Read A[j_back]
    let val_j = A.op_Array_Access a vj_back;

    // Compute digit key
    let key = B.digit val_j d (SZ.v base_val);
    B.digit_bound val_j d (SZ.v base_val);

    // Read C[key]
    let pos = V.op_Array_Access c (SZ.uint_to_t key);

    // Prove pos >= 1 /\ pos <= len from tracking invariant
    DL.phase4_pos_bounds sc sa d (SZ.v base_val) (SZ.v len) (SZ.v vj_back + 1) key;

    // B[pos-1] = val_j  (CLRS uses 1-based, we use 0-based)
    A.op_Array_Assignment b (SZ.uint_to_t (pos - 1)) val_j;

    with sb_curr'. assert (A.pts_to b sb_curr');

    // C[key]--
    V.op_Array_Assignment c (SZ.uint_to_t key) (pos - 1);

    with sc'. assert (V.pts_to c sc');

    // Step the tracking invariants
    DL.phase4_c_step sc sc' sa d (SZ.v base_val) (SZ.v len) (SZ.v vj_back + 1) key;
    DL.phase4_b_step sc sc' sa sb_curr sb_curr' d (SZ.v base_val) (SZ.v len) (SZ.v vj_back + 1) key;
    DL.phase4_content_step sc sc' sa sb_curr sb_curr' d (SZ.v base_val) (SZ.v len) (SZ.v vj_back + 1) key;

    // Check if we're done (j_back == 0)
    if (vj_back = 0sz) {
      done := true;
    } else {
      // j_back--
      j_back := vj_back -^ 1sz;
    };
  };

  // Free count array and prove final result
  with sc_final. assert (V.pts_to c sc_final);
  with sb_final. assert (A.pts_to b sb_final);

  // Prove is_stable_sort_on_digit from completed invariants
  DL.phase4_final_is_stable sc_final sa sb_final d (SZ.v base_val) (SZ.v len);

  V.free c;
  ()
  } // else len > 0
}
```
#pop-options

