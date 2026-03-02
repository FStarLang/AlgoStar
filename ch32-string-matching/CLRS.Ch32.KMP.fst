(*
   KMP String Matching - Prefix Function Computation and Matching in Pulse
   
   Implements the COMPUTE-PREFIX-FUNCTION and KMP-MATCHER from CLRS Chapter 32.
   Given a pattern P[0..m-1], computes the failure function π[i] for each i,
   where π[i] is the length of the longest proper prefix of P[0..i] 
   that is also a suffix of P[0..i].

      Proves memory safety, prefix function maximality (pi is the LONGEST
   prefix-suffix at each position), O(n + m) comparison complexity, and
   full functional correctness: the returned count equals the total number
   of pattern occurrences in the text (count == count_matches_spec).
   Key insight from CLRS §32.4:
   - Prefix function computation: at most 2(m-1) comparisons
   - Matching phase: at most 2n comparisons
   - Total: at most 2n + 2m comparisons

   The proof uses amortized analysis with potential function Φ = k (or q in matcher).
   The functional correctness proof tracks Spec.is_max_prefix_below and
   Spec.follow_fail through the KMP loop, connecting the Pulse implementation
   to the pure specification via Bridge.pi_max_sz_to_spec_pi_max and
   Spec.kmp_count_step.

   NO admits. NO assumes.
*)

module CLRS.Ch32.KMP
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

#push-options "--z3rlimit 100 --ifuel 2 --fuel 2"

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Bridge = CLRS.Ch32.KMP.Bridge
module Spec = CLRS.Ch32.KMP.Spec

open CLRS.Ch32.KMP.PureDefs

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Compute Prefix Function ==========

//SNIPPET_START: compute_prefix_function_sig
fn compute_prefix_function
  (#a: eqtype)
  (#p_pat: perm)
  (pattern: array a)
  (pi: V.vec SZ.t)
  (#s_pat: Ghost.erased (Seq.seq a))
  (m: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires 
    A.pts_to pattern #p_pat s_pat **
    V.pts_to pi #1.0R (Seq.create (SZ.v m) 0sz) **
    GR.pts_to ctr c0 **
    pure (
      SZ.v m == Seq.length s_pat /\
      Seq.length s_pat <= A.length pattern /\
      SZ.v m <= V.length pi /\
      SZ.v m > 0 /\
      SZ.fits (SZ.v m + 1) /\
      SZ.fits (2 * (SZ.v m - 1))
    )
  returns _: unit
  ensures exists* s_pi (cf: nat).
    A.pts_to pattern #p_pat s_pat **
    V.pts_to pi #1.0R s_pi **
    GR.pts_to ctr cf **
    pure (
      Seq.length s_pi == SZ.v m /\
      pi_correct s_pat s_pi /\
      Bridge.pi_max_sz s_pat s_pi /\
      prefix_function_complexity_bound cf (reveal c0) (SZ.v m)
    )
//SNIPPET_END: compute_prefix_function_sig
{
  prefix_suffix_zero s_pat 0;
  Bridge.maximality_base s_pat (Seq.create (SZ.v m) 0sz);
  
  let mut k: SZ.t = 0sz;
  let mut q: SZ.t = 1sz;
  
  while (!q <^ m)
  invariant exists* vq vk s_pi_outer (vc_outer: nat).
    R.pts_to q vq **
    R.pts_to k vk **
    A.pts_to pattern #p_pat s_pat **
    V.pts_to pi #1.0R s_pi_outer **
    GR.pts_to ctr vc_outer **
    pure (
      SZ.v vq <= SZ.v m /\
      SZ.v vq >= 1 /\
      SZ.v vk >= 0 /\
      SZ.v vk < SZ.v vq /\
      Seq.length s_pi_outer == SZ.v m /\
      (forall (i: nat). i < SZ.v vq ==> 
        is_prefix_suffix s_pat i (SZ.v (Seq.index s_pi_outer i))) /\
      is_prefix_suffix s_pat (SZ.v vq - 1) (SZ.v vk) /\
      // Amortized potential: (comparisons - c0) + k <= 2*(q - 1)
      vc_outer >= reveal c0 /\
      vc_outer - reveal c0 + SZ.v vk <= 2 * (SZ.v vq - 1) /\
      // Maximality: pi is maximal at positions 0..vq-1
      Bridge.pi_max_sz_up_to s_pat s_pi_outer (SZ.v vq) /\
      // k equals pi[vq-1] (needed for inner loop init)
      SZ.v vk == SZ.v (Seq.index s_pi_outer (SZ.v vq - 1))
    )
  decreases (SZ.v m - SZ.v !q)
  {
    with _vq_g _vk_g s_pi_out _vc_g. _;
    let vq = !q;
    let vk_init = !k;
    Bridge.inner_maximality_init s_pat s_pi_out (SZ.v vq) (SZ.v vk_init);
    
    let mut done_inner: bool = false;
    
    while (not !done_inner)
    invariant exists* vdone vk_inner s_pi_inner (vc_inner: nat).
      R.pts_to q vq **
      R.pts_to k vk_inner **
      R.pts_to done_inner vdone **
      A.pts_to pattern #p_pat s_pat **
      V.pts_to pi #1.0R s_pi_inner **
      GR.pts_to ctr vc_inner **
      pure (
        SZ.v vk_inner >= 0 /\
        SZ.v vk_inner < SZ.v vq /\
        SZ.v vq < SZ.v m /\
        Seq.length s_pi_inner == SZ.v m /\
        (forall (i: nat). i < SZ.v vq ==> 
          is_prefix_suffix s_pat i (SZ.v (Seq.index s_pi_inner i))) /\
        is_prefix_suffix s_pat (SZ.v vq - 1) (SZ.v vk_inner) /\
        (vdone ==> (SZ.v vk_inner == 0 \/ Seq.index s_pat (SZ.v vk_inner) == Seq.index s_pat (SZ.v vq))) /\
        // Amortized: (comparisons - c0) + k <= 2*(q - 1)
        vc_inner >= reveal c0 /\
        vc_inner - reveal c0 + SZ.v vk_inner <= 2 * (SZ.v vq - 1) /\
        // Mismatch invariant: all PS above current k have been checked
        Bridge.all_ps_above_mismatch s_pat (SZ.v vq) (SZ.v vk_inner) /\
        // Maximality preserved (pi array unchanged in inner loop)
        Bridge.pi_max_sz_up_to s_pat s_pi_inner (SZ.v vq)
      )
    // TODO: decreases
    {
      with _vd_il _vki_il s_pi_il _vci_il. _;
      let vk = !k;
      
      let safe_pi_idx: SZ.t = (if SZ.v vk > 0 then vk -^ 1sz else 0sz);
      let pi_prev = V.op_Array_Access pi safe_pi_idx;
      
      let pk = A.op_Array_Access pattern vk;
      let pq = A.op_Array_Access pattern vq;
      
      let should_update: bool = (SZ.v vk > 0 && pk <> pq);
      
      if should_update {
        // Follow failure chain — count this comparison, k decreases
        tick ctr;
        
        assert pure (SZ.v vk > 0 /\ is_prefix_suffix s_pat (SZ.v vk - 1) (SZ.v pi_prev));
        assert pure (SZ.v pi_prev <= SZ.v vk - 1);
        
        inner_step_preserves s_pat (SZ.v vq - 1) (SZ.v vk) (SZ.v pi_prev) true;
        
        Bridge.inner_maximality_step s_pat s_pi_il (SZ.v vq) (SZ.v vk) (SZ.v pi_prev);
        
        k := pi_prev
      } else {
        done_inner := true
      }
    };
    
    with _ _vd_post _vki_post s_pi_post _vci_post. _;
    let vk_after_inner = !k;
    
    let pk_final = A.op_Array_Access pattern vk_after_inner;
    let pq_final = A.op_Array_Access pattern vq;
    
    // Count the extend-check comparison
    tick ctr;
    
    let chars_match = (pk_final = pq_final);
    let new_k_final: SZ.t = (if chars_match then vk_after_inner +^ 1sz else vk_after_inner);
    
    extend_step_correct s_pat (SZ.v vq - 1) (SZ.v vk_after_inner) chars_match;
    
    k := new_k_final;
    
    let final_k = !k;
    V.op_Array_Assignment pi vq final_k;
    
    Bridge.extend_maximality s_pat (Seq.upd s_pi_post (SZ.v vq) final_k) (SZ.v vq) (SZ.v vk_after_inner) chars_match;
    
    assert pure (is_prefix_suffix s_pat (SZ.v vq) (SZ.v final_k));
    assert pure (SZ.v final_k >= 0);
    assert pure (SZ.v final_k <= SZ.v vq);
    assert pure (SZ.v final_k < SZ.v vq + 1);
    
    q := vq +^ 1sz
  };
  
  with _ _vq_f _vk_f s_pi_f _vc_f. _;
  Bridge.up_to_full s_pat s_pi_f;
  
  let final_q = !q;
  assert pure (SZ.v final_q == SZ.v m)
}

#pop-options

// ========== KMP Matcher ==========

#push-options "--z3rlimit 100 --ifuel 1 --fuel 1"

//SNIPPET_START: kmp_matcher_sig
fn kmp_matcher
  (#p_text #p_pat #p_pi: perm)
  (text: array int)
  (pattern: array int)
  (pi: V.vec SZ.t)
  (#s_text: Ghost.erased (Seq.seq int))
  (#s_pat: Ghost.erased (Seq.seq int))
  (#s_pi: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (m: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires 
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    V.pts_to pi #p_pi s_pi **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s_text /\
      SZ.v m == Seq.length s_pat /\
      Seq.length s_text <= A.length text /\
      Seq.length s_pat <= A.length pattern /\
      Seq.length s_pi <= V.length pi /\
      SZ.v m > 0 /\
      SZ.v n >= SZ.v m /\
      SZ.fits (SZ.v n + 1) /\
      SZ.fits (SZ.v m + 1) /\
      SZ.fits (2 * SZ.v n) /\
      pi_correct s_pat s_pi /\
      Bridge.pi_max_sz s_pat s_pi
    )
  returns count: SZ.t
  ensures exists* (cf: nat).
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    V.pts_to pi #p_pi s_pi **
    GR.pts_to ctr cf **
    pure (
      SZ.v count >= 0 /\
      SZ.v count <= SZ.v n + 1 /\
      SZ.v count == Spec.count_matches_spec (reveal s_text) (reveal s_pat) (SZ.v n) (SZ.v m) /\
      matcher_complexity_bound cf (reveal c0) (SZ.v n)
    )
//SNIPPET_END: kmp_matcher_sig
{
  // Convert pi_max_sz to Spec.pi_max for the int-sequence version
  Bridge.pi_max_sz_to_spec_pi_max (reveal s_pat) (reveal s_pi);
  
  let mut q: SZ.t = 0sz;
  let mut count_matches: SZ.t = 0sz;
  let mut i: SZ.t = 0sz;
  
  // Main loop: scan through text
  while (!i <^ n)
  invariant exists* vi vq vcount (vc: nat).
    R.pts_to i vi **
    R.pts_to q vq **
    R.pts_to count_matches vcount **
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    V.pts_to pi #p_pi s_pi **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      SZ.v vq >= 0 /\
      SZ.v vq < SZ.v m /\
      SZ.v vcount >= 0 /\
      SZ.v vcount <= SZ.v vi + 1 /\
      // Amortized invariant: (comparisons - c0) + q <= 2*i
      vc >= reveal c0 /\
      vc - reveal c0 + SZ.v vq <= 2 * SZ.v vi /\
      // Spec invariants
      Spec.is_max_prefix_below (reveal s_text) (reveal s_pat) (SZ.v vi) (SZ.v vq) /\
      (SZ.v vi >= SZ.v m ==>
        SZ.v vcount == Spec.count_before (reveal s_text) (reveal s_pat) (SZ.v vi - SZ.v m + 1)) /\
      (SZ.v vi < SZ.v m ==> SZ.v vcount == 0)
    )
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    let vcount_outer = !count_matches;
    let vq_init = !q;
    
    let mut done_follow: bool = false;
    
    while (not !done_follow)
    invariant exists* vdone vq_inner vcount_inner (vc_inner: nat).
      R.pts_to i vi **
      R.pts_to q vq_inner **
      R.pts_to count_matches vcount_inner **
      R.pts_to done_follow vdone **
      A.pts_to text #p_text s_text **
      A.pts_to pattern #p_pat s_pat **
      V.pts_to pi #p_pi s_pi **
      GR.pts_to ctr vc_inner **
      pure (
        SZ.v vi < SZ.v n /\
        SZ.v vq_inner >= 0 /\
        SZ.v vq_inner < SZ.v m /\
        SZ.v vcount_inner == SZ.v vcount_outer /\
        SZ.v vcount_inner >= 0 /\
        SZ.v vcount_inner <= SZ.v vi + 1 /\
        (vdone ==> (SZ.v vq_inner == 0 \/ Seq.index s_pat (SZ.v vq_inner) == Seq.index s_text (SZ.v vi))) /\
        // Amortized: (comparisons - c0) + q <= 2*i
        vc_inner >= reveal c0 /\
        vc_inner - reveal c0 + SZ.v vq_inner <= 2 * SZ.v vi /\
        // Spec: carry outer invariants and track follow_fail
        Spec.is_max_prefix_below (reveal s_text) (reveal s_pat) (SZ.v vi) (SZ.v vq_init) /\
        (SZ.v vi >= SZ.v m ==>
          SZ.v vcount_outer == Spec.count_before (reveal s_text) (reveal s_pat) (SZ.v vi - SZ.v m + 1)) /\
        (SZ.v vi < SZ.v m ==> SZ.v vcount_outer == 0) /\
        Spec.follow_fail (reveal s_pat) (Bridge.sz_seq_to_int (reveal s_pi)) (SZ.v vq_init) (Seq.index (reveal s_text) (SZ.v vi)) ==
          Spec.follow_fail (reveal s_pat) (Bridge.sz_seq_to_int (reveal s_pi)) (SZ.v vq_inner) (Seq.index (reveal s_text) (SZ.v vi))
      )
    // TODO: decreases
    {
      let vq = !q;
      let text_char = A.op_Array_Access text vi;
      let pat_char = A.op_Array_Access pattern vq;
      
      let should_follow: bool = (SZ.v vq > 0 && pat_char <> text_char);
      
      if should_follow {
        // Follow failure chain — count this comparison, q decreases
        tick ctr;
        let safe_idx = vq -^ 1sz;
        let pi_val = V.op_Array_Access pi safe_idx;
        
        assert pure (is_prefix_suffix s_pat (SZ.v vq - 1) (SZ.v pi_val));
        assert pure (SZ.v pi_val <= SZ.v vq - 1);
        assert pure (SZ.v pi_val < SZ.v vq);
        
        // Connect pi_val to pi_int for follow_fail tracking
        Bridge.sz_seq_to_int_index (reveal s_pi) (SZ.v vq - 1);
        
        q := pi_val
      } else {
        done_follow := true
      }
    };
    
    let vq_after = !q;
    let text_char_final = A.op_Array_Access text vi;
    let pat_char_final = A.op_Array_Access pattern vq_after;
    
    // Count the extend-check comparison
    tick ctr;
    
    let chars_match = (pat_char_final = text_char_final);
    let new_q_val: SZ.t = (if chars_match then vq_after +^ 1sz else vq_after);
    
    q := new_q_val;
    
    let vq_final = !q;
    assert pure (SZ.v vq_final <= SZ.v m);
    let have_match = (vq_final = m);
    assert pure (not have_match ==> SZ.v vq_final < SZ.v m);
    
    let old_count = !count_matches;
    let new_count_val: SZ.t = (if have_match then old_count +^ 1sz else old_count);
    
    let pi_idx_for_reset = m -^ 1sz;
    let pi_val_for_reset = V.op_Array_Access pi pi_idx_for_reset;
    let new_q_after_match: SZ.t = (if have_match then pi_val_for_reset else vq_final);
    
    // Connect Pulse result to spec via kmp_count_step
    Bridge.sz_seq_to_int_index (reveal s_pi) (SZ.v m - 1);
    Spec.kmp_count_step (reveal s_text) (reveal s_pat) (Bridge.sz_seq_to_int (reveal s_pi)) (SZ.v vi) (SZ.v vq_init) (SZ.v vcount_outer);
    
    let vi_next = vi +^ 1sz;
    assert pure (SZ.v old_count <= SZ.v vi + 1);
    assert pure (SZ.v new_count_val <= SZ.v vi + 2);
    assert pure (SZ.v vi_next == SZ.v vi + 1);
    assert pure (SZ.v new_count_val <= SZ.v vi_next + 1);
    assert pure (SZ.v pi_val_for_reset < SZ.v m);
    assert pure (SZ.v new_q_after_match < SZ.v m);
    
    count_matches := new_count_val;
    q := new_q_after_match;
    
    i := vi_next
  };
  
  // After loop: convert count_before to count_matches_spec
  Spec.count_before_eq_spec (reveal s_text) (reveal s_pat) (SZ.v n) (SZ.v m);
  
  let final_count = !count_matches;
  final_count
}

#pop-options

// ========== Combined KMP with Complexity ==========

#push-options "--z3rlimit 50 --ifuel 1 --fuel 1"

fn kmp_string_match
  (#p_text #p_pat: perm)
  (text: array int)
  (pattern: array int)
  (#s_text: Ghost.erased (Seq.seq int))
  (#s_pat: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (m: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires 
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s_text /\
      SZ.v m == Seq.length s_pat /\
      Seq.length s_text <= A.length text /\
      Seq.length s_pat <= A.length pattern /\
      SZ.v m > 0 /\
      SZ.v n >= SZ.v m /\
      SZ.fits (SZ.v n + 1) /\
      SZ.fits (SZ.v m + 1) /\
      SZ.fits (2 * SZ.v n) /\
      SZ.fits (2 * (SZ.v m - 1)) /\
      SZ.fits (2 * SZ.v n + 2 * SZ.v m)
    )
  returns count: SZ.t
  ensures exists* (cf: nat).
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    GR.pts_to ctr cf **
    pure (
      SZ.v count >= 0 /\
      SZ.v count <= SZ.v n + 1 /\
      SZ.v count == Spec.count_matches_spec (reveal s_text) (reveal s_pat) (SZ.v n) (SZ.v m) /\
      kmp_total_complexity_bound cf (reveal c0) (SZ.v n) (SZ.v m)
    )
{
  // Allocate pi array
  let pi: V.vec SZ.t = V.alloc 0sz m;
  
  // Phase 1: Compute prefix function
  compute_prefix_function pattern pi m ctr;
  
  // Phase 2: Run matcher
  let result = kmp_matcher text pattern pi n m ctr;
  
  with cf. _;
  assert pure (kmp_total_complexity_bound cf (reveal c0) (SZ.v n) (SZ.v m));
  
  V.free pi;
  
  result
}

#pop-options
