(*
   KMP String Matching with Complexity Bound
   
   Proves O(n + m) comparison complexity for the Knuth-Morris-Pratt algorithm.
   Specifically: at most 2*n + 2*m character comparisons.
   
   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Each character comparison gets one ghost tick.
   
   Key insight from CLRS §32.4:
   - Prefix function computation: at most 2(m-1) comparisons
   - Matching phase: at most 2n comparisons
   - Total: at most 2n + 2m - 2 < 2(n + m) comparisons
   
   The proof uses amortized analysis with potential function Φ = k (or q in matcher).
   Inner loops only tick for actual failure-chain follows (not exit iterations),
   keeping the amortized sum (comparisons + potential) non-increasing.
   NO admits, NO assumes.
*)

module CLRS.Ch32.KMP.Complexity
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

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Pure Specification (from CLRS.Ch32.KMP) ==========

let is_prefix_suffix (#a: eqtype) (pattern: Seq.seq a) (q: nat{q < Seq.length pattern}) (k: nat) : prop =
  k <= q /\
  (forall (i: nat). i < k ==> Seq.index pattern i == Seq.index pattern (q - k + 1 + i))

let extends_to (#a: eqtype) (pattern: Seq.seq a) (q: nat{q + 1 < Seq.length pattern}) (k: nat) : prop =
  k <= q /\ k < Seq.length pattern /\
  is_prefix_suffix pattern q k /\
  Seq.index pattern k == Seq.index pattern (q + 1)

let prefix_suffix_extend (#a: eqtype) (pattern: Seq.seq a) 
    (q: nat{q + 1 < Seq.length pattern}) (k: nat)
  : Lemma (requires is_prefix_suffix pattern q k /\ k < Seq.length pattern /\
                     Seq.index pattern k == Seq.index pattern (q + 1))
          (ensures is_prefix_suffix pattern (q + 1) (k + 1))
  = assert (q + 1 - (k + 1) + 1 == q - k + 1)

let prefix_suffix_zero (#a: eqtype) (pattern: Seq.seq a) (q: nat{q < Seq.length pattern})
  : Lemma (is_prefix_suffix pattern q 0)
  = ()

let failure_chain (#a: eqtype) (pattern: Seq.seq a) 
    (q: nat{q < Seq.length pattern}) (k: nat) (j: nat)
  : Lemma (requires is_prefix_suffix pattern q k /\ k > 0 /\ k - 1 < Seq.length pattern /\
                     is_prefix_suffix pattern (k - 1) j)
          (ensures is_prefix_suffix pattern q j)
  = assert (j <= k - 1);
    assert (k <= q);
    assert (j <= q);
    assert (forall (i:nat). i < j ==> (k - 1) - j + 1 + i == k - j + i);
    assert (forall (i:nat). i < j ==> k - j + i < k);
    assert (forall (i:nat). i < j ==> q - k + 1 + (k - j + i) == q - j + 1 + i);
    ()

let extend_step_correct (#a: eqtype) (pattern: Seq.seq a)
    (q: nat{q + 1 < Seq.length pattern}) (k: nat) (chars_match: bool)
  : Lemma (requires is_prefix_suffix pattern q k /\ k < Seq.length pattern /\
                     (chars_match <==> Seq.index pattern k == Seq.index pattern (q + 1)) /\
                     (not chars_match ==> k == 0))
          (ensures is_prefix_suffix pattern (q + 1) (if chars_match then k + 1 else k))
  = if chars_match then prefix_suffix_extend pattern q k
    else prefix_suffix_zero pattern (q + 1)

let inner_step_preserves (#a: eqtype) (pattern: Seq.seq a)
    (q: nat{q < Seq.length pattern}) (k: nat) (pi_prev: nat) (should_update: bool)
  : Lemma (requires is_prefix_suffix pattern q k /\
                     (should_update ==> (k > 0 /\ k - 1 < Seq.length pattern /\
                                          is_prefix_suffix pattern (k - 1) pi_prev)) /\
                     (not should_update ==> true))
          (ensures is_prefix_suffix pattern q (if should_update then pi_prev else k))
  = if should_update then failure_chain pattern q k pi_prev else ()

let pi_correct (#a: eqtype) (pattern: Seq.seq a) (pi: Seq.seq SZ.t) : prop =
  Seq.length pi == Seq.length pattern /\
  Seq.length pattern > 0 /\
  (forall (q: nat). q < Seq.length pattern ==> 
    is_prefix_suffix pattern q (SZ.v (Seq.index pi q)))

let matches_at (text pattern: Seq.seq int) (s: nat) : prop =
  s + Seq.length pattern <= Seq.length text /\
  (forall (j: nat). j < Seq.length pattern ==> 
    Seq.index text (s + j) == Seq.index pattern j)

// ========== Complexity bounds ==========

// Prefix function: at most 2*(m-1) comparisons
let prefix_function_complexity_bound (c_final c_init m: nat) : prop =
  c_final >= c_init /\
  (if m >= 1 then c_final - c_init <= 2 * (m - 1) else c_final == c_init)

// Matching: at most 2*n comparisons
let matcher_complexity_bound (c_final c_init n: nat) : prop =
  c_final >= c_init /\
  c_final - c_init <= 2 * n

// ========== Compute Prefix Function with Complexity ==========

fn compute_prefix_function_complexity
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
      prefix_function_complexity_bound cf (reveal c0) (SZ.v m)
    )
{
  prefix_suffix_zero s_pat 0;
  
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
      vc_outer - reveal c0 + SZ.v vk <= 2 * (SZ.v vq - 1)
    )
  {
    let vq = !q;
    
    let mut done_inner: bool = false;
    
    // Inner loop invariant follows directly from outer: same amortized bound
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
        // Amortized: (comparisons - c0) + k <= 2*(q - 1) — same as outer
        vc_inner >= reveal c0 /\
        vc_inner - reveal c0 + SZ.v vk_inner <= 2 * (SZ.v vq - 1)
      )
    {
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
        
        // (vc+1) - c0 + pi_prev <= (vc+1) - c0 + (vk-1) = (vc - c0 + vk) <= 2*(vq-1)
        k := pi_prev
      } else {
        done_inner := true
      }
    };
    
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
    
    assert pure (is_prefix_suffix s_pat (SZ.v vq) (SZ.v final_k));
    assert pure (SZ.v final_k >= 0);
    assert pure (SZ.v final_k <= SZ.v vq);
    assert pure (SZ.v final_k < SZ.v vq + 1);
    
    // Amortized: after inner loop, (vc_after - c0) + vk_after <= 2*(vq-1).
    // After tick + possible k increment: sum <= 2*(vq-1) + 2 = 2*vq = 2*((vq+1) - 1).
    q := vq +^ 1sz
  };
  
  let final_q = !q;
  assert pure (SZ.v final_q == SZ.v m)
  // Postcondition: from invariant at vq=m, vc - c0 + vk <= 2*(m-1), vk >= 0
}

#pop-options

// ========== KMP Matcher with Complexity ==========

#push-options "--z3rlimit 50 --ifuel 1 --fuel 1"

fn kmp_matcher_complexity
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
      pi_correct s_pat s_pi
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
      matcher_complexity_bound cf (reveal c0) (SZ.v n)
    )
{
  let mut q: SZ.t = 0sz;
  let mut count_matches: SZ.t = 0sz;
  let mut i: SZ.t = 0sz;
  
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
      // q starts at 0, can increase by at most 1 per outer iteration
      vc >= reveal c0 /\
      vc - reveal c0 + SZ.v vq <= 2 * SZ.v vi
    )
  {
    let vi = !i;
    let vcount_outer = !count_matches;
    
    let mut done_follow: bool = false;
    
    // Inner loop invariant follows directly from outer: same amortized bound
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
        // Amortized: (comparisons - c0) + q <= 2*i — same as outer
        vc_inner >= reveal c0 /\
        vc_inner - reveal c0 + SZ.v vq_inner <= 2 * SZ.v vi
      )
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
        
        // (vc+1) - c0 + pi_val <= (vc+1) - c0 + (vq-1) = (vc - c0 + vq) <= 2*vi
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
    // Amortized: after inner loop, (vc_after - c0) + vq_after <= 2*vi.
    // After tick + possible q increment/reset: sum <= 2*vi + 2 = 2*(vi+1) = 2*vi_next.
  };
  
  let final_count = !count_matches;
  // Postcondition: from invariant at vi=n, vc - c0 + vq <= 2*n, vq >= 0
  
  final_count
}

#pop-options

// ========== Combined KMP with Complexity ==========

#push-options "--z3rlimit 50 --ifuel 1 --fuel 1"

//SNIPPET_START: kmp_total_complexity
// Combined complexity bound: prefix + matching
let kmp_total_complexity_bound (c_final c_init n m: nat) : prop =
  c_final >= c_init /\
  c_final - c_init <= 2 * n + 2 * m
//SNIPPET_END: kmp_total_complexity

fn kmp_string_match_with_complexity
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
      kmp_total_complexity_bound cf (reveal c0) (SZ.v n) (SZ.v m)
    )
{
  // Allocate pi array
  let pi: V.vec SZ.t = V.alloc 0sz m;
  
  // Phase 1: Compute prefix function
  compute_prefix_function_complexity pattern pi m ctr;
  
  // Phase 2: Run matcher
  let result = kmp_matcher_complexity text pattern pi n m ctr;
  
  // Combine bounds:
  // After phase 1: (c1 - c0) <= 2*(m-1) (since k_final >= 0)
  // After phase 2: (c2 - c1) <= 2*n (since q_final >= 0)
  // Therefore: c2 - c0 = (c2 - c1) + (c1 - c0) <= 2*n + 2*(m-1) <= 2*n + 2*m
  with cf. _;
  assert pure (kmp_total_complexity_bound cf (reveal c0) (SZ.v n) (SZ.v m));
  
  V.free pi;
  
  result
}

#pop-options
