(*
   KMP String Matching - Prefix Function Computation in Pulse
   
   Implements the COMPUTE-PREFIX-FUNCTION from CLRS Chapter 32.
   Given a pattern P[0..m-1], computes the failure function π[i] for each i,
   where π[i] is the length of the longest proper prefix of P[0..i] 
   that is also a suffix of P[0..i].
   
   NO admits. NO assumes.
*)

module CLRS.Ch32.KMP
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

#push-options "--z3rlimit 50 --ifuel 2 --fuel 2"

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Pure Specification ==========

// Does pattern[0..k-1] == pattern[q-k+1..q]? (prefix of length k matches suffix ending at q)
let is_prefix_suffix (#a: eqtype) (pattern: Seq.seq a) (q: nat{q < Seq.length pattern}) (k: nat) : prop =
  k <= q /\
  (forall (i: nat). i < k ==> Seq.index pattern i == Seq.index pattern (q - k + 1 + i))

// Is k a valid prefix-suffix length that could extend to position q+1?
// If pattern[k] == pattern[q+1], then k+1 is a prefix-suffix of pattern[0..q+1]
let extends_to (#a: eqtype) (pattern: Seq.seq a) (q: nat{q + 1 < Seq.length pattern}) (k: nat) : prop =
  k <= q /\ k < Seq.length pattern /\
  is_prefix_suffix pattern q k /\
  Seq.index pattern k == Seq.index pattern (q + 1)

// Key lemma: if is_prefix_suffix pattern q k and pattern[k] == pattern[q+1],
// then is_prefix_suffix pattern (q+1) (k+1)
let prefix_suffix_extend (#a: eqtype) (pattern: Seq.seq a) 
    (q: nat{q + 1 < Seq.length pattern}) (k: nat)
  : Lemma (requires is_prefix_suffix pattern q k /\ k < Seq.length pattern /\
                     Seq.index pattern k == Seq.index pattern (q + 1))
          (ensures is_prefix_suffix pattern (q + 1) (k + 1))
  = // Need: forall i < k+1. pattern[i] == pattern[(q+1)-(k+1)+1+i] = pattern[q-k+1+i]
    // For i < k: from is_prefix_suffix pattern q k
    // For i = k: pattern[k] == pattern[q+1] = pattern[q-k+1+k]
    assert (q + 1 - (k + 1) + 1 == q - k + 1)

// Key lemma: is_prefix_suffix pattern q 0 is always true
let prefix_suffix_zero (#a: eqtype) (pattern: Seq.seq a) (q: nat{q < Seq.length pattern})
  : Lemma (is_prefix_suffix pattern q 0)
  = ()

// Key lemma: if is_prefix_suffix pattern q k and k > 0, 
// then is_prefix_suffix pattern (k-1) is related to the failure chain
// Specifically: if pi_correct for positions < q, and k = pi[q], 
// then following pi gives shorter valid prefix-suffixes

// Failure chain lemma: if k is a prefix-suffix of pattern[0..q] (k > 0),
// and j is a prefix-suffix of pattern[0..k-1], then j is also a prefix-suffix of pattern[0..q]
let failure_chain (#a: eqtype) (pattern: Seq.seq a) 
    (q: nat{q < Seq.length pattern}) (k: nat) (j: nat)
  : Lemma (requires is_prefix_suffix pattern q k /\ k > 0 /\ k - 1 < Seq.length pattern /\
                     is_prefix_suffix pattern (k - 1) j)
          (ensures is_prefix_suffix pattern q j)
  = // j <= k-1 < q, so j <= q ✓
    // From is_prefix_suffix pattern (k-1) j: forall i < j. pattern[i] == pattern[k - j + i]
    // From is_prefix_suffix pattern q k: forall i < k. pattern[i] == pattern[q - k + 1 + i]
    // For each i < j: k - j + i < k, so pattern[k-j+i] == pattern[q-k+1+(k-j+i)] = pattern[q-j+1+i]
    // Chain: pattern[i] == pattern[k-j+i] == pattern[q-j+1+i]
    assert (j <= k - 1);
    assert (k <= q);
    assert (j <= q);
    // The forall instantiation should let Z3 chain the equalities
    assert (forall (i:nat). i < j ==> (k - 1) - j + 1 + i == k - j + i);
    assert (forall (i:nat). i < j ==> k - j + i < k);
    assert (forall (i:nat). i < j ==> q - k + 1 + (k - j + i) == q - j + 1 + i);
    // Z3 should now be able to prove: forall i < j. pattern[i] == pattern[q - j + 1 + i]
    ()

// Lemma for the extend step: we need k == 0 when chars don't match
// because the inner loop terminates with k == 0 || pattern[k] == pattern[q]
let extend_step_correct (#a: eqtype) (pattern: Seq.seq a)
    (q: nat{q + 1 < Seq.length pattern}) (k: nat) (chars_match: bool)
  : Lemma (requires is_prefix_suffix pattern q k /\ k < Seq.length pattern /\
                     (chars_match <==> Seq.index pattern k == Seq.index pattern (q + 1)) /\
                     (not chars_match ==> k == 0))
          (ensures is_prefix_suffix pattern (q + 1) (if chars_match then k + 1 else k))
  = if chars_match then prefix_suffix_extend pattern q k
    else prefix_suffix_zero pattern (q + 1)
// new_k is still a valid prefix-suffix of pattern[0..q]
let inner_step_preserves (#a: eqtype) (pattern: Seq.seq a)
    (q: nat{q < Seq.length pattern}) (k: nat) (pi_prev: nat) (should_update: bool)
  : Lemma (requires is_prefix_suffix pattern q k /\
                     (should_update ==> (k > 0 /\ k - 1 < Seq.length pattern /\
                                          is_prefix_suffix pattern (k - 1) pi_prev)) /\
                     (not should_update ==> true))
          (ensures is_prefix_suffix pattern q (if should_update then pi_prev else k))
  = if should_update then failure_chain pattern q k pi_prev else ()

// The full spec: pi[q] is a valid prefix-suffix
let pi_correct (#a: eqtype) (pattern: Seq.seq a) (pi: Seq.seq SZ.t) : prop =
  Seq.length pi == Seq.length pattern /\
  Seq.length pattern > 0 /\
  (forall (q: nat). q < Seq.length pattern ==> 
    is_prefix_suffix pattern q (SZ.v (Seq.index pi q)))

// ========== Pulse Implementation ==========

// Compute the prefix function for a pattern
fn compute_prefix_function
  (#a: eqtype)
  (#p_pat: perm)
  (pattern: array a)
  (pi: array SZ.t)
  (#s_pat: Ghost.erased (Seq.seq a))
  (m: SZ.t)
  requires 
    A.pts_to pattern #p_pat s_pat **
    A.pts_to pi #1.0R (Seq.create (SZ.v m) 0sz) **
    pure (
      SZ.v m == Seq.length s_pat /\
      Seq.length s_pat <= A.length pattern /\
      SZ.v m <= A.length pi /\
      SZ.v m > 0 /\
      SZ.fits (SZ.v m + 1)
    )
  returns _: unit
  ensures exists* s_pi.
    A.pts_to pattern #p_pat s_pat **
    A.pts_to pi #1.0R s_pi **
    pure (
      Seq.length s_pi == SZ.v m /\
      pi_correct s_pat s_pi
    )
{
  // π[0] = 0 (already initialized)
  // is_prefix_suffix pattern 0 0 is trivially true
  prefix_suffix_zero s_pat 0;
  
  // k tracks the length of the previous longest prefix suffix
  let mut k: SZ.t = 0sz;
  
  // q is the current position we're computing π[q] for
  let mut q: SZ.t = 1sz;
  
  // Outer loop: for q = 1 to m-1
  while (!q <^ m)
  invariant exists* vq vk s_pi_outer.
    R.pts_to q vq **
    R.pts_to k vk **
    A.pts_to pattern #p_pat s_pat **
    A.pts_to pi #1.0R s_pi_outer **
    pure (
      SZ.v vq <= SZ.v m /\
      SZ.v vq >= 1 /\
      SZ.v vk >= 0 /\
      SZ.v vk < SZ.v vq /\
      Seq.length s_pi_outer == SZ.v m /\
      // All positions < vq have correct prefix-suffix values
      (forall (i: nat). i < SZ.v vq ==> 
        is_prefix_suffix s_pat i (SZ.v (Seq.index s_pi_outer i))) /\
      // k is a valid prefix-suffix of pattern[0..vq-1]
      is_prefix_suffix s_pat (SZ.v vq - 1) (SZ.v vk)
    )
  {
    let vq = !q;
    let vk_init = !k;
    
    // Inner loop: while k > 0 && P[k] != P[q], set k = π[k-1]
    let mut done_inner: bool = false;
    
    while (not !done_inner)
    invariant exists* vdone vk_inner s_pi_inner.
      R.pts_to q vq **
      R.pts_to k vk_inner **
      R.pts_to done_inner vdone **
      A.pts_to pattern #p_pat s_pat **
      A.pts_to pi #1.0R s_pi_inner **
      pure (
        SZ.v vk_inner >= 0 /\
        SZ.v vk_inner < SZ.v vq /\
        SZ.v vq < SZ.v m /\
        Seq.length s_pi_inner == SZ.v m /\
        (forall (i: nat). i < SZ.v vq ==> 
          is_prefix_suffix s_pat i (SZ.v (Seq.index s_pi_inner i))) /\
        is_prefix_suffix s_pat (SZ.v vq - 1) (SZ.v vk_inner) /\
        // When done, k satisfies the exit condition
        (vdone ==> (SZ.v vk_inner == 0 \/ Seq.index s_pat (SZ.v vk_inner) == Seq.index s_pat (SZ.v vq)))
      )
    {
      let vk = !k;
      
      let safe_pi_idx: SZ.t = (if SZ.v vk > 0 then vk -^ 1sz else 0sz);
      let pi_prev = A.op_Array_Access pi safe_pi_idx;
      
      let pk = A.op_Array_Access pattern vk;
      let pq = A.op_Array_Access pattern vq;
      
      let should_update: bool = (SZ.v vk > 0 && pk <> pq);
      let new_k: SZ.t = (if should_update then pi_prev else vk);
      
      // Prove new_k is still a valid prefix-suffix of pattern[0..vq-1]
      inner_step_preserves s_pat (SZ.v vq - 1) (SZ.v vk) (SZ.v pi_prev) should_update;
      
      k := new_k;
      
      // If no update needed, we're done
      done_inner := not should_update
    };
    
    // After inner loop: k == 0 || pattern[k] == pattern[q]
    let vk_after_inner = !k;
    
    let pk_final = A.op_Array_Access pattern vk_after_inner;
    let pq_final = A.op_Array_Access pattern vq;
    
    let chars_match = (pk_final = pq_final);
    let new_k_final: SZ.t = (if chars_match then vk_after_inner +^ 1sz else vk_after_inner);
    
    // Prove is_prefix_suffix pattern vq new_k_final
    extend_step_correct s_pat (SZ.v vq - 1) (SZ.v vk_after_inner) chars_match;
    
    k := new_k_final;
    
    // π[q] = k
    let final_k = !k;
    A.op_Array_Assignment pi vq final_k;
    
    // Move to next position
    q := vq +^ 1sz;
  };
  
  let final_q = !q;
  assert pure (SZ.v final_q == SZ.v m);
}

#pop-options
