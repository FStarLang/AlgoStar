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

#push-options "--z3rlimit 100 --ifuel 2 --fuel 2"

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
    
    // After this assignment, pi[vq] = final_k and is_prefix_suffix pattern vq final_k
    // We need to show this for the invariant restoration
    assert pure (is_prefix_suffix s_pat (SZ.v vq) (SZ.v final_k));
    assert pure (SZ.v final_k >= 0);
    assert pure (SZ.v final_k <= SZ.v vq);
    assert pure (SZ.v final_k < SZ.v vq + 1);
    
    // Move to next position
    q := vq +^ 1sz;
  };
  
  let final_q = !q;
  assert pure (SZ.v final_q == SZ.v m);
}

#pop-options

// ========== KMP Matcher Specification ==========

#push-options "--z3rlimit 20 --ifuel 2 --fuel 2"

// Does the pattern match at position s in the text?
let matches_at (text pattern: Seq.seq int) (s: nat) : prop =
  s + Seq.length pattern <= Seq.length text /\
  (forall (j: nat). j < Seq.length pattern ==> 
    Seq.index text (s + j) == Seq.index pattern j)

// Pure check if pattern matches at position s
let rec check_match_at (text pattern: Seq.seq int) (s: nat) (j: nat) 
  : Tot bool (decreases (Seq.length pattern - j))
  = if j >= Seq.length pattern then true
    else if s + j >= Seq.length text then false
    else if Seq.index text (s + j) <> Seq.index pattern j then false
    else check_match_at text pattern s (j + 1)

// Count matches from position s to n
let rec count_matches_up_to (text pattern: Seq.seq int) (n m s: nat) 
  : Pure nat 
    (requires s <= n /\ m > 0) 
    (ensures fun _ -> True) 
    (decreases (n - s))
  = if s + m > n then 0
    else (if check_match_at text pattern s 0 then 1 else 0) + 
         count_matches_up_to text pattern n m (s + 1)

// The spec: count all matches in text
let count_matches_spec (text pattern: Seq.seq int) (n m: nat{m > 0}) : nat =
  count_matches_up_to text pattern n m 0

#pop-options

// ========== KMP Matcher Implementation ==========

#push-options "--z3rlimit 50 --ifuel 1 --fuel 1"

fn kmp_matcher
  (#p_text #p_pat #p_pi: perm)
  (text: array int)
  (pattern: array int)
  (pi: array SZ.t)
  (#s_text: Ghost.erased (Seq.seq int))
  (#s_pat: Ghost.erased (Seq.seq int))
  (#s_pi: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (m: SZ.t)
  requires 
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    A.pts_to pi #p_pi s_pi **
    pure (
      SZ.v n == Seq.length s_text /\
      SZ.v m == Seq.length s_pat /\
      Seq.length s_text <= A.length text /\
      Seq.length s_pat <= A.length pattern /\
      Seq.length s_pi <= A.length pi /\
      SZ.v m > 0 /\
      SZ.v n >= SZ.v m /\
      SZ.fits (SZ.v n + 1) /\
      SZ.fits (SZ.v m + 1) /\
      pi_correct s_pat s_pi
    )
  returns count: SZ.t
  ensures 
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    A.pts_to pi #p_pi s_pi **
    pure (
      SZ.v count >= 0 /\
      SZ.v count <= SZ.v n + 1
    )
{
  let mut q: SZ.t = 0sz;               // number of characters matched
  let mut count_matches: SZ.t = 0sz;  // number of matches found
  let mut i: SZ.t = 0sz;               // current position in text
  
  // Main loop: scan through text
  while (!i <^ n)
  invariant exists* vi vq vcount.
    R.pts_to i vi **
    R.pts_to q vq **
    R.pts_to count_matches vcount **
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    A.pts_to pi #p_pi s_pi **
    pure (
      SZ.v vi <= SZ.v n /\
      SZ.v vq >= 0 /\
      SZ.v vq < SZ.v m /\
      SZ.v vcount >= 0 /\
      SZ.v vcount <= SZ.v vi + 1
    )
  {
    let vi = !i;
    let vq_init = !q;
    let vcount_outer = !count_matches;
    
    // Inner while loop: follow failure links while chars don't match
    let mut done_follow: bool = false;
    
    while (not !done_follow)
    invariant exists* vdone vq_inner vcount_inner.
      R.pts_to i vi **
      R.pts_to q vq_inner **
      R.pts_to count_matches vcount_inner **
      R.pts_to done_follow vdone **
      A.pts_to text #p_text s_text **
      A.pts_to pattern #p_pat s_pat **
      A.pts_to pi #p_pi s_pi **
      pure (
        SZ.v vi < SZ.v n /\
        SZ.v vq_inner >= 0 /\
        SZ.v vq_inner < SZ.v m /\
        SZ.v vcount_inner == SZ.v vcount_outer /\
        SZ.v vcount_inner >= 0 /\
        SZ.v vcount_inner <= SZ.v vi + 1 /\
        (vdone ==> (SZ.v vq_inner == 0 \/ Seq.index s_pat (SZ.v vq_inner) == Seq.index s_text (SZ.v vi)))
      )
    {
      let vq = !q;
      let text_char = A.op_Array_Access text vi;
      let pat_char = A.op_Array_Access pattern vq;
      
      let should_follow: bool = (SZ.v vq > 0 && pat_char <> text_char);
      
      if should_follow {
        let safe_idx = vq -^ 1sz;
        let pi_val = A.op_Array_Access pi safe_idx;
        // pi[vq-1] is a valid prefix-suffix for pattern[0..vq-1]
        // By failure_chain lemma, it's also valid for the current position
        q := pi_val;
        assert pure (is_prefix_suffix s_pat (SZ.v vq - 1) (SZ.v pi_val))
      } else {
        done_follow := true
      }
    };
    
    // After inner loop: q == 0 or pattern[q] == text[i]
    let vq_after = !q;
    let text_char_final = A.op_Array_Access text vi;
    let pat_char_final = A.op_Array_Access pattern vq_after;
    
    // Check if characters match
    let chars_match = (pat_char_final = text_char_final);
    
    // Compute new q value (will be written only if chars match)
    let new_q_val: SZ.t = (if chars_match then vq_after +^ 1sz else vq_after);
    
    // Write new q
    q := new_q_val;
    
    // Check if we have a complete match  
    let vq_final = !q;
    let have_match = (vq_final = m);
    
    // Compute new count value
    let old_count = !count_matches;
    let new_count_val: SZ.t = (if have_match then old_count +^ 1sz else old_count);
    
    // Compute new q value (reset to pi[m-1] if match, else stay same)
    let pi_idx_for_reset = m -^ 1sz;
    let pi_val_for_reset = A.op_Array_Access pi pi_idx_for_reset;
    let new_q_after_match: SZ.t = (if have_match then pi_val_for_reset else vq_final);
    
    // Assertions to help prove the invariant
    let vi_next = vi +^ 1sz;
    assert pure (SZ.v old_count <= SZ.v vi + 1);
    assert pure (SZ.v new_count_val <= SZ.v vi + 2);
    assert pure (SZ.v vi_next == SZ.v vi + 1);
    assert pure (SZ.v new_count_val <= SZ.v vi_next + 1);
    assert pure (SZ.v pi_val_for_reset < SZ.v m);
    assert pure (SZ.v new_q_after_match < SZ.v m);
    
    // Write new values unconditionally
    count_matches := new_count_val;
    q := new_q_after_match;
    
    // Move to next position in text
    i := vi_next
  };
  
  let final_count = !count_matches;
  final_count
}

#pop-options
