(*
   KMP String Matching - Pure Specification Definitions

   Shared pure definitions used by both the Pulse implementation (KMP.fst)
   and the Bridge module (Bridge.fst). Factored out to avoid circular
   dependencies.
*)
module CLRS.Ch32.KMP.PureDefs

open FStar.Seq
open FStar.SizeT

module SZ = FStar.SizeT

// ========== Pure Specification ==========

//SNIPPET_START: is_prefix_suffix
// Does pattern[0..k-1] == pattern[q-k+1..q]? (prefix of length k matches suffix ending at q)
let is_prefix_suffix (#a: eqtype) (pattern: seq a) (q: nat{q < length pattern}) (k: nat) : prop =
  k <= q /\
  (forall (i: nat). i < k ==> index pattern i == index pattern (q - k + 1 + i))
//SNIPPET_END: is_prefix_suffix

// Is k a valid prefix-suffix length that could extend to position q+1?
let extends_to (#a: eqtype) (pattern: seq a) (q: nat{q + 1 < length pattern}) (k: nat) : prop =
  k <= q /\ k < length pattern /\
  is_prefix_suffix pattern q k /\
  index pattern k == index pattern (q + 1)

// Key lemma: if is_prefix_suffix pattern q k and pattern[k] == pattern[q+1],
// then is_prefix_suffix pattern (q+1) (k+1)
let prefix_suffix_extend (#a: eqtype) (pattern: seq a) 
    (q: nat{q + 1 < length pattern}) (k: nat)
  : Lemma (requires is_prefix_suffix pattern q k /\ k < length pattern /\
                     index pattern k == index pattern (q + 1))
          (ensures is_prefix_suffix pattern (q + 1) (k + 1))
  = assert (q + 1 - (k + 1) + 1 == q - k + 1)

// Key lemma: is_prefix_suffix pattern q 0 is always true
let prefix_suffix_zero (#a: eqtype) (pattern: seq a) (q: nat{q < length pattern})
  : Lemma (is_prefix_suffix pattern q 0)
  = ()

// Failure chain lemma: if k is a prefix-suffix of pattern[0..q] (k > 0),
// and j is a prefix-suffix of pattern[0..k-1], then j is also a prefix-suffix of pattern[0..q]
let failure_chain (#a: eqtype) (pattern: seq a) 
    (q: nat{q < length pattern}) (k: nat) (j: nat)
  : Lemma (requires is_prefix_suffix pattern q k /\ k > 0 /\ k - 1 < length pattern /\
                     is_prefix_suffix pattern (k - 1) j)
          (ensures is_prefix_suffix pattern q j)
  = assert (j <= k - 1);
    assert (k <= q);
    assert (j <= q);
    assert (forall (i:nat). i < j ==> (k - 1) - j + 1 + i == k - j + i);
    assert (forall (i:nat). i < j ==> k - j + i < k);
    assert (forall (i:nat). i < j ==> q - k + 1 + (k - j + i) == q - j + 1 + i);
    ()

let extend_step_correct (#a: eqtype) (pattern: seq a)
    (q: nat{q + 1 < length pattern}) (k: nat) (chars_match: bool)
  : Lemma (requires is_prefix_suffix pattern q k /\ k < length pattern /\
                     (chars_match <==> index pattern k == index pattern (q + 1)) /\
                     (not chars_match ==> k == 0))
          (ensures is_prefix_suffix pattern (q + 1) (if chars_match then k + 1 else k))
  = if chars_match then prefix_suffix_extend pattern q k
    else prefix_suffix_zero pattern (q + 1)

let inner_step_preserves (#a: eqtype) (pattern: seq a)
    (q: nat{q < length pattern}) (k: nat) (pi_prev: nat) (should_update: bool)
  : Lemma (requires is_prefix_suffix pattern q k /\
                     (should_update ==> (k > 0 /\ k - 1 < length pattern /\
                                          is_prefix_suffix pattern (k - 1) pi_prev)) /\
                     (not should_update ==> true))
          (ensures is_prefix_suffix pattern q (if should_update then pi_prev else k))
  = if should_update then failure_chain pattern q k pi_prev else ()

//SNIPPET_START: pi_correct
// The full spec: pi[q] is a valid prefix-suffix
let pi_correct (#a: eqtype) (pattern: seq a) (pi: seq SZ.t) : prop =
  length pi == length pattern /\
  length pattern > 0 /\
  (forall (q: nat). q < length pattern ==> 
    is_prefix_suffix pattern q (SZ.v (index pi q)))
//SNIPPET_END: pi_correct

// ========== KMP Matcher Specification ==========

// Does the pattern match at position s in the text?
let matches_at (text pattern: seq int) (s: nat) : prop =
  s + length pattern <= length text /\
  (forall (j: nat). j < length pattern ==> 
    index text (s + j) == index pattern j)

// ========== Complexity bounds ==========

// Prefix function: at most 2*(m-1) comparisons
let prefix_function_complexity_bound (c_final c_init m: nat) : prop =
  c_final >= c_init /\
  (if m >= 1 then c_final - c_init <= 2 * (m - 1) else c_final == c_init)

// Matching: at most 2*n comparisons
let matcher_complexity_bound (c_final c_init n: nat) : prop =
  c_final >= c_init /\
  c_final - c_init <= 2 * n

//SNIPPET_START: kmp_total_complexity
// Combined complexity bound: prefix + matching
let kmp_total_complexity_bound (c_final c_init n m: nat) : prop =
  c_final >= c_init /\
  c_final - c_init <= 2 * n + 2 * m
//SNIPPET_END: kmp_total_complexity
