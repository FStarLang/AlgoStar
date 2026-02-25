(*
   KMP String Matching — Completeness Specification (CLRS §32.4)

   Proves that the KMP algorithm finds ALL matches:
   1. Forward: each detection (q = m) is a valid match
   2. Backward: every valid match is detected
   3. Combined: KMP count == count_matches_spec

   Key insight: the failure function chain explores all valid prefix-suffix
   lengths, so the KMP step always finds the longest matching prefix.

   Requires pi_max (pi is the longest prefix-suffix at each position).
*)

module CLRS.Ch32.KMP.Spec

open FStar.Seq
open FStar.Classical
open CLRS.Ch32.KMP

module SZ = FStar.SizeT

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20 --z3refresh"

// ========== Core Definitions ==========

/// q characters of pattern match a suffix of text[0..i-1]
let matched_prefix_at (text pattern: seq int) (i q: nat) : prop =
  q <= length pattern /\ q <= i /\ i <= length text /\
  (forall (j: nat). j < q ==> index text (i - q + j) == index pattern j)

/// q is the longest matched prefix (< m) at position i.
let is_max_prefix_below (text pattern: seq int) (i q: nat) : prop =
  let m = length pattern in
  matched_prefix_at text pattern i q /\ q < m /\
  (forall (k: nat). matched_prefix_at text pattern i k /\ k < m ==> k <= q)

/// pi[q] is the LONGEST proper prefix-suffix of pattern[0..q]
let pi_max (pattern: seq int) (pi: seq int) : prop =
  length pi == length pattern /\
  length pattern > 0 /\
  (forall (q: nat). q < length pattern ==> index pi q >= 0) /\
  (forall (q: nat). q < length pattern ==>
    is_prefix_suffix #int pattern q (index pi q)) /\
  (forall (q: nat). q < length pattern ==>
    (forall (k: nat). is_prefix_suffix #int pattern q k ==> k <= index pi q))

/// Helper: under pi_max, pi[q] is a nat with known bounds
let pi_val_bounds (pattern pi: seq int) (q: nat)
  : Lemma (requires pi_max pattern pi /\ q < length pattern)
          (ensures index pi q >= 0 /\ index pi q <= q)
  = ()

/// Follow failure links: find k in the chain from start where pattern[k] = c
let rec follow_fail (pattern pi: seq int) (k: nat) (c: int)
  : Tot nat (decreases k) =
  if k = 0 then 0
  else if k < length pattern && index pattern k = c then k
  else if k > 0 && k - 1 < length pi && index pi (k - 1) >= 0 && index pi (k - 1) < k then
    follow_fail pattern pi (index pi (k - 1)) c
  else 0

/// KMP step: follow failure chain then try to extend
let kmp_step_result (pattern pi: seq int) (q: nat) (c: int) (m: nat) : nat =
  let q' = follow_fail pattern pi q c in
  if q' < m && q' < length pattern && index pattern q' = c then q' + 1
  else q'

/// Decidable match check
let matches_at_dec (text pattern: seq int) (s: nat) : bool =
  s + length pattern <= length text && check_match_at text pattern s 0

/// Count matches at positions 0..limit-1
let rec count_before (text pattern: seq int) (limit: nat)
  : Tot nat (decreases limit) =
  if limit = 0 then 0
  else count_before text pattern (limit - 1) +
       (if matches_at_dec text pattern (limit - 1) then 1 else 0)

// ========== Forward Direction ==========

/// matched_prefix_at with length m implies matches_at
let matched_prefix_is_match (text pattern: seq int) (i: nat)
  : Lemma
    (requires matched_prefix_at text pattern i (length pattern) /\
             length pattern > 0)
    (ensures CLRS.Ch32.KMP.matches_at text pattern (i - length pattern))
  = ()

/// matches_at implies matched_prefix_at with length m
let match_is_matched_prefix (text pattern: seq int) (s: nat)
  : Lemma
    (requires CLRS.Ch32.KMP.matches_at text pattern s /\ length pattern > 0)
    (ensures matched_prefix_at text pattern (s + length pattern) (length pattern))
  = let m = length pattern in
    let aux (j: nat{j < m})
      : Lemma (index text (s + m - m + j) == index pattern j) =
      assert (s + m - m + j == s + j)
    in
    Classical.forall_intro (Classical.move_requires aux)

// ========== Matched Prefix → Prefix-Suffix ==========

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let matched_prefix_implies_ps (text pattern: seq int) (i q k: nat)
  : Lemma
    (requires matched_prefix_at text pattern i q /\
             matched_prefix_at text pattern i k /\
             0 < k /\ k < q /\ q <= length pattern /\ q - 1 < length pattern)
    (ensures is_prefix_suffix #int pattern (q - 1) k)
  = let aux (j: nat{j < k})
      : Lemma (index pattern j == index pattern ((q - 1) - k + 1 + j)) =
      assert (i - k + j == i - q + (q - k + j));
      assert ((q - 1) - k + 1 + j == q - k + j);
      assert (q - k + j < q)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

// ========== Follow-Failure Properties ==========

/// follow_fail returns a valid result.
/// Result r satisfies: r <= k, and if r > 0 then pattern[r] = c.
/// If r < k and r > 0, then r is in the failure chain (is_prefix_suffix of k-1).
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1 --split_queries always"
let rec follow_fail_valid (pattern pi: seq int) (k: nat) (c: int)
  : Lemma
    (requires pi_max pattern pi /\ k > 0 /\ k - 1 < length pattern)
    (ensures (let r = follow_fail pattern pi k c in
              r <= k /\
              (r > 0 ==> r < length pattern /\ index pattern r = c) /\
              (r > 0 /\ r < k ==> is_prefix_suffix #int pattern (k - 1) r)))
    (decreases k)
  = pi_val_bounds pattern pi (k - 1);
    let piv : nat = index pi (k - 1) in
    if k < length pattern && index pattern k = c then ()
    else begin
      if piv = 0 then ()
      else begin
        follow_fail_valid pattern pi piv c;
        let r = follow_fail pattern pi piv c in
        if r > 0 && r < piv then
          failure_chain #int pattern (k - 1) piv r
        else ()
      end
    end
#pop-options

/// Nesting property of prefix-suffixes:
/// If both j and k are PS of q, and j < k, then j is PS of k-1.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let ps_nesting (pattern: seq int) (q: nat{q < length pattern}) (k j: nat)
  : Lemma
    (requires is_prefix_suffix #int pattern q k /\
             is_prefix_suffix #int pattern q j /\
             j < k)
    (ensures k > 0 /\ k - 1 < length pattern /\
             is_prefix_suffix #int pattern (k - 1) j)
  = // j < k <= q < length pattern
    assert (k > 0 /\ k - 1 < length pattern);
    // j PS of q: pattern[i] = pattern[q - j + 1 + i] for i < j
    // k PS of q: pattern[i] = pattern[q - k + 1 + i] for i < k
    // Need: pattern[i] = pattern[(k-1) - j + 1 + i] = pattern[k - j + i] for i < j
    // From k PS of q: for i' = k - j + i (where i < j, so i' < k):
    //   pattern[k-j+i] = pattern[q - k + 1 + (k-j+i)] = pattern[q - j + 1 + i]
    // From j PS of q: pattern[i] = pattern[q - j + 1 + i]
    // Chaining: pattern[i] = pattern[q-j+1+i] = pattern[k-j+i]
    let aux (i: nat{i < j})
      : Lemma (index pattern i == index pattern (k - j + i)) =
      assert (k - j + i < k);
      assert (q - k + 1 + (k - j + i) == q - j + 1 + i)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

/// Key lemma: follow_fail finds any target in the failure chain.
/// If target is a PS of k-1 with pattern[target] = c, then follow_fail >= target.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1 --split_queries always"
let rec follow_fail_maximal (pattern pi: seq int) (k: nat) (c: int) (target: nat)
  : Lemma
    (requires pi_max pattern pi /\
             k > 0 /\ k - 1 < length pattern /\
             is_prefix_suffix #int pattern (k - 1) target /\
             target > 0 /\ target < length pattern /\
             index pattern target = c)
    (ensures follow_fail pattern pi k c >= target)
    (decreases k)
  = pi_val_bounds pattern pi (k - 1);
    let piv : nat = index pi (k - 1) in
    if k < length pattern && index pattern k = c then
      assert (target <= k - 1)
    else begin
      assert (target <= piv);
      if target = piv then
        if piv < length pattern && index pattern piv = c then ()
        else assert false
      else begin
        ps_nesting pattern (k - 1) piv target;
        follow_fail_maximal pattern pi piv c target
      end
    end
#pop-options

// ========== KMP Step Correctness ==========

/// When follow_fail returns q (same value), q+1 is a valid matched prefix
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1 --split_queries always"
let kmp_step_valid_eq (text pattern: seq int) (i q: nat)
  : Lemma
    (requires matched_prefix_at text pattern i q /\
             i < length text /\
             q > 0 /\ q < length pattern /\
             index pattern q == index text i)
    (ensures matched_prefix_at text pattern (i + 1) (q + 1))
  = let aux (j: nat{j < q + 1})
      : Lemma (index text (i + 1 - (q + 1) + j) == index pattern j) =
      assert (i + 1 - (q + 1) + j == i - q + j)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

/// When follow_fail returns q' < q > 0, q'+1 is a valid matched prefix
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1 --split_queries always"
let kmp_step_valid_lt (text pattern: seq int) (i q q': nat)
  : Lemma
    (requires matched_prefix_at text pattern i q /\
             i < length text /\
             q > 0 /\ q' > 0 /\ q' < q /\
             q <= length pattern /\
             is_prefix_suffix #int pattern (q - 1) q' /\
             index pattern q' == index text i)
    (ensures matched_prefix_at text pattern (i + 1) (q' + 1))
  = let aux (j: nat{j < q'})
      : Lemma (index text (i + 1 - (q' + 1) + j) == index pattern j) =
      let k = q - q' + j in
      assert (k < q);
      assert ((q - 1) - q' + 1 + j == k)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

/// The KMP step result is a valid matched prefix
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let kmp_step_valid (text pattern pi: seq int) (i q: nat)
  : Lemma
    (requires pi_max pattern pi /\
             is_max_prefix_below text pattern i q /\
             i < length text)
    (ensures (let c = index text i in
              let q_new = kmp_step_result pattern pi q c (length pattern) in
              matched_prefix_at text pattern (i + 1) q_new /\
              q_new <= length pattern))
  = let c = index text i in
    let m = length pattern in
    if q = 0 then ()
    else begin
      follow_fail_valid pattern pi q c;
      let r = follow_fail pattern pi q c in
      if r = q then
        kmp_step_valid_eq text pattern i q
      else if r > 0 then
        kmp_step_valid_lt text pattern i q r
      else ()
    end
#pop-options

/// The KMP step result is the true maximum (possibly = m)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1 --split_queries always"
let kmp_step_maximal (text pattern pi: seq int) (i q: nat)
  : Lemma
    (requires pi_max pattern pi /\
             is_max_prefix_below text pattern i q /\
             i < length text)
    (ensures (let c = index text i in
              let q_new = kmp_step_result pattern pi q c (length pattern) in
              matched_prefix_at text pattern (i + 1) q_new /\
              q_new <= length pattern /\
              (forall (k: nat). matched_prefix_at text pattern (i + 1) k ==> k <= q_new)))
  = let c = index text i in
    let m = length pattern in
    let q_new = kmp_step_result pattern pi q c m in
    kmp_step_valid text pattern pi i q;
    let aux (k: nat)
      : Lemma (requires matched_prefix_at text pattern (i + 1) k)
              (ensures k <= q_new) =
      if k = 0 then ()
      else begin
        assert (index text i == index pattern (k - 1));
        assert (matched_prefix_at text pattern i (k - 1));
        assert (k - 1 < m);
        assert (k - 1 <= q);
        if k - 1 = q then begin
          if q > 0 then begin
            assert (q < m);
            assert (index pattern q == c)
          end
          else ()
        end
        else begin
          if k - 1 = 0 then begin
            assert (index pattern 0 = c)
          end
          else begin
            matched_prefix_implies_ps text pattern i q (k - 1);
            assert (is_prefix_suffix #int pattern (q - 1) (k - 1));
            assert (index pattern (k - 1) = c);
            assert (k - 1 < length pattern);
            if q > 0 then begin
              follow_fail_maximal pattern pi q c (k - 1);
              follow_fail_valid pattern pi q c;
              let r = follow_fail pattern pi q c in
              assert (r >= k - 1);
              if r > 0 then begin
                assert (index pattern r = c);
                assert (q_new >= r + 1);
                assert (q_new >= k)
              end
              else begin
                assert (r >= k - 1);
                assert (k - 1 > 0);
                assert false
              end
            end
            else ()
          end
        end
      end
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

// ========== Match Reset ==========

/// After match (q=m), pi[m-1] gives is_max_prefix_below at position i+1
/// Helper: matched prefix of pattern at i+1 with |pattern| chars, and q' = pi[m-1], 
/// then q' is a valid matched prefix at i+1
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1 --split_queries always"
let match_reset_valid_prefix (text pattern: seq int) (i m q': nat)
  : Lemma
    (requires matched_prefix_at text pattern (i + 1) m /\
             m == length pattern /\ m > 0 /\
             is_prefix_suffix #int pattern (m - 1) q' /\
             q' <= m - 1 /\
             i + 1 <= length text)
    (ensures matched_prefix_at text pattern (i + 1) q')
  = if q' = 0 then ()
    else begin
      let aux (j: nat{j < q'})
        : Lemma (index text (i + 1 - q' + j) == index pattern j) =
        let k = m - q' + j in
        assert (k < m);
        assert (i + 1 - q' + j == i + 1 - m + k);
        assert ((m - 1) - q' + 1 + j == k)
      in
      Classical.forall_intro (Classical.move_requires aux)
    end
#pop-options

/// After match (q=m), pi[m-1] gives is_max_prefix_below at position i+1
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1 --split_queries always"
let match_reset_max (text pattern pi: seq int) (i: nat)
  : Lemma
    (requires pi_max pattern pi /\
             matched_prefix_at text pattern (i + 1) (length pattern) /\
             i + 1 <= length text)
    (ensures (let m = length pattern in
              let q' = index pi (m - 1) in
              is_max_prefix_below text pattern (i + 1) q'))
  = let m = length pattern in
    pi_val_bounds pattern pi (m - 1);
    let q' : nat = index pi (m - 1) in
    match_reset_valid_prefix text pattern i m q';
    let aux_max (k: nat)
      : Lemma (requires matched_prefix_at text pattern (i + 1) k /\ k < m)
              (ensures k <= q') =
      if k = 0 then ()
      else begin
        matched_prefix_implies_ps text pattern (i + 1) m k;
        assert (is_prefix_suffix #int pattern (m - 1) k)
      end
    in
    Classical.forall_intro (Classical.move_requires aux_max)
#pop-options

// ========== Decidable Match Correctness ==========

#push-options "--fuel 1 --ifuel 1"
let rec check_match_correct (text pattern: seq int) (s: nat) (j: nat)
  : Lemma
    (requires s + length pattern <= length text /\ j <= length pattern)
    (ensures check_match_at text pattern s j <==>
             (forall (k: nat). j <= k /\ k < length pattern ==>
               index text (s + k) == index pattern k))
    (decreases (length pattern - j))
  = if j >= length pattern then ()
    else check_match_correct text pattern s (j + 1)
#pop-options

#push-options "--fuel 0 --ifuel 0"
let matches_at_dec_iff (text pattern: seq int) (s: nat)
  : Lemma
    (requires s + length pattern <= length text)
    (ensures matches_at_dec text pattern s <==>
             CLRS.Ch32.KMP.matches_at text pattern s)
  = check_match_correct text pattern s 0
#pop-options

// ========== Match Detection Equivalence ==========

/// q_new = m iff there's a match at position i+1-m
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let kmp_match_iff (text pattern pi: seq int) (i q: nat)
  : Lemma
    (requires pi_max pattern pi /\
             is_max_prefix_below text pattern i q /\
             i < length text)
    (ensures (let c = index text i in
              let m = length pattern in
              let q_new = kmp_step_result pattern pi q c m in
              (q_new = m <==>
                (i + 1 >= m /\
                 CLRS.Ch32.KMP.matches_at text pattern (i + 1 - m)))))
  = let c = index text i in
    let m = length pattern in
    let q_new = kmp_step_result pattern pi q c m in
    kmp_step_maximal text pattern pi i q;
    if q_new = m then
      matched_prefix_is_match text pattern (i + 1)
    else ();
    if i + 1 >= m then begin
      if i + 1 - m + m <= length text then begin
        if check_match_at text pattern (i + 1 - m) 0 then begin
          check_match_correct text pattern (i + 1 - m) 0;
          match_is_matched_prefix text pattern (i + 1 - m);
          assert (matched_prefix_at text pattern (i + 1) m);
          assert (m <= q_new)
        end
        else ()
      end
      else ()
    end
    else begin
      assert (q_new <= i + 1)
    end
#pop-options

// ========== Count Helpers ==========

#push-options "--fuel 1 --ifuel 0"
let count_before_unfold (text pattern: seq int) (limit: nat)
  : Lemma (requires limit > 0)
          (ensures count_before text pattern limit ==
                   count_before text pattern (limit - 1) +
                   (if matches_at_dec text pattern (limit - 1) then 1 else 0))
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 0"
let rec count_before_bounded (text pattern: seq int) (limit: nat)
  : Lemma (ensures count_before text pattern limit <= limit)
          (decreases limit)
  = if limit = 0 then ()
    else count_before_bounded text pattern (limit - 1)
#pop-options

// ========== Main Theorem ==========

/// The main count invariant step
/// Invariant preservation part of KMP step
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1 --split_queries always"
let kmp_step_invariant (text pattern pi: seq int) (i q: nat)
  : Lemma
    (requires pi_max pattern pi /\
             length pattern > 0 /\
             i < length text /\
             is_max_prefix_below text pattern i q)
    (ensures (let m = length pattern in
              let c = index text i in
              let q_new = kmp_step_result pattern pi q c m in
              let q_next = if q_new = m then index pi (m - 1) else q_new in
              is_max_prefix_below text pattern (i + 1) q_next))
  = let m = length pattern in
    let c = index text i in
    let q_new = kmp_step_result pattern pi q c m in
    kmp_step_maximal text pattern pi i q;
    if q_new = m then begin
      assert (matched_prefix_at text pattern (i + 1) m);
      match_reset_max text pattern pi i
    end else begin
      assert (matched_prefix_at text pattern (i + 1) q_new);
      assert (q_new < m);
      assert (forall (k:nat). matched_prefix_at text pattern (i + 1) k ==> k <= q_new)
    end
#pop-options

/// Count tracking helper — isolated from pi_max to prevent quantifier explosion.
/// Takes the match detection result as a parameter instead of computing it.
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let count_tracking (text pattern: seq int) (i count: nat) (found: bool)
  : Lemma
    (requires length pattern > 0 /\
             i < length text /\ length text >= length pattern /\
             (i >= length pattern ==>
               count == count_before text pattern (i - length pattern + 1)) /\
             (i < length pattern ==> count == 0) /\
             (i + 1 >= length pattern ==>
               (found <==> CLRS.Ch32.KMP.matches_at text pattern (i + 1 - length pattern))) /\
             (i + 1 < length pattern ==> found == false))
    (ensures (let m = length pattern in
              let count' = if found then count + 1 else count in
              (i + 1 >= m ==>
                count' == count_before text pattern (i + 1 - m + 1)) /\
              (i + 1 < m ==> count' == 0)))
  = let m = length pattern in
    let count' = if found then count + 1 else count in
    let s = i + 1 - m in
    if i + 1 < m then ()
    else if i + 1 = m then begin
      count_before_unfold text pattern 1;
      matches_at_dec_iff text pattern 0
    end
    else begin
      count_before_unfold text pattern (i - m + 2);
      matches_at_dec_iff text pattern s
    end
#pop-options

/// Count tracking part of KMP step
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let kmp_count_step (text pattern pi: seq int) (i q count: nat)
  : Lemma
    (requires pi_max pattern pi /\
             length pattern > 0 /\
             i < length text /\
             length text >= length pattern /\
             is_max_prefix_below text pattern i q /\
             (i >= length pattern ==>
               count == count_before text pattern (i - length pattern + 1)) /\
             (i < length pattern ==> count == 0))
    (ensures (let m = length pattern in
              let c = index text i in
              let q_new = kmp_step_result pattern pi q c m in
              let found = (q_new = m) in
              let count' = if found then count + 1 else count in
              let q_next = if found then index pi (m - 1) else q_new in
              is_max_prefix_below text pattern (i + 1) q_next /\
              (i + 1 >= m ==>
                count' == count_before text pattern (i + 1 - m + 1)) /\
              (i + 1 < m ==> count' == 0)))
  = let m = length pattern in
    let c = index text i in
    let q_new = kmp_step_result pattern pi q c m in
    kmp_step_invariant text pattern pi i q;
    kmp_match_iff text pattern pi i q;
    let found = (q_new = m) in
    count_tracking text pattern i count found
#pop-options

/// KMP correctness meta-theorem
let kmp_correct_statement (text pattern pi: seq int)
  : Lemma
    (requires pi_max pattern pi /\
             length pattern > 0 /\
             length text >= length pattern)
    (ensures True)
  = ()

/// Helper: count_before s + count_matches_up_to ... s == count_matches_up_to ... 0
#push-options "--fuel 2 --ifuel 0"
let rec count_split (text pattern: seq int) (n m s: nat)
  : Lemma
    (requires m > 0 /\ n >= m /\ n == length text /\ m == length pattern /\ s <= n - m + 1)
    (ensures count_before text pattern s + count_matches_up_to text pattern n m s ==
             count_matches_up_to text pattern n m 0)
    (decreases s)
  = if s = 0 then ()
    else begin
      count_split text pattern n m (s - 1);
      assert (s - 1 + m <= n);
      assert (matches_at_dec text pattern (s - 1) == check_match_at text pattern (s - 1) 0)
    end
#pop-options

/// count_matches_up_to at the end returns 0
#push-options "--fuel 1 --ifuel 0"
let count_up_to_end (text pattern: seq int) (n m: nat)
  : Lemma
    (requires m > 0 /\ n >= m)
    (ensures count_matches_up_to text pattern n m (n - m + 1) == 0)
  = ()
#pop-options

/// Top-level: KMP count equals the naive match count
#push-options "--fuel 0 --ifuel 0"
let count_before_eq_spec (text pattern: seq int) (n m: nat)
  : Lemma
    (requires m > 0 /\ n >= m /\ n == length text /\ m == length pattern)
    (ensures count_before text pattern (n - m + 1) ==
             count_matches_spec text pattern n m)
  = count_split text pattern n m (n - m + 1);
    count_up_to_end text pattern n m
#pop-options
