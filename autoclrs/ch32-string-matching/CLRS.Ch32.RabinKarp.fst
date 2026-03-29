(*
   Rabin-Karp String Matching Algorithm - Verified implementation in Pulse

   Implements the Rabin-Karp string matching algorithm from CLRS Chapter 32:
   Given text of length n and pattern of length m, finds all occurrences
   of pattern in text using a polynomial rolling hash.

   Hash function: CLRS polynomial hash (Horner's rule) from RabinKarp.Spec.
   On hash match, verify character-by-character.

   NO admits. NO assumes.
*)

module CLRS.Ch32.RabinKarp
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

#push-options "--z3rlimit 50 --ifuel 2 --fuel 2"

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module RKSpec = CLRS.Ch32.RabinKarp.Spec

open CLRS.Common.Complexity
open CLRS.Ch32.RabinKarp.Complexity

// ========== Pure Specification ==========

// Count of matches from position 0 to limit-1
let rec count_matches_up_to (text pattern: Seq.seq nat) (limit: nat)
  : Tot nat (decreases limit)
  = if limit = 0 then 0
    else count_matches_up_to text pattern (limit - 1) +
         (if RKSpec.matches_at_dec text pattern (limit - 1) then 1 else 0)

let count_matches_up_to_unfold (text pattern: Seq.seq nat) (limit: nat)
  : Lemma (requires limit > 0)
          (ensures count_matches_up_to text pattern limit ==
                   count_matches_up_to text pattern (limit - 1) +
                   (if RKSpec.matches_at_dec text pattern (limit - 1) then 1 else 0))
  = ()

let rec count_matches_up_to_bounded (text pattern: Seq.seq nat) (limit: nat)
  : Lemma (ensures count_matches_up_to text pattern limit <= limit)
          (decreases limit)
  = if limit = 0 then ()
    else count_matches_up_to_bounded text pattern (limit - 1)

// Key combined lemma: should_count equivalence
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1 --split_queries always"
let should_count_correct
    (text pattern: Seq.seq nat) (d: nat) (q: pos) (s m: nat)
    (hash_match: bool) (final_verified: int) (final_j: nat)
    (t_hash p_hash: int)
  : Lemma (requires
      s + m <= Seq.length text /\ m == Seq.length pattern /\ m > 0 /\
      final_j <= m /\
      (final_verified == 1 \/ final_verified == 0) /\
      (final_j >= m \/ final_verified <> 1) /\
      (final_verified == 1 ==> (forall (k:nat). k < final_j ==> Seq.index text (s + k) == Seq.index pattern k)) /\
      (final_verified == 0 ==> (exists (k:nat). k < final_j /\ Seq.index text (s + k) <> Seq.index pattern k) \/ not hash_match) /\
      (hash_match /\ (forall (k:nat). k < final_j ==> Seq.index text (s + k) == Seq.index pattern k) ==> final_verified == 1) /\
      t_hash == RKSpec.hash text d q s (s + m) /\
      p_hash == RKSpec.hash pattern d q 0 m /\
      hash_match == (t_hash = p_hash)
    )
    (ensures (if final_verified = 1 && final_j = m then 1 else 0) ==
             (if RKSpec.matches_at_dec text pattern s then 1 else 0))
  = RKSpec.matches_at_dec_correct text pattern s;
    if RKSpec.matches_at_dec text pattern s then (
      RKSpec.hash_match_lemma text pattern d q s;
      assert (hash_match == true);
      assert (final_verified == 1);
      assert (final_j >= m);
      ()
    ) else (
      if final_verified = 1 && final_j = m then (
        assert (forall (k:nat). k < m ==> Seq.index text (s + k) == Seq.index pattern k)
      ) else ()
    )
#pop-options

// ========== Helper: Compute Hash (Horner's rule, left-to-right) ==========

fn compute_hash
  (#p: perm)
  (arr: array nat)
  (#s: Ghost.erased (Seq.seq nat))
  (d: nat)
  (q: pos)
  (start: SZ.t)
  (len: SZ.t)
  requires
    A.pts_to arr #p s **
    pure (
      SZ.v start + SZ.v len <= Seq.length s /\
      Seq.length s <= A.length arr /\
      SZ.fits (SZ.v start + SZ.v len)
    )
  returns h: int
  ensures
    A.pts_to arr #p s **
    pure (SZ.v start + SZ.v len <= Seq.length s /\
          h >= 0 /\
          h == RKSpec.hash s d q (SZ.v start) (SZ.v start + SZ.v len))
{
  let mut acc: int = 0;
  let mut i: SZ.t = 0sz;

  while (!i <^ len)
  invariant exists* vi vacc.
    R.pts_to i vi **
    R.pts_to acc vacc **
    A.pts_to arr #p s **
    pure (
      SZ.v vi <= SZ.v len /\
      vacc >= 0 /\
      vacc == RKSpec.hash s d q (SZ.v start) (SZ.v start + SZ.v vi)
    )
  decreases (SZ.v len - SZ.v !i)
  {
    let vi = !i;
    let vacc = !acc;

    let c = A.op_Array_Access arr (start +^ vi);
    // hash(start, start+vi+1) = (d * hash(start, start+vi) + x[start+vi]) % q
    let new_acc = (d * vacc + c) % q;
    acc := new_acc;
    i := vi +^ 1sz;
  };

  !acc
}

// ========== Helper: Compute pow_mod ==========

fn compute_pow_mod
  (d: nat)
  (exp: SZ.t)
  (q: pos)
  requires pure (true)
  returns r: int
  ensures pure (r >= 0 /\ r == RKSpec.pow_mod d (SZ.v exp) q)
{
  let mut acc: int = 1 % q;
  let mut i: SZ.t = 0sz;

  while (!i <^ exp)
  invariant exists* vi vacc.
    R.pts_to i vi **
    R.pts_to acc vacc **
    pure (
      SZ.v vi <= SZ.v exp /\
      vacc >= 0 /\
      vacc == RKSpec.pow_mod d (SZ.v vi) q
    )
  decreases (SZ.v exp - SZ.v !i)
  {
    let vi = !i;
    let vacc = !acc;
    // pow_mod(d, k+1, q) = (d * pow_mod(d, k, q)) % q
    let new_acc = (d * vacc) % q;
    acc := new_acc;
    i := vi +^ 1sz;
  };

  !acc
}

// ========== Main Algorithm ==========

//SNIPPET_START: rabin_karp_sig
fn rabin_karp
  (#p_text: perm)
  (#p_pat: perm)
  (text: array nat)
  (pattern: array nat)
  (#s_text: Ghost.erased (Seq.seq nat))
  (#s_pat: Ghost.erased (Seq.seq nat))
  (n: SZ.t)
  (m: SZ.t)
  (d: nat)
  (q: pos)
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
      SZ.v m <= SZ.v n /\
      SZ.fits (SZ.v n - SZ.v m + 2) /\
      SZ.fits (SZ.v n + 1)
    )
  returns result: int
  ensures exists* (cf: nat).
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    GR.pts_to ctr cf **
    pure (result >= 0 /\ result <= SZ.v n - SZ.v m + 1 /\
          result == count_matches_up_to s_text s_pat (SZ.v n - SZ.v m + 1) /\
          rk_complexity_bounded cf (reveal c0) (SZ.v n) (SZ.v m))
//SNIPPET_END: rabin_karp_sig
{
  // Compute pattern hash and pow_mod for rolling hash
  let p_hash = compute_hash pattern #s_pat d q 0sz m;
  let t_hash_init = compute_hash text #s_text d q 0sz m;
  let h = compute_pow_mod d (if m = 1sz then 0sz else (m -^ 1sz)) q;

  // Account for m operations in pattern hash preprocessing
  ticks ctr (SZ.v m);

  let mut t_hash: int = t_hash_init;
  let mut count: int = 0;
  let mut s: SZ.t = 0sz;

  let max_s = n -^ m;

  // Main loop: try each starting position
  while (!s <=^ max_s)
  invariant exists* vs vcount vt_hash (vc: nat).
    R.pts_to s vs **
    R.pts_to count vcount **
    R.pts_to t_hash vt_hash **
    GR.pts_to ctr vc **
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    pure (
      SZ.v vs <= SZ.v n - SZ.v m + 1 /\
      vcount >= 0 /\
      vcount <= SZ.v vs /\
      vcount == count_matches_up_to s_text s_pat (SZ.v vs) /\
      vt_hash >= 0 /\
      (SZ.v vs <= SZ.v max_s ==> vt_hash == RKSpec.hash s_text d q (SZ.v vs) (SZ.v vs + SZ.v m)) /\
      p_hash == RKSpec.hash s_pat d q 0 (SZ.v m) /\
      h == RKSpec.pow_mod d (SZ.v m - 1) q /\
      vc >= reveal c0 /\
      vc - reveal c0 <= SZ.v m + SZ.v vs * SZ.v m
    )
  decreases (SZ.v n - SZ.v !s)
  {
    let vs = !s;
    let vcount_outer = !count;
    let vt_hash_outer = !t_hash;

    // Check if hashes match
    let hash_match = (vt_hash_outer = p_hash);

    // If hash matches, verify character by character
    let mut verified: int =
      (if hash_match then 1 else 0);

    // Inner verification loop
    let mut j: SZ.t = 0sz;

    while (!j <^ m && !verified = 1)
    invariant exists* vj vverified vcount' vt_hash' (vc_inner: nat).
      R.pts_to s vs **
      R.pts_to count vcount' **
      R.pts_to t_hash vt_hash' **
      R.pts_to j vj **
      R.pts_to verified vverified **
      GR.pts_to ctr vc_inner **
      A.pts_to text #p_text s_text **
      A.pts_to pattern #p_pat s_pat **
      pure (
        SZ.v vj <= SZ.v m /\
        vcount' == vcount_outer /\
        vt_hash' == vt_hash_outer /\
        (vverified == 1 \/ vverified == 0) /\
        (vverified == 1 ==> (forall (k: nat). k < SZ.v vj ==>
          Seq.index s_text (SZ.v vs + k) == Seq.index s_pat k)) /\
        (vverified == 0 ==> (exists (k: nat). k < SZ.v vj /\
          Seq.index s_text (SZ.v vs + k) <> Seq.index s_pat k) \/
          (not hash_match)) /\
        (hash_match /\ (forall (k: nat). k < SZ.v vj ==>
          Seq.index s_text (SZ.v vs + k) == Seq.index s_pat k) ==> vverified == 1) /\
        vc_inner >= reveal c0 /\
        vc_inner - reveal c0 <= SZ.v m + SZ.v vs * SZ.v m + SZ.v vj /\
        vc_inner - reveal c0 <= SZ.v m + SZ.v vs * SZ.v m + SZ.v m
      )
    decreases (SZ.v m - SZ.v !j)
    {
      let vj = !j;

      let text_char = A.op_Array_Access text (vs +^ vj);
      let pat_char = A.op_Array_Access pattern vj;

      // Count the comparison — one ghost tick
      tick ctr;

      let current_verified = !verified;
      let chars_match = (text_char = pat_char);
      let new_verified =
        (if chars_match then current_verified else 0);

      verified := new_verified;
      j := vj +^ 1sz;
    };

    // Count update
    let final_verified = !verified;
    let final_j = !j;

    should_count_correct s_text s_pat d q (SZ.v vs) (SZ.v m)
      hash_match final_verified (SZ.v final_j) vt_hash_outer p_hash;

    let should_count =
      (if (final_verified = 1 && final_j = m) then 1 else 0);

    count := vcount_outer + should_count;

    count_matches_up_to_unfold s_text s_pat (SZ.v vs + 1);
    count_matches_up_to_bounded s_text s_pat (SZ.v vs + 1);

    // Update rolling hash for next position
    let is_last = (vs = max_s);

    if is_last {
      t_hash := vt_hash_outer;
      s := vs +^ 1sz
    } else {
      // Rolling hash update: t_{s+1} = (d * ((t_s + q - (old*h)%q) % q) + new) % q
      let old_char = A.op_Array_Access text vs;
      let new_char = A.op_Array_Access text (vs +^ m);
      let new_hash = RKSpec.rolling_hash_step vt_hash_outer old_char new_char d q h;
      RKSpec.rolling_hash_step_correct s_text d q (SZ.v vs) (SZ.v m) vt_hash_outer h;
      t_hash := new_hash;
      s := vs +^ 1sz
    }
  };

  rk_worst_case_unfold (SZ.v n) (SZ.v m);

  !count
}

#pop-options
