(*
   Rabin-Karp String Matching Algorithm - Verified implementation in Pulse
   
   Implements the Rabin-Karp string matching algorithm from CLRS Chapter 32:
   Given text of length n and pattern of length m, finds all occurrences
   of pattern in text using a rolling hash with O(n) expected time.
   
   Hash function: Simple sum of characters for verification tractability.
   On hash match, verify character-by-character.
   
   NO admits. NO assumes.
*)

module CLRS.Ch32.RabinKarp
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

// Does pattern match text starting at position s?
let matches_at (text: Seq.seq FStar.Char.char) (pattern: Seq.seq FStar.Char.char) (s: nat) : prop =
  s + Seq.length pattern <= Seq.length text /\
  (forall (j: nat). j < Seq.length pattern ==> 
    Seq.index text (s + j) == Seq.index pattern j)

// Decidable check for matching
let rec check_match_at (text: Seq.seq FStar.Char.char) (pattern: Seq.seq FStar.Char.char) (s: nat) (j: nat{j <= Seq.length pattern})
  : Tot bool (decreases (Seq.length pattern - j))
  = if j >= Seq.length pattern then true
    else if s + j >= Seq.length text then false
    else if Seq.index text (s + j) = Seq.index pattern j
         then check_match_at text pattern s (j + 1)
         else false

let matches_at_dec (text: Seq.seq FStar.Char.char) (pattern: Seq.seq FStar.Char.char) (s: nat) : bool =
  s + Seq.length pattern <= Seq.length text && check_match_at text pattern s 0

let rec check_match_at_correct (text: Seq.seq FStar.Char.char) (pattern: Seq.seq FStar.Char.char) (s: nat) (j: nat{j <= Seq.length pattern})
  : Lemma (requires s + Seq.length pattern <= Seq.length text)
          (ensures check_match_at text pattern s j <==>
                   (forall (k: nat). j <= k /\ k < Seq.length pattern ==>
                     Seq.index text (s + k) == Seq.index pattern k))
          (decreases (Seq.length pattern - j))
  = if j >= Seq.length pattern then ()
    else check_match_at_correct text pattern s (j + 1)

let matches_at_dec_correct (text: Seq.seq FStar.Char.char) (pattern: Seq.seq FStar.Char.char) (s: nat)
  : Lemma (requires s + Seq.length pattern <= Seq.length text)
          (ensures matches_at_dec text pattern s <==> matches_at text pattern s)
  = check_match_at_correct text pattern s 0

// Count of matches from position 0 to limit-1
let rec count_matches_up_to (text: Seq.seq FStar.Char.char) (pattern: Seq.seq FStar.Char.char) (limit: nat)
  : Tot nat (decreases limit)
  = if limit = 0 then 0
    else count_matches_up_to text pattern (limit - 1) +
         (if matches_at_dec text pattern (limit - 1) then 1 else 0)

let count_matches_up_to_unfold (text: Seq.seq FStar.Char.char) (pattern: Seq.seq FStar.Char.char) (limit: nat)
  : Lemma (requires limit > 0)
          (ensures count_matches_up_to text pattern limit ==
                   count_matches_up_to text pattern (limit - 1) +
                   (if matches_at_dec text pattern (limit - 1) then 1 else 0))
  = ()

let rec count_matches_up_to_bounded (text: Seq.seq FStar.Char.char) (pattern: Seq.seq FStar.Char.char) (limit: nat)
  : Lemma (ensures count_matches_up_to text pattern limit <= limit)
          (decreases limit)
  = if limit = 0 then ()
    else count_matches_up_to_bounded text pattern (limit - 1)

// Simple hash: sum of characters (cast to int)
let rec compute_hash_spec (s: Seq.seq FStar.Char.char) (start: nat) (len: nat)
  : Tot int (decreases len)
  = if len = 0 || start >= Seq.length s then 0
    else if start + len > Seq.length s then 0
    else FStar.Char.int_of_char (Seq.index s start) + 
         compute_hash_spec s (start + 1) (len - 1)

// Lemma: compute_hash_spec extends by one character
let rec compute_hash_spec_extend (s: Seq.seq FStar.Char.char) (start: nat) (len: nat)
  : Lemma (requires start + len < Seq.length s)
          (ensures compute_hash_spec s start (len + 1) ==
                   compute_hash_spec s start len + FStar.Char.int_of_char (Seq.index s (start + len)))
          (decreases len)
  = if len = 0 then ()
    else compute_hash_spec_extend s (start + 1) (len - 1)

// Lemma: hash of matching substrings are equal (general version)
let rec hash_of_matching_substrings_gen (text pattern: Seq.seq FStar.Char.char) (s p: nat) (len: nat)
  : Lemma (requires s + len <= Seq.length text /\ p + len <= Seq.length pattern /\
                     (forall (j:nat). j < len ==> Seq.index text (s + j) == Seq.index pattern (p + j)))
          (ensures compute_hash_spec text s len == compute_hash_spec pattern p len)
          (decreases len)
  = if len = 0 then ()
    else (
      assert (Seq.index text s == Seq.index pattern p);
      // Need: forall j < len-1. text[(s+1)+j] == pattern[(p+1)+j]
      // From precondition: forall j < len. text[s+j] == pattern[p+j]
      // Taking j' = j+1 where j' < len: text[s+j'] == pattern[p+j']
      // Since s+j' = (s+1)+(j'-1) and j'-1 < len-1, this is what we need
      assert (forall (j:nat). j < len - 1 ==> (j + 1 < len /\ s + (j + 1) == (s + 1) + j /\ p + (j + 1) == (p + 1) + j));
      assert (forall (j:nat). j < len - 1 ==> Seq.index text ((s + 1) + j) == Seq.index pattern ((p + 1) + j));
      hash_of_matching_substrings_gen text pattern (s + 1) (p + 1) (len - 1)
    )

let hash_of_matching_substrings (text pattern: Seq.seq FStar.Char.char) (s: nat) (len: nat)
  : Lemma (requires s + len <= Seq.length text /\ len <= Seq.length pattern /\
                     (forall (j:nat). j < len ==> Seq.index text (s + j) == Seq.index pattern j))
          (ensures compute_hash_spec text s len == compute_hash_spec pattern 0 len)
  = assert (forall (j:nat). j < len ==> Seq.index text (s + j) == Seq.index pattern (0 + j));
    hash_of_matching_substrings_gen text pattern s 0 len

// Lemma: rolling hash update
// compute_hash_spec s (start+1) len = compute_hash_spec s start len 
//   - int_of_char(s[start]) + int_of_char(s[start+len])
let rec compute_hash_spec_roll (s: Seq.seq FStar.Char.char) (start: nat) (len: nat)
  : Lemma (requires start + len < Seq.length s /\ len > 0)
          (ensures compute_hash_spec s (start + 1) len ==
                   compute_hash_spec s start len
                   - FStar.Char.int_of_char (Seq.index s start)
                   + FStar.Char.int_of_char (Seq.index s (start + len)))
          (decreases len)
  = if len = 1 then ()
    else compute_hash_spec_roll s (start + 1) (len - 1)

// Key lemma: matches_at_dec implies hash equality
let matches_at_dec_implies_hash_eq 
    (text pattern: Seq.seq FStar.Char.char) (s m: nat)
  : Lemma (requires s + m <= Seq.length text /\ m == Seq.length pattern /\ m > 0 /\
                     matches_at_dec text pattern s)
          (ensures compute_hash_spec text s m == compute_hash_spec pattern 0 m)
  = matches_at_dec_correct text pattern s;
    hash_of_matching_substrings text pattern s m

// Key combined lemma: should_count equivalence
// Given: inner loop runs and produces final_verified, final_j
// Proves: should_count matches matches_at_dec
let should_count_correct 
    (text pattern: Seq.seq FStar.Char.char) (s m: nat)
    (hash_match: bool) (final_verified: int) (final_j: nat)
    (t_hash p_hash: int)
  : Lemma (requires 
      s + m <= Seq.length text /\ m == Seq.length pattern /\ m > 0 /\
      final_j <= m /\
      (final_verified == 1 \/ final_verified == 0) /\
      // Loop exit condition
      (final_j >= m \/ final_verified <> 1) /\
      // Invariant for verified == 1
      (final_verified == 1 ==> (forall (k:nat). k < final_j ==> Seq.index text (s + k) == Seq.index pattern k)) /\
      // Invariant for verified == 0
      (final_verified == 0 ==> (exists (k:nat). k < final_j /\ Seq.index text (s + k) <> Seq.index pattern k) \/ not hash_match) /\
      // Invariant for hash_match ==> verified == 1 (when all match)
      (hash_match /\ (forall (k:nat). k < final_j ==> Seq.index text (s + k) == Seq.index pattern k) ==> final_verified == 1) /\
      // Hash facts
      t_hash == compute_hash_spec text s m /\
      p_hash == compute_hash_spec pattern 0 m /\
      hash_match == (t_hash = p_hash)
    )
    (ensures (if final_verified = 1 && final_j = m then 1 else 0) ==
             (if matches_at_dec text pattern s then 1 else 0))
  = matches_at_dec_correct text pattern s;
    if matches_at_dec text pattern s then (
      // matches_at is true => forall j < m. text[s+j] == pat[j]
      hash_of_matching_substrings text pattern s m;
      // => compute_hash_spec text s m == compute_hash_spec pattern 0 m
      // => t_hash == p_hash => hash_match = true
      // => from invariant: hash_match /\ forall k < final_j. match ==> final_verified == 1
      // Since all chars match: forall k < final_j. match (since final_j <= m)
      // => final_verified == 1 => final_j >= m => final_j == m
      assert (hash_match == true);
      assert (final_verified == 1);
      assert (final_j >= m);
      ()
    ) else (
      // matches_at is false => exists j < m. text[s+j] != pat[j]
      // If final_verified == 1 && final_j == m: forall k < m. match => matches_at => contradiction
      if final_verified = 1 && final_j = m then (
        assert (forall (k:nat). k < m ==> Seq.index text (s + k) == Seq.index pattern k)
      ) else ()
    )

// ========== Helper: Compute Hash ==========

fn compute_hash
  (#p: perm)
  (arr: array FStar.Char.char)
  (#s: Ghost.erased (Seq.seq FStar.Char.char))
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
    pure (h == compute_hash_spec s (SZ.v start) (SZ.v len))
{
  let mut hash: int = 0;
  let mut i: SZ.t = 0sz;
  
  while (!i <^ len)
  invariant exists* vi vhash.
    R.pts_to i vi **
    R.pts_to hash vhash **
    A.pts_to arr #p s **
    pure (
      SZ.v vi <= SZ.v len /\
      vhash == compute_hash_spec s (SZ.v start) (SZ.v vi)
    )
  {
    let vi = !i;
    let vhash = !hash;
    
    // Read arr[start + vi]
    let c = A.op_Array_Access arr (start +^ vi);
    let c_int = FStar.Char.int_of_char c;
    
    // Update hash
    compute_hash_spec_extend s (SZ.v start) (SZ.v vi);
    hash := vhash + c_int;
    i := vi +^ 1sz;
  };
  
  !hash
}

// ========== Main Algorithm ==========

fn rabin_karp
  (#p_text: perm)
  (#p_pat: perm)
  (text: array FStar.Char.char)
  (pattern: array FStar.Char.char)
  (#s_text: Ghost.erased (Seq.seq FStar.Char.char))
  (#s_pat: Ghost.erased (Seq.seq FStar.Char.char))
  (n: SZ.t)
  (m: SZ.t)
  requires 
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
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
  ensures
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    pure (result >= 0 /\ result <= SZ.v n - SZ.v m + 1 /\
          result == count_matches_up_to s_text s_pat (SZ.v n - SZ.v m + 1))
{
  // Compute pattern hash
  let p_hash = compute_hash pattern #s_pat 0sz m;
  
  // Compute initial text hash (first m characters)
  let mut t_hash: int = compute_hash text #s_text 0sz m;
  
  let mut count: int = 0;
  let mut s: SZ.t = 0sz;  // current position in text
  
  let max_s = n -^ m;
  
  // Main loop: try each starting position
  while (!s <=^ max_s)
  invariant exists* vs vcount vt_hash.
    R.pts_to s vs **
    R.pts_to count vcount **
    R.pts_to t_hash vt_hash **
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    pure (
      SZ.v vs <= SZ.v n - SZ.v m + 1 /\
      vcount >= 0 /\
      vcount <= SZ.v vs /\
      vcount == count_matches_up_to s_text s_pat (SZ.v vs) /\
      (SZ.v vs <= SZ.v max_s ==> vt_hash == compute_hash_spec s_text (SZ.v vs) (SZ.v m)) /\
      p_hash == compute_hash_spec s_pat 0 (SZ.v m)
    )
  {
    let vs = !s;
    let vcount_outer = !count;
    let vt_hash_outer = !t_hash;
    
    // Check if hashes match
    let hash_match = (vt_hash_outer = p_hash);
    
    // If hash matches, verify character by character
    // Use a flag approach to avoid conditionals around array access
    let mut verified: int = 
      (if hash_match then 1 else 0);
    
    // Inner verification loop (only runs if hash_match)
    let mut j: SZ.t = 0sz;
    
    while (!j <^ m && !verified = 1)
    invariant exists* vj vverified vcount vt_hash.
      R.pts_to s vs **
      R.pts_to count vcount **
      R.pts_to t_hash vt_hash **
      R.pts_to j vj **
      R.pts_to verified vverified **
      A.pts_to text #p_text s_text **
      A.pts_to pattern #p_pat s_pat **
      pure (
        SZ.v vj <= SZ.v m /\
        vcount == vcount_outer /\
        vt_hash == vt_hash_outer /\
        (vverified == 1 \/ vverified == 0) /\
        (vverified == 1 ==> (forall (k: nat). k < SZ.v vj ==> 
          Seq.index s_text (SZ.v vs + k) == Seq.index s_pat k)) /\
        (vverified == 0 ==> (exists (k: nat). k < SZ.v vj /\
          Seq.index s_text (SZ.v vs + k) <> Seq.index s_pat k) \/ 
          (not hash_match)) /\
        (hash_match /\ (forall (k: nat). k < SZ.v vj ==>
          Seq.index s_text (SZ.v vs + k) == Seq.index s_pat k) ==> vverified == 1)
      )
    {
      let vj = !j;
      
      // Read text[vs + vj] and pattern[vj]
      let text_char = A.op_Array_Access text (vs +^ vj);
      let pat_char = A.op_Array_Access pattern vj;
      
      // Update verified flag (unconditional write)
      let current_verified = !verified;
      let chars_match = (text_char = pat_char);
      let new_verified = 
        (if chars_match then current_verified else 0);
      
      verified := new_verified;
      j := vj +^ 1sz;
    };
    
    // If verified == 1 after checking all m characters, increment count
    let final_verified = !verified;
    let final_j = !j;
    
    // Connect the verification result to matches_at_dec using combined lemma
    should_count_correct s_text s_pat (SZ.v vs) (SZ.v m)
      hash_match final_verified (SZ.v final_j) vt_hash_outer p_hash;
    
    // Unconditional update to count
    let should_count = 
      (if (final_verified = 1 && final_j = m) then 1 else 0);
    
    count := vcount_outer + should_count;
    
    // Prove count == count_matches_up_to s_text s_pat (vs + 1)
    count_matches_up_to_unfold s_text s_pat (SZ.v vs + 1);
    count_matches_up_to_bounded s_text s_pat (SZ.v vs + 1);
    
    // Update rolling hash for next position
    let is_last = (vs = max_s);
    
    // Read old character to remove from hash
    let old_char = A.op_Array_Access text vs;
    let old_char_int = FStar.Char.int_of_char old_char;
    
    // Always read the "next" character
    let next_idx = (if is_last then vs else (vs +^ m));
    let new_char = A.op_Array_Access text next_idx;
    let new_char_int = FStar.Char.int_of_char new_char;
    
    // Compute updated hash
    let updated_hash = vt_hash_outer - old_char_int + new_char_int;
    
    // Write new hash and update position
    if is_last {
      t_hash := vt_hash_outer;
      s := vs +^ 1sz
    } else {
      // Prove rolling hash correctness
      compute_hash_spec_roll s_text (SZ.v vs) (SZ.v m);
      t_hash := updated_hash;
      s := vs +^ 1sz
    }
  };
  
  let final_count = !count;
  final_count
}

#pop-options
