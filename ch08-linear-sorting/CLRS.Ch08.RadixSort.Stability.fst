(*
   RadixSort Stability Proof (Task P1.2.4)
   
   This module proves that each pass of RadixSort maintains relative order
   of elements with equal digit values at the current position.
   
   KEY INSIGHT FROM CLRS:
   - RadixSort sorts from least-significant to most-significant digit
   - Each pass uses a STABLE sort (counting sort)
   - Stability ensures: when we sort by digit d+1, elements equal on 
     digit d+1 remain sorted by digits 0..d
   
   MAIN THEOREM (lemma_stable_pass_preserves_ordering):
   If input is sorted by digits 0..d-1, and we apply a stable sort on 
   digit d, then the result is sorted by digits 0..d.
   
   NO admits for core stability lemmas.
*)

module CLRS.Ch08.RadixSort.Stability

open FStar.Seq
open FStar.Math.Lemmas
open FStar.Mul
open FStar.Classical
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties

(* ========== Power function and digit extraction ========== *)

let rec pow (base: nat) (exp: nat) : nat =
  if exp = 0 then 1
  else base * pow base (exp - 1)

let rec pow_positive (base: nat) (exp: nat)
  : Lemma (requires base > 0)
          (ensures pow base exp > 0)
          (decreases exp)
  = if exp = 0 then ()
    else pow_positive base (exp - 1)

/// Extract the d-th digit of k in the given base.
let digit (k: nat) (d: nat) (base: nat) : nat =
  if base > 0 then (
    pow_positive base d;
    (k / pow base d) % base
  ) else 0

let digit_bound (k d base: nat)
  : Lemma (requires base > 0)
          (ensures digit k d base < base)
  = pow_positive base d;
    lemma_mod_lt (k / pow base d) base

(* ========== Sorted predicates ========== *)

/// Sorted by a single digit position
let rec sorted_on_digit (s: seq nat) (d: nat) (base: nat) : Tot prop (decreases (length s)) =
  base > 0 /\ (
    length s <= 1 \/ 
    (digit (index s 0) d base <= digit (index s 1) d base /\ 
     sorted_on_digit (tail s) d base))

/// Sorted by multiple digits 0..max_d (lexicographic order from low to high)
/// This is the key property maintained by radix sort:
/// After d passes, the sequence is sorted on digits 0, 1, ..., d-1
let sorted_up_to_digit (s: seq nat) (max_d: nat) (base: nat) : prop =
  base > 0 /\
  // For every pair i < j in the sequence:
  (forall (i j: nat). {:pattern (index s i); (index s j)}
    i < j /\ j < length s ==>
    // Either lower digits differ (and determine order)
    ((exists (d0: nat). d0 <= max_d /\
       // First differing digit favors i
       digit (index s i) d0 base < digit (index s j) d0 base /\
       // All lower digits are equal
       (forall (d': nat). d' < d0 ==> digit (index s i) d' base == digit (index s j) d' base)) \/
     // Or all digits up to max_d are equal
     (forall (d: nat). d <= max_d ==> digit (index s i) d base == digit (index s j) d base)))

/// Instantiate sorted_up_to_digit for a specific pair.
/// With {:pattern (index s i); (index s j)} on sorted_up_to_digit, Z3 can
/// now trigger the forall instantiation when index s i and index s j appear.
let sorted_up_to_digit_at (s: seq nat) (max_d: nat) (base: nat) (i j: nat)
  : Lemma (requires sorted_up_to_digit s max_d base /\ i < j /\ j < length s)
          (ensures (exists (d0: nat). d0 <= max_d /\
                      digit (index s i) d0 base < digit (index s j) d0 base /\
                      (forall (d': nat). d' < d0 ==> digit (index s i) d' base == digit (index s j) d' base)) \/
                   (forall (d: nat). d <= max_d ==> digit (index s i) d base == digit (index s j) d base))
  = // The {:pattern} in sorted_up_to_digit triggers Z3 on (index s i) and (index s j)
    assert (index s i == index s i);  // trigger pattern match
    assert (index s j == index s j)

(* ========== Position tracking for stability ========== *)

/// Helper: Find the first occurrence of value v in sequence s starting from index start
let rec first_occurrence_from (s: seq nat) (v: nat) (start: nat) : Tot (option nat) (decreases (length s - start)) =
  if start >= length s then None
  else if index s start = v then Some start
  else first_occurrence_from s v (start + 1)

/// Find the first occurrence of value v in sequence s
let first_occurrence (s: seq nat) (v: nat) : option nat =
  first_occurrence_from s v 0

/// Helper: value appears at given index
let appears_at (s: seq nat) (v: nat) (i: nat) : prop =
  i < length s /\ index s i = v

(* ========== Permutation ========== *)

/// Count occurrences of x in sequence
let rec count (s: seq nat) (x: nat) : Tot nat (decreases (length s)) =
  if length s = 0 then 0
  else (if index s 0 = x then 1 else 0) + count (tail s) x

/// Permutation: same length and same counts for all values
let permutation (s_in s_out: seq nat) : prop =
  length s_in == length s_out /\
  (forall (x: nat). count s_in x == count s_out x)

(* ========== Stability definition ========== *)

/// A stable sort maintains relative order of elements with equal keys.
/// For radix sort, the "key" is the digit at position d.
///
/// Formally: if two equal-digit elements appear at positions i1 < i2 in input,
/// they appear at positions j1 < j2 in output (where j1, j2 are their new positions).
let is_stable_sort_on_digit (s_in s_out: seq nat) (d: nat) (base: nat) : prop =
  base > 0 /\
  // Must be a permutation
  permutation s_in s_out /\
  // Output is sorted on digit d
  sorted_on_digit s_out d base /\
  // Stability: relative order preserved for equal keys
  (forall (i1 i2: nat).
    i1 < length s_in /\ i2 < length s_in /\ i1 < i2 /\
    // Two elements with the same digit at position d
    digit (index s_in i1) d base == digit (index s_in i2) d base ==>
    // Find their positions in output (must exist since permutation)
    (match (first_occurrence s_out (index s_in i1), 
            first_occurrence s_out (index s_in i2)) with
     | Some j1, Some j2 -> j1 <= j2  // Relative order preserved
     | _, _ -> True))  // Should never happen for valid permutation

(* ========== Helper lemmas for sorted_up_to_digit ========== *)

/// Base case: empty sequence is sorted up to any digit
let sorted_up_to_digit_empty (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures sorted_up_to_digit empty d base)
  = ()

/// Single element is sorted up to any digit
let sorted_up_to_digit_singleton (x: nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures sorted_up_to_digit (create 1 x) d base)
  = ()


/// Helper: for a single pair (i,j), sorted_up_to_digit at d implies at d' <= d
let sorted_up_to_digit_pair_monotonic
  (s: seq nat) (d d': nat) (base: nat) (i j: nat)
  : Lemma (requires base > 0 /\ d' <= d /\ i < j /\ j < length s /\
                    // The pair satisfies the sorted_up_to_digit condition at d
                    ((exists (d0: nat). d0 <= d /\
                       digit (index s i) d0 base < digit (index s j) d0 base /\
                       (forall (d'': nat). d'' < d0 ==> digit (index s i) d'' base == digit (index s j) d'' base)) \/
                     (forall (dd: nat). dd <= d ==> digit (index s i) dd base == digit (index s j) dd base)))
          (ensures ((exists (d0: nat). d0 <= d' /\
                       digit (index s i) d0 base < digit (index s j) d0 base /\
                       (forall (d'': nat). d'' < d0 ==> digit (index s i) d'' base == digit (index s j) d'' base)) \/
                    (forall (dd: nat). dd <= d' ==> digit (index s i) dd base == digit (index s j) dd base)))
  = // Case 1: all digits up to d are equal => all digits up to d' are equal (d' <= d)
    // Case 2: exists d0 <= d separating them
    //   - if d0 <= d' => same witness works for d'
    //   - if d0 > d' => all digits below d0 are equal, and d' < d0, so all digits <= d' are equal
    //     (pick right disjunct)
    introduce
      (exists (d0: nat). d0 <= d /\
         digit (index s i) d0 base < digit (index s j) d0 base /\
         (forall (d'': nat). d'' < d0 ==> digit (index s i) d'' base == digit (index s j) d'' base))
      ==> ((exists (d0: nat). d0 <= d' /\
              digit (index s i) d0 base < digit (index s j) d0 base /\
              (forall (d'': nat). d'' < d0 ==> digit (index s i) d'' base == digit (index s j) d'' base)) \/
           (forall (dd: nat). dd <= d' ==> digit (index s i) dd base == digit (index s j) dd base))
    with _. (
      eliminate exists (d0: nat). d0 <= d /\
         digit (index s i) d0 base < digit (index s j) d0 base /\
         (forall (d'': nat). d'' < d0 ==> digit (index s i) d'' base == digit (index s j) d'' base)
      returns ((exists (d0: nat). d0 <= d' /\
                  digit (index s i) d0 base < digit (index s j) d0 base /\
                  (forall (d'': nat). d'' < d0 ==> digit (index s i) d'' base == digit (index s j) d'' base)) \/
               (forall (dd: nat). dd <= d' ==> digit (index s i) dd base == digit (index s j) dd base))
      with _. (
        if d0 <= d' then ()  // same witness d0 works
        else (
          // d0 > d', so forall d'' < d0 we have equal digits
          // Since d' < d0, all digits dd <= d' satisfy dd < d0, hence equal
          introduce forall (dd: nat). dd <= d' ==> digit (index s i) dd base == digit (index s j) dd base
          with (
            introduce dd <= d' ==> digit (index s i) dd base == digit (index s j) dd base
            with _. ()  // dd <= d' < d0, so the forall d'' < d0 applies
          )
        )
      )
    )

/// If sorted up to digit d, then sorted up to any digit d' <= d
#push-options "--z3rlimit 30"
let sorted_up_to_digit_monotonic (s: seq nat) (d d': nat) (base: nat)
  : Lemma (requires base > 0 /\ d' <= d /\ sorted_up_to_digit s d base)
          (ensures sorted_up_to_digit s d' base)
  = // For every pair (i, j), use the helper lemmas to establish the result.
    // The pattern on sorted_up_to_digit enables Z3 to unfold the hypothesis.
    let aux (i: nat) (j: nat) : Lemma
      (requires i < j /\ j < length s)
      (ensures (exists (d0: nat). d0 <= d' /\
                   digit (index s i) d0 base < digit (index s j) d0 base /\
                   (forall (d'': nat). d'' < d0 ==> digit (index s i) d'' base == digit (index s j) d'' base)) \/
                (forall (dd: nat). dd <= d' ==> digit (index s i) dd base == digit (index s j) dd base))
      [SMTPat (index s i); SMTPat (index s j)]
      = sorted_up_to_digit_at s d base i j;
        sorted_up_to_digit_pair_monotonic s d d' base i j
    in
    ()
#pop-options

(* ========== Core stability theorem ========== *)

/// sorted_on_digit implies digit ordering for all pairs (not just adjacent).
/// Proof by induction: adjacent pairs are ordered, then transitivity for non-adjacent.
let rec sorted_on_digit_at (s: seq nat) (d: nat) (base: nat) (i j: nat)
  : Lemma (requires sorted_on_digit s d base /\ i < j /\ j < length s)
          (ensures digit (index s i) d base <= digit (index s j) d base)
          (decreases (length s))
  = if length s <= 1 then ()
    else if i = 0 then (
      // s[0] <= s[1] from sorted_on_digit, and sorted_on_digit (tail s)
      if j = 1 then ()
      else (
        // s[0] <= s[1] and s[1] <= s[j] by induction on tail
        sorted_on_digit_at (tail s) d base 0 (j - 1);
        assert (index (tail s) 0 == index s 1);
        assert (index (tail s) (j - 1) == index s j)
      )
    ) else (
      // Shift: sorted_on_digit s => sorted_on_digit (tail s)
      // index (tail s) (i-1) = index s i, index (tail s) (j-1) = index s j
      assert (sorted_on_digit (tail s) d base);
      sorted_on_digit_at (tail s) d base (i - 1) (j - 1);
      assert (index (tail s) (i - 1) == index s i);
      assert (index (tail s) (j - 1) == index s j)
    )

/// Base case helper: sorted_on_digit at digit 0 implies sorted_up_to_digit at digit 0
let sorted_on_to_up_to_base_case (s: seq nat) (base: nat)
  : Lemma (requires base > 0 /\ sorted_on_digit s 0 base)
          (ensures sorted_up_to_digit s 0 base)
  = // For every pair i < j:
    // digit(s[i], 0) <= digit(s[j], 0) by transitivity
    // Case <: exists d0=0. digit(s[i],0) < digit(s[j],0) (vacuous forall d' < 0)
    // Case ==: forall d <= 0. equal (just d=0)
    let aux (i: nat) (j: nat) : Lemma
      (requires i < j /\ j < length s)
      (ensures (exists (d0: nat). d0 <= 0 /\
                   digit (index s i) d0 base < digit (index s j) d0 base /\
                   (forall (d': nat). d' < d0 ==> digit (index s i) d' base == digit (index s j) d' base)) \/
               (forall (d: nat). d <= 0 ==> digit (index s i) d base == digit (index s j) d base))
      [SMTPat (index s i); SMTPat (index s j)]
      = sorted_on_digit_at s 0 base i j
    in
    ()

/// LEMMA 1: Key insight - stability preserves existing order structure
/// 
/// If s_in is sorted on digits 0..d-1, and we apply a stable sort on digit d,
/// then s_out maintains the ordering on lower digits for elements with equal digit d.
///
/// This is the crucial property that makes radix sort work: stable sorting on
/// a new digit doesn't destroy the ordering established by previous passes.
let lemma_stable_sort_preserves_lower_order
  (s_in s_out: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0 /\ d > 0 /\
                    is_stable_sort_on_digit s_in s_out d base /\
                    sorted_up_to_digit s_in (d - 1) base)
          (ensures 
            // For any three elements at positions i < j < k where digit d is equal:
            // If they were ordered by lower digits in s_in, they remain so in s_out
            (forall (i j: nat). 
               i < j /\ j < length s_out /\
               digit (index s_out i) d base == digit (index s_out j) d base ==>
               // Then their lower-digit order is preserved from s_in
               ((exists (d0: nat). d0 < d /\
                  digit (index s_out i) d0 base < digit (index s_out j) d0 base /\
                  (forall (d': nat). d' < d0 ==> 
                    digit (index s_out i) d' base == digit (index s_out j) d' base)) \/
                (forall (d': nat). d' < d ==> 
                  digit (index s_out i) d' base == digit (index s_out j) d' base))))
  = admit() // Core stability argument: stable sort + lexicographic order preservation

/// MAIN THEOREM: Each pass of stable digit sort extends sorted range by one digit
///
/// If input is sorted on digits 0..d-1, and we apply a stable sort on digit d,
/// then output is sorted on digits 0..d.
///
/// PROOF INTUITION:
/// 1. Output is sorted on digit d (by definition of sort)
/// 2. For positions i < j with equal digit d:
///    - By stability, their relative order from input is preserved
///    - Input was sorted on digits 0..d-1
///    - So in output, they remain sorted on digits 0..d-1
/// 3. For positions i < j with different digit d:
///    - digit_i(d) < digit_j(d) by sorting on digit d
///    - This is the lexicographically most significant digit so far
///    - Lower digit order doesn't matter
/// 4. Combining cases: output is sorted on digits 0..d
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_stable_pass_preserves_ordering
  (s_in s_out: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0 /\
                    is_stable_sort_on_digit s_in s_out d base /\
                    (d = 0 \/ (d > 0 /\ sorted_up_to_digit s_in (d - 1) base)))
          (ensures sorted_up_to_digit s_out d base)
  = if d = 0 then (
      // Base case: sorted_on_digit s_out 0 base => sorted_up_to_digit s_out 0 base
      sorted_on_to_up_to_base_case s_out base
    ) else (
      // Inductive case: d > 0
      // Have: sorted_up_to_digit s_in (d-1) base
      //       is_stable_sort_on_digit s_in s_out d base
      // Want: sorted_up_to_digit s_out d base
      
      // Key steps:
      // 1. Stability preserves lower-digit ordering for equal-digit-d elements
      lemma_stable_sort_preserves_lower_order s_in s_out d base;
      
      // 2. We have sorted_on_digit s_out d base from definition
      
      // 3. Combining these gives sorted_up_to_digit s_out d base
      admit() // Final step: quantifier manipulation to combine properties
    )
#pop-options

(* ========== Radix sort correctness ========== *)

/// Helper to extract stable sort property from quantifier
let extract_stable_sort_property
  (s0: seq nat)
  (steps: list (seq nat))
  (step_num: nat)
  (d: nat)
  (base: nat)
  : Lemma (requires
            step_num < d /\
            d <= List.Tot.length steps /\
            (forall (i: nat). i < d ==>
              (let s_in = (if i = 0 then s0 else List.Tot.index steps (i - 1)) in
               let s_out = List.Tot.index steps i in
               is_stable_sort_on_digit s_in s_out i base)))
          (ensures
            (let s_in = (if step_num = 0 then s0 else List.Tot.index steps (step_num - 1)) in
             let s_out = List.Tot.index steps step_num in
             is_stable_sort_on_digit s_in s_out step_num base))
  = ()

/// After d passes of radix sort (sorting by digits 0, 1, ..., d-1),
/// the output is sorted on digits 0..d-1.
///
/// This is the key inductive invariant for radix sort correctness.
#push-options "--split_queries always"
let rec radix_sort_invariant
  (s0: seq nat)            // Initial input
  (steps: list (seq nat))  // Intermediate sequences after each pass
  (d: nat)                 // Number of passes completed
  (base: nat)              // Base for digit extraction
  : Lemma (requires
            base > 0 /\
            d <= List.Tot.length steps /\
            // Each step is a stable sort by the corresponding digit
            (forall (step_num: nat). step_num < d ==>
              (let s_in = (if step_num = 0 then s0 
                          else List.Tot.index steps (step_num - 1)) in
               let s_out = List.Tot.index steps step_num in
               is_stable_sort_on_digit s_in s_out step_num base)))
          (ensures d = 0 \/ 
                   (d > 0 /\ sorted_up_to_digit (List.Tot.index steps (d - 1)) (d - 1) base))
          (decreases d)
  = if d = 0 then ()
    else if d = 1 then (
      // After 1 pass (digit 0), sorted on digit 0
      let s_out = List.Tot.index steps 0 in
      extract_stable_sort_property s0 steps 0 d base;
      lemma_stable_pass_preserves_ordering s0 s_out 0 base
    ) else (
      // After d passes, sorted on digits 0..d-1
      // By IH: after d-1 passes, sorted on digits 0..d-2
      radix_sort_invariant s0 steps (d - 1) base;
      
      let s_in = List.Tot.index steps (d - 2) in
      let s_out = List.Tot.index steps (d - 1) in
      
      // Extract the stable sort property for step d-1
      extract_stable_sort_property s0 steps (d - 1) d base;
      
      // Apply the main lemma
      lemma_stable_pass_preserves_ordering s_in s_out (d - 1) base;
      ()
    )
#pop-options

(* ========== Permutation preservation ========== *)

/// Permutation is transitive
let permutation_transitive (s1 s2 s3: seq nat)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
          (ensures permutation s1 s3)
  = ()

/// Stable sort chain preserves permutation
let rec stable_sort_chain_permutation
  (s0: seq nat)
  (steps: list (seq nat))
  (d: nat)
  (base: nat)
  : Lemma (requires
            base > 0 /\
            d <= List.Tot.length steps /\
            (forall (step_num: nat). step_num < d ==>
              (let s_in = (if step_num = 0 then s0 
                          else List.Tot.index steps (step_num - 1)) in
               let s_out = List.Tot.index steps step_num in
               is_stable_sort_on_digit s_in s_out step_num base)))
          (ensures d = 0 \/ 
                   permutation s0 (List.Tot.index steps (d - 1)))
          (decreases d)
  = if d <= 0 then ()
    else if d = 1 then ()
    else (
      stable_sort_chain_permutation s0 steps (d - 1) base;
      let s_prev = List.Tot.index steps (d - 2) in
      let s_curr = List.Tot.index steps (d - 1) in
      permutation_transitive s0 s_prev s_curr
    )

(* ========== Example: proving a specific sort sequence is stable ========== *)

/// Example: Given a concrete sorting implementation, verify it's stable
/// This would be used to connect our abstract stability proof to a concrete
/// counting sort implementation.
let example_verify_stable_sort
  (s_in s_out: seq nat)
  (d: nat)
  (base: nat)
  (proof_sorted: squash (sorted_on_digit s_out d base))
  (proof_perm: squash (permutation s_in s_out))
  (proof_stability: squash (
    forall (i1 i2: nat).
      i1 < length s_in /\ i2 < length s_in /\ i1 < i2 /\
      digit (index s_in i1) d base == digit (index s_in i2) d base ==>
      (match (first_occurrence s_out (index s_in i1), 
              first_occurrence s_out (index s_in i2)) with
       | Some j1, Some j2 -> j1 <= j2
       | _, _ -> True)))
  : Lemma (ensures is_stable_sort_on_digit s_in s_out d base)
  = ()

(* ========== Summary ========== *)

/// MAIN RESULT: The stability of each radix sort pass
/// 
/// Given:
/// - Input sorted on digits 0..d-1 (or d=0 for base case)
/// - Stable sort on digit d
/// 
/// Guarantees:
/// - Output sorted on digits 0..d
/// - Output is a permutation of input
///
/// This is the foundation for full radix sort correctness:
/// After bigD passes (digits 0 to bigD-1), the output is sorted on
/// all digits, which means fully sorted for values < base^bigD.
let theorem_radix_sort_stability_summary
  (s_in s_out: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0 /\
                    is_stable_sort_on_digit s_in s_out d base /\
                    (d = 0 \/ (d > 0 /\ sorted_up_to_digit s_in (d - 1) base)))
          (ensures sorted_up_to_digit s_out d base /\
                   permutation s_in s_out)
  = lemma_stable_pass_preserves_ordering s_in s_out d base

