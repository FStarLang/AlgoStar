(*
   RadixSort Full Correctness (Task P1.2.5)
   
   This module proves that after all d passes of RadixSort, the output array
   is sorted by full key value, not just by individual digits.
   
   KEY THEOREM: radix_sort_fully_sorted
   
   Strategy:
   1. Use stability proof (P1.2.4): after d passes, sorted on digits 0..d-1
   2. Prove: sorted on all digits 0..d-1 implies sorted by full value
   3. This requires showing lexicographic digit order equals numeric order
   
   Main steps:
   - Digit decomposition: any number k = sum of (digit_i * base^i)
   - If all digits 0..d-1 are lexicographically ordered, then values are ordered
   - Apply this to the result of radix_sort_invariant
   
   NO admits for basic arithmetic - admits only for complex digit algebra.
*)

module CLRS.Ch08.RadixSort.FullSort

open FStar.Seq
open FStar.Math.Lemmas
open FStar.Mul
open FStar.Classical
open CLRS.Ch08.RadixSort.Stability
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties

(* ========== FullSort-specific definitions ========== *)

/// A sequence is sorted if each element is <= the next
let rec sorted (s: seq nat) : Tot prop (decreases (length s)) =
  length s <= 1 \/ (index s 0 <= index s 1 /\ sorted (tail s))

let rec pow_monotonic (base exp1 exp2: nat)
  : Lemma (requires base >= 2 /\ exp1 <= exp2)
          (ensures pow base exp1 <= pow base exp2)
          (decreases exp2)
  = if exp1 = exp2 then ()
    else if exp1 = 0 then pow_positive base exp2
    else pow_monotonic base exp1 (exp2 - 1)

/// Helper: if count > 0, the element appears somewhere in the sequence
let rec count_positive_means_appears (s: seq nat) (v: nat)
  : Lemma (requires count s v > 0)
          (ensures (exists (i: nat). i < length s /\ index s i == v))
          (decreases (length s))
  = if length s = 0 then ()
    else if index s 0 = v then ()
    else count_positive_means_appears (tail s) v

/// Helper: if an element appears in a sequence, its count is positive
let rec element_appears_means_count_positive (s: seq nat) (i: nat{i < length s})
  : Lemma (ensures count s (index s i) > 0)
          (decreases (length s))
  = if i = 0 then ()
    else element_appears_means_count_positive (tail s) (i - 1)

/// Helper: permutation preserves upper bounds on elements
let permutation_preserves_bounds (s_in s_out: seq nat) (bound: nat)
  : Lemma (requires permutation s_in s_out /\
                    (forall (i: nat). i < length s_in ==> index s_in i < bound))
          (ensures (forall (i: nat). i < length s_out ==> index s_out i < bound))
  = let aux (i: nat{i < length s_out}) : Lemma (index s_out i < bound) =
      let v = index s_out i in
      element_appears_means_count_positive s_out i;
      assert (count s_out v > 0);
      assert (count s_in v == count s_out v);
      assert (count s_in v > 0);
      count_positive_means_appears s_in v;
      ()
    in
    Classical.forall_intro aux

(* ========== Digit decomposition ========== *)

/// Sum of digits 0 to d-1
let rec digit_sum (k: nat) (d: nat) (base: nat) : Tot nat (decreases d) =
  if d = 0 || base = 0 then 0
  else digit k (d - 1) base * pow base (d - 1) + digit_sum k (d - 1) base

/// Helper lemma: if all digits equal, digit sums are equal
let rec digit_sum_equal_helper (x y: nat) (bigD: nat) (base: nat)
  : Lemma (requires base >= 2 /\
                    (forall (d: nat). d < bigD ==> digit x d base == digit y d base))
          (ensures digit_sum x bigD base == digit_sum y bigD base)
          (decreases bigD)
  = if bigD = 0 || base = 0 then ()
    else (
      // digit_sum x bigD = digit x (bigD-1) * pow base (bigD-1) + digit_sum x (bigD-1)
      // digit_sum y bigD = digit y (bigD-1) * pow base (bigD-1) + digit_sum y (bigD-1)
      digit_sum_equal_helper x y (bigD - 1) base;
      // By forall assumption: digit x (bigD-1) == digit y (bigD-1)
      assert (digit x (bigD - 1) base == digit y (bigD - 1) base);
      // And by IH: digit_sum x (bigD-1) == digit_sum y (bigD-1)
      ()
    )

/// Helper: digit extraction properties
let digit_at_lower (k: nat) (d: nat) (base: nat)
  : Lemma (requires base >= 2 /\ d > 0)
          (ensures digit k d base == digit (k / base) (d - 1) base)
  = pow_positive base (d - 1);
    pow_positive base d;
    // digit k d base = (k / base^d) % base
    // digit (k/base) (d-1) base = ((k/base) / base^(d-1)) % base
    //                           = (k / (base * base^(d-1))) % base
    //                           = (k / base^d) % base
    ()

/// Helper: pow splits: base^(a+b) = base^a * base^b
let rec pow_split (base a b: nat)
  : Lemma (ensures pow base (a + b) == pow base a * pow base b)
          (decreases a)
  = if a = 0 then ()
    else begin
      pow_split base (a - 1) b;
      assert (pow base (a - 1 + b) == pow base (a - 1) * pow base b);
      assert (pow base (a + b) == base * pow base (a - 1 + b));
      assert (pow base a == base * pow base (a - 1))
    end

/// Helper: Raw form - digits below preserved by modulo  
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let digit_preserved_by_modulo_raw (k: nat) (d: nat) (bigD: nat) (base: nat)
  : Lemma (requires base >= 2 /\ d < bigD /\ bigD > 0 /\ pow base d > 0 /\ pow base bigD > 0)
          (ensures (k / pow base d) % base == ((k % pow base bigD) / pow base d) % base)
  = // pow base bigD = pow base d * pow base (bigD - d)
    pow_split base d (bigD - d);
    assert (pow base (d + (bigD - d)) == pow base d * pow base (bigD - d));
    assert (d + (bigD - d) == bigD);
    pow_positive base (bigD - d);
    // modulo_division_lemma: (a % (b * c)) / b = (a / b) % c
    modulo_division_lemma k (pow base d) (pow base (bigD - d));
    assert ((k % pow base bigD) / pow base d == (k / pow base d) % pow base (bigD - d));
    // Now: ((k % pow base bigD) / pow base d) % base = ((k / pow base d) % pow base (bigD-d)) % base
    // Since bigD - d >= 1, pow base (bigD-d) = base * pow base (bigD-d-1)
    pow_positive base (bigD - d - 1);
    pow_split base 1 (bigD - d - 1);
    assert (pow base (1 + (bigD - d - 1)) == pow base 1 * pow base (bigD - d - 1));
    assert (pow base 1 == base);
    assert (pow base (bigD - d) == base * pow base (bigD - d - 1));
    // modulo_modulo_lemma: (a % (b * c)) % b = a % b
    modulo_modulo_lemma (k / pow base d) base (pow base (bigD - d - 1))
    
/// Wrapper that connects to digit function
let digit_preserved_by_modulo (k: nat) (d: nat) (bigD: nat) (base: nat)
  : Lemma (requires base >= 2 /\ d < bigD /\ bigD > 0 /\ pow base bigD > 0)
          (ensures digit k d base == digit (k % pow base bigD) d base)
  = pow_positive base d;
    pow_positive base bigD;
    digit_preserved_by_modulo_raw k d bigD base
#pop-options

/// Key property: a number equals the sum of its digits times powers of base
/// For k < base^bigD, we have k = sum_{i=0}^{bigD-1} digit(k,i) * base^i
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec digit_decomposition (k: nat) (bigD: nat) (base: nat)
  : Lemma (requires bigD > 0 /\ base >= 2 /\ k < pow base bigD)
          (ensures k == digit_sum k bigD base)
          (decreases bigD)
  = if bigD = 1 then (
      // Base case: k < base, so k has only digit 0
      // digit_sum k 1 base = digit k 0 base * base^0 = (k % base) * 1 = k
      pow_positive base 0;
      assert (pow base 0 == 1);
      assert (k < base);
      small_modulo_lemma_1 k base;
      assert (k % base == k);
      assert (digit k 0 base == k);
      assert (digit_sum k 1 base == k)
    ) else (
      // Inductive case: k < base^bigD where bigD > 1
      pow_positive base (bigD - 1);
      pow_positive base bigD;
      assert (pow base (bigD - 1) > 0);  // Explicitly state for type checking
      
      // Division theorem: k = q * pow base (bigD-1) + r where r = k % pow base (bigD-1)
      lemma_div_mod k (pow base (bigD - 1));
      let q = k / pow base (bigD - 1) in
      let r = k % pow base (bigD - 1) in
      
      // Bound on quotient: k < base * pow base (bigD-1) implies q < base
      assert (pow base bigD == base * pow base (bigD - 1));
      assert (k < base * pow base (bigD - 1));
      assert (k == q * pow base (bigD - 1) + r);
      modulo_range_lemma k (pow base (bigD - 1));
      assert (r < pow base (bigD - 1));
      // From k = q * c + r and k < b * c and r < c, we get q < b
      assert (q < base);
      
      // The highest digit equals q
      small_modulo_lemma_1 q base;
      assert (digit k (bigD - 1) base == q);
      
      // Apply IH to remainder
      digit_decomposition r (bigD - 1) base;
      assert (r == digit_sum r (bigD - 1) base);
      
      // Show all lower digits match: digit k d == digit r d for all d < bigD-1
      let aux (d: nat{d < bigD - 1}) : Lemma (digit k d base == digit r d base) =
        digit_preserved_by_modulo k d (bigD - 1) base
      in
      Classical.forall_intro aux;
      digit_sum_equal_helper k r (bigD - 1) base;
      assert (digit_sum k (bigD - 1) base == digit_sum r (bigD - 1) base);
      
      // Combine: digit_sum k bigD = q * pow base (bigD-1) + digit_sum k (bigD-1)
      //                            = q * pow base (bigD-1) + r = k
      ()
    )
#pop-options

(* ========== Lexicographic order implies numeric order ========== *)

/// Helper: digit_sum k d base < pow base d
let rec lemma_digit_sum_bound_3 (k: nat) (d: nat) (base: nat)
  : Lemma (requires base >= 2)
          (ensures digit_sum k d base < pow base d)
          (decreases d)
  = if d = 0 || base = 0 then (pow_positive base 0)
    else (
      lemma_digit_sum_bound_3 k (d - 1) base;
      digit_bound k (d - 1) base;
      pow_positive base (d - 1);
      // digit k (d-1) base < base
      // digit k (d-1) base * pow base (d-1) <= (base - 1) * pow base (d-1)
      lemma_mult_le_right (pow base (d - 1)) (digit k (d - 1) base) (base - 1);
      // (base - 1) * pow base (d-1) + pow base (d-1) = base * pow base (d-1) = pow base d
      ()
    )

/// Helper: digit_sum ordering when MSD differs
#push-options "--z3rlimit 30 --fuel 2"
let rec lemma_digit_sum_msd_le_3 (x y: nat) (d d0: nat) (base: nat)
  : Lemma (requires base >= 2 /\ d0 < d /\
                    digit x d0 base < digit y d0 base /\
                    (forall (d': nat). d0 < d' /\ d' < d ==> digit x d' base == digit y d' base))
          (ensures digit_sum x d base <= digit_sum y d base)
          (decreases d)
  = if d = d0 + 1 then (
      // digit_sum k (d0+1) = digit k d0 * pow base d0 + digit_sum k d0
      pow_positive base d0;
      lemma_digit_sum_bound_3 x d0 base;
      // digit(x,d0) < digit(y,d0) => digit(x,d0) <= digit(y,d0) - 1
      // digit(x,d0) * base^d0 + digit_sum x d0 
      //   <= (digit(y,d0) - 1) * base^d0 + (base^d0 - 1)
      //   = digit(y,d0) * base^d0 - 1
      //   <= digit(y,d0) * base^d0 + digit_sum y d0
      lemma_mult_le_right (pow base d0) (digit x d0 base) (digit y d0 base - 1);
      ()
    ) else (
      // d > d0 + 1: digit(x, d-1) == digit(y, d-1) since d-1 > d0
      assert (digit x (d - 1) base == digit y (d - 1) base);
      lemma_digit_sum_msd_le_3 x y (d - 1) d0 base;
      ()
    )
#pop-options

/// If two numbers have digits that compare lexicographically (from low to high),
/// then the numbers themselves compare numerically.
///
/// Key insight: In base-b positional notation, if x and y differ first at digit d,
/// then the contribution from digit d (and all higher digits) determines the order.
/// Since digit_x(d) < digit_y(d), we have x < y regardless of higher digits.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let digits_lex_order_implies_numeric_order
  (x y: nat) (bigD: nat) (base: nat)
  : Lemma (requires bigD > 0 /\ base >= 2 /\
                    x < pow base bigD /\ y < pow base bigD /\
                    // MSD-primary lexicographic comparison on digits 0..bigD-1
                    ((exists (d0: nat). d0 < bigD /\
                       digit x d0 base < digit y d0 base /\
                       (forall (d': nat). d0 < d' /\ d' < bigD ==> 
                         digit x d' base == digit y d' base)) \/
                     (forall (d: nat). d < bigD ==> 
                       digit x d base == digit y d base)))
          (ensures x <= y)
          (decreases bigD)
  = digit_decomposition x bigD base;
    digit_decomposition y bigD base;
    
    if bigD = 1 then ()
    else (
      // Case split: all digits equal vs exists separating digit
      match FStar.StrongExcludedMiddle.strong_excluded_middle
        (forall (d: nat). d < bigD ==> digit x d base == digit y d base) with
      | true -> 
        // All digits equal: digit_sum x = digit_sum y, so x = y
        digit_sum_equal_helper x y bigD base
      | false ->
        // Exists d0 with digit x d0 < digit y d0 and higher digits equal
        // Use eliminate exists pattern
        eliminate exists (d0: nat).
          d0 < bigD /\ digit x d0 base < digit y d0 base /\
          (forall (d': nat). d0 < d' /\ d' < bigD ==> digit x d' base == digit y d' base)
        returns digit_sum x bigD base <= digit_sum y bigD base
        with _. lemma_digit_sum_msd_le_3 x y bigD d0 base
    )
#pop-options

/// If all digits are equal, then the numbers are equal
let digits_all_equal_implies_equal
  (x y: nat) (bigD: nat) (base: nat)
  : Lemma (requires bigD > 0 /\ base >= 2 /\
                    x < pow base bigD /\ y < pow base bigD /\
                    (forall (d: nat). d < bigD ==> digit x d base == digit y d base))
          (ensures x == y)
  = digit_decomposition x bigD base;
    digit_decomposition y bigD base;
    // Since all digits equal, digit_sum x bigD base == digit_sum y bigD base
    digit_sum_equal_helper x y bigD base;
    // Therefore x == digit_sum x bigD base == digit_sum y bigD base == y
    ()

(* ========== Main theorem: sorted_up_to_digit implies sorted ========== *)

/// Helper: prove sorted by induction after establishing pairwise order
/// Note: This requires standard sequence lemmas about tail and indexing
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec lemma_pairwise_le_implies_sorted (s: seq nat)
  : Lemma (requires length s > 0 /\
                    (forall (i j: nat). i < length s /\ j < length s /\ i < j ==> 
                      index s i <= index s j))
          (ensures sorted s)
          (decreases (length s))
  = if length s <= 1 then ()
    else (
      // sorted s = index s 0 <= index s 1 /\ sorted (tail s)
      // Part 1: index s 0 <= index s 1 is trivially from pairwise with i=0, j=1
      
      // Part 2: sorted (tail s), by recursion
      let t = tail s in
      if length t <= 1 then ()
      else (
        // Need to show: forall i j. i < |t| /\ j < |t| /\ i < j ==> index t i <= index t j
        // We know: tail s == slice s 1 (length s)
        // So index t k == index s (k + 1) by lemma_index_slice
        let aux (i: nat) (j: nat) : Lemma 
          (requires i < length t /\ j < length t /\ i < j)
          (ensures index t i <= index t j)
          [SMTPat (index t i); SMTPat (index t j)]
          = Seq.lemma_index_slice s 1 (length s) i;
            Seq.lemma_index_slice s 1 (length s) j;
            // Explicitly access s at (i+1) and (j+1) to trigger the quantifier
            let _ = index s (i + 1) in
            let _ = index s (j + 1) in
            ()
        in
        lemma_pairwise_le_implies_sorted t
      )
    )
#pop-options

/// If a sequence is sorted up to digit d (lexicographically on digits 0..d),
/// then it is sorted by full numeric value.
///
/// This is the key bridge between digit-wise sorting and value sorting.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let lemma_sorted_up_to_all_digits_implies_sorted
  (s: seq nat) (bigD: nat) (base: nat)
  : Lemma (requires bigD > 0 /\ base >= 2 /\
                    (forall (i: nat). i < length s ==> index s i < pow base bigD) /\
                    sorted_up_to_digit s (bigD - 1) base)
          (ensures sorted s)
  = if length s <= 1 then ()
    else (
      // For each pair (i, j) with i < j, sorted_up_to_digit gives lex order on digits 0..bigD-1
      let aux (i: nat{i < length s}) (j: nat{j < length s /\ i < j})
        : Lemma (index s i <= index s j)
        = sorted_up_to_digit_at s (bigD - 1) base i j;
          digits_lex_order_implies_numeric_order (index s i) (index s j) bigD base
      in
      // Establish pairwise ordering explicitly
      let pairwise_aux (i: nat{i < length s}) : Lemma
        (forall (j: nat{j < length s /\ i < j}). index s i <= index s j)
        = Classical.forall_intro (aux i)
      in
      // Now use the pairwise ordering to show sorted
      // Need: forall i j. i < |s| /\ j < |s| /\ i < j ==> s[i] <= s[j]
      // We have it for each i. Use forall_intro:
      let top (i: nat) : Lemma 
        (i < length s ==> (forall (j: nat{j < length s /\ i < j}). index s i <= index s j))
        = if i < length s then pairwise_aux i else ()
      in
      Classical.forall_intro top;
      lemma_pairwise_le_implies_sorted s
    )
#pop-options

(* ========== Stability is imported from CLRS.Ch08.RadixSort.Stability ========== *)
(* is_stable_sort_on_digit, radix_sort_invariant, stable_sort_chain_permutation,  *)
(* sorted_on_digit, sorted_up_to_digit, permutation, count, etc. are all         *)
(* imported via open CLRS.Ch08.RadixSort.Stability above.                         *)

(* ========== Main correctness theorem ========== *)

/// THEOREM P1.2.5: Radix sort produces a fully sorted permutation
///
/// After bigD passes of radix sort (sorting by digits 0, 1, ..., bigD-1),
/// the output sequence is:
/// 1. A permutation of the input
/// 2. Sorted by full numeric value
///
/// This is CLRS Lemma 8.3: the complete correctness of radix sort.
///
/// Proof structure:
/// 1. By radix_sort_invariant: after bigD passes, sorted_up_to_digit on digits 0..bigD-1
/// 2. By lemma_sorted_up_to_all_digits_implies_sorted: sorted_up_to_digit implies sorted
/// 3. By stable_sort_chain_permutation: result is a permutation
/// 4. Therefore: result is a sorted permutation ∎
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let radix_sort_fully_sorted
  (s0: seq nat)
  (steps: list (seq nat))
  (bigD: nat)
  (base: nat)
  : Lemma (requires
            bigD > 0 /\
            base >= 2 /\
            // All input values fit in bigD digits
            (forall (i: nat). i < length s0 ==> index s0 i < pow base bigD) /\
            // We have exactly bigD steps
            List.Tot.length steps == bigD /\
            // Each step is a stable sort on the corresponding digit
            (forall (step_num: nat). step_num < bigD ==>
              (let s_in = (if step_num = 0 then s0 
                          else List.Tot.index steps (step_num - 1)) in
               let s_out = List.Tot.index steps step_num in
               is_stable_sort_on_digit s_in s_out step_num base)))
          (ensures
            (let s_final = List.Tot.index steps (bigD - 1) in
             // Result is a permutation of input
             permutation s0 s_final /\
             // Result is sorted by full value
             sorted s_final))
  = let s_final = List.Tot.index steps (bigD - 1) in
    
    // Step 1: Prove sorted_up_to_digit (from stability module)
    radix_sort_invariant s0 steps bigD base;
    assert (sorted_up_to_digit s_final (bigD - 1) base);
    
    // Step 2: Prove permutation (from stability module)
    stable_sort_chain_permutation s0 steps bigD base;
    assert (permutation s0 s_final);
    
    // Step 3: Permutation preserves bounds
    // If all elements of s0 are < pow base bigD, so are all elements of s_final
    permutation_preserves_bounds s0 s_final (pow base bigD);
    
    // Step 4: Apply the key lemma
    lemma_sorted_up_to_all_digits_implies_sorted s_final bigD base;
    assert (sorted s_final);
    ()
#pop-options

(* ========== Corollary: simpler statement ========== *)

/// Simplified version: given proper radix sort execution, result is sorted
let radix_sort_correct
  (s0 s_final: seq nat)
  (bigD: nat)
  (base: nat)
  (steps: list (seq nat))
  : Lemma (requires
            bigD > 0 /\
            base >= 2 /\
            (forall (i: nat). i < length s0 ==> index s0 i < pow base bigD) /\
            List.Tot.length steps == bigD /\
            (forall (step_num: nat). step_num < bigD ==>
              (let s_in = (if step_num = 0 then s0 
                          else List.Tot.index steps (step_num - 1)) in
               let s_out = List.Tot.index steps step_num in
               is_stable_sort_on_digit s_in s_out step_num base)) /\
            s_final == List.Tot.index steps (bigD - 1))
          (ensures
            permutation s0 s_final /\
            sorted s_final)
  = radix_sort_fully_sorted s0 steps bigD base

(* ========== Summary ========== *)

/// Task P1.2.5 Complete: We have proven that after all d passes of RadixSort,
/// the output array is sorted by full key value.
///
/// Key components:
/// 1. Digit decomposition: numbers equal their digit sums
/// 2. Lexicographic order: digit-wise order implies numeric order  
/// 3. Stability result (P1.2.4): d passes give sorted_up_to_digit
/// 4. Main theorem: combines above to show full sorting
///
/// This completes the formal verification of CLRS Radix Sort correctness!
