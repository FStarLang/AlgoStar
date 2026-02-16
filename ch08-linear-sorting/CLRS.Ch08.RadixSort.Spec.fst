(*
   Radix Sort Specification - Multi-digit correctness theory
   
   This module provides the mathematical foundation for CLRS Radix Sort
   (Section 8.3) with d digits in base b.
   
   Key results:
   1. Digit extraction and decomposition (any k can be written as sum of digits)
   2. Stable sorting preserves relative order for equal keys
   3. CLRS Lemma 8.3: After d passes of stable sort (by digit 0, 1, ..., d-1),
      the array is sorted by the full key value.
   
   NO admits for basic digit arithmetic.
   Admits OK for high-level stability lemmas (proof of concept).
*)

module CLRS.Ch08.RadixSort.Spec

open FStar.Seq
open FStar.Math.Lemmas
open FStar.Mul
open FStar.Classical
module Seq = FStar.Seq

(* ========== Power function ========== *)

let rec pow (base: nat) (exp: nat) : nat =
  if exp = 0 then 1
  else base * pow base (exp - 1)

let pow_zero (base: nat) 
  : Lemma (pow base 0 == 1)
  = ()

let rec pow_succ (base: nat) (d: nat)
  : Lemma (pow base (d + 1) == base * pow base d)
  = if d = 0 then ()
    else pow_succ base (d - 1)

let rec pow_positive (base: nat) (exp: nat)
  : Lemma (requires base > 0)
          (ensures pow base exp > 0)
          (decreases exp)
  = if exp = 0 then ()
    else pow_positive base (exp - 1)

let rec pow_one (exp: nat)
  : Lemma (pow 1 exp == 1)
  = if exp = 0 then () else pow_one (exp - 1)

let rec pow_monotonic (base exp1 exp2: nat)
  : Lemma (requires base >= 2 /\ exp1 <= exp2)
          (ensures pow base exp1 <= pow base exp2)
          (decreases exp2)
  = if exp1 = exp2 then ()
    else if exp1 = 0 then pow_positive base exp2
    else pow_monotonic base exp1 (exp2 - 1)

(* ========== Digit extraction ========== *)

// Extract the d-th digit of k in the given base.
// digit k d base = (k / base^d) mod base
let digit (k d base: nat) : nat =
  if base > 0 then (
    pow_positive base d;
    (k / pow base d) % base
  ) else 0

// Digit is always less than base
let digit_bound (k d base: nat)
  : Lemma (requires base > 0)
          (ensures digit k d base < base)
  = pow_positive base d;
    lemma_mod_lt (k / pow base d) base

// Digit of zero is zero
let digit_zero (d base: nat)
  : Lemma (requires base > 0)
          (ensures digit 0 d base == 0)
  = pow_positive base d;
    small_modulo_lemma_1 0 base

(* ========== Digit decomposition ========== *)

// Sum of k's first d digits * powers of base
let rec digit_sum (k bigD base d: nat) : Tot nat (decreases d) =
  if d = 0 || base = 0 then 0
  else digit k (d - 1) base * pow base (d - 1) + digit_sum k bigD base (d - 1)

// Main decomposition theorem: k equals the sum of its digits
// This is a key property but complex to prove - we admit the detailed algebra
// Helper lemma: if k < base * p then k / p < base
let lemma_div_pow_bound (k base p: nat)
  : Lemma (requires base >= 1 /\ p > 0 /\ k < base * p)
          (ensures k / p < base)
  = // By contradiction: assume k / p >= base
    // Then k / p * p >= base * p (since p > 0)
    // By division: k >= (k / p) * p (since k = (k/p)*p + k%p and k%p >= 0)
    // Actually, we have k = (k/p)*p + k%p, so k >= (k/p)*p
    // If k / p >= base, then k >= base * p, contradicting k < base * p
    ()

let rec lemma_pow_add (base: nat) (m n: nat)
  : Lemma (requires base >= 2)
          (ensures pow base (m + n) == pow base m * pow base n)
          (decreases m)
  = if m = 0 then pow_zero base
    else (
      pow_succ base (m - 1 + n);
      pow_succ base (m - 1);
      lemma_pow_add base (m - 1) n
    )

// Helper lemma: lower digits of k are the same as digits of k % pow base d
let lemma_digit_mod (k d base: nat) (d': nat)
  : Lemma (requires base >= 2 /\ d > 0 /\ d' < d /\ pow base d > 0 /\ pow base d' > 0)
          (ensures digit k d' base == digit (k % pow base d) d' base)
  = pow_positive base d;
    pow_positive base d';
    pow_monotonic base d' d;
    
    // We want to show: (k / pow base d') % base == ((k % pow base d) / pow base d') % base
    
    // We'll use modulo_division_lemma: (a % (b * c)) / b = (a / b) % c
    // Set a = k, b = pow base d', c = pow base (d - d')
    // Then b * c = pow base d' * pow base (d - d') = pow base d
    
    // First, show that pow base d = pow base d' * pow base (d - d')
    assert (d' + (d - d') == d);
    lemma_pow_add base d' (d - d');
    assert (pow base d == pow base d' * pow base (d - d'));
    
    // Now apply modulo_division_lemma
    modulo_division_lemma k (pow base d') (pow base (d - d'));
    
    // This gives us: (k % (pow base d' * pow base (d - d'))) / pow base d' = (k / pow base d') % (pow base (d - d'))
    //            i.e.: (k % pow base d) / pow base d' = (k / pow base d') % (pow base (d - d'))
    
    // Now we need: ((k / pow base d') % pow base (d - d')) % base = (k / pow base d') % base
    // Since d - d' >= 1, pow base (d - d') >= base
    
    pow_positive base (d - d');
    assert (pow base (d - d') >= base);  // since base >= 2 and d - d' >= 1
    
    // Use modulo_modulo_lemma: (a % b) % c = a % c when c divides b
    // Or more directly: if b >= c, then (a % b) % c reduces properly
    
    // Actually the right lemma is: (a % (b*c)) % b = a % b
    // Which follows from modulo_modulo_lemma
    
    // Let me use a different approach: show that
    // (x % (base * y)) % base = x % base for any y >= 1
    
    // For d - d' = 1: pow base 1 = base, so (k / pow base d') % base = (k / pow base d') % base trivially
    // For d - d' > 1: pow base (d - d') = base * pow base (d - d' - 1)
    
    if d - d' = 1 then (
      pow_succ base 0;
      pow_zero base;
      assert (pow base 1 == base)
    ) else (
      pow_succ base (d - d' - 1);
      assert (pow base (d - d') == base * pow base (d - d' - 1));
      modulo_modulo_lemma (k / pow base d') base (pow base (d - d' - 1))
    )

// Helper: digit_sum doesn't depend on the bigD parameter (it's just for specification)
let rec lemma_digit_sum_bigD_irrelevant (k bigD1 bigD2 base d: nat)
  : Lemma (requires d <= bigD1 /\ d <= bigD2)
          (ensures digit_sum k bigD1 base d == digit_sum k bigD2 base d)
          (decreases d)
  = if d = 0 || base = 0 then ()
    else lemma_digit_sum_bigD_irrelevant k bigD1 bigD2 base (d - 1)

// Helper: if digits match, digit_sums match
let rec lemma_digit_sum_extensional (k1 k2 bigD base d: nat)
  : Lemma (requires d <= bigD /\ 
                     (forall (i: nat). i < d ==> digit k1 i base == digit k2 i base))
          (ensures digit_sum k1 bigD base d == digit_sum k2 bigD base d)
          (decreases d)
  = if d = 0 || base = 0 then ()
    else (
      lemma_digit_sum_extensional k1 k2 bigD base (d - 1);
      assert (digit k1 (d - 1) base == digit k2 (d - 1) base)
    )

let rec digit_decomposition (k bigD base: nat)
  : Lemma (requires bigD > 0 /\ base >= 2 /\ k < pow base bigD)
          (ensures k == digit_sum k bigD base bigD)
          (decreases bigD)
  = if bigD = 1 then (
      pow_zero base;
      pow_positive base 0;
      assert (k < base);
      small_modulo_lemma_1 k base
    ) else (
      // k = digit(k, bigD-1) * base^(bigD-1) + (k mod base^(bigD-1))
      // The lower part k mod base^(bigD-1) can be decomposed recursively
      pow_positive base (bigD - 1);
      let lower_part = k % pow base (bigD - 1) in
      let high_digit = digit k (bigD - 1) base in
      
      // First establish: k = (k / base^(bigD-1)) * base^(bigD-1) + lower_part
      lemma_div_mod k (pow base (bigD - 1));
      assert (k == (k / pow base (bigD - 1)) * pow base (bigD - 1) + lower_part);
      
      // high_digit = (k / base^(bigD-1)) mod base
      pow_succ base (bigD - 1);
      assert (pow base bigD == base * pow base (bigD - 1));
      
      // k < base^bigD means k / base^(bigD-1) < base
      lemma_div_pow_bound k base (pow base (bigD - 1));
      
      // So high_digit = k / base^(bigD-1)
      small_modulo_lemma_1 (k / pow base (bigD - 1)) base;
      assert (high_digit == k / pow base (bigD - 1));
      
      // Now prove lower_part < base^(bigD-1)
      modulo_range_lemma k (pow base (bigD - 1));
      assert (lower_part < pow base (bigD - 1));
      
      // Apply induction to lower_part
      digit_decomposition lower_part (bigD - 1) base;
      
      // Need to show: digits of lower_part equal lower digits of k
      // Use lemma_digit_mod for each digit position
      let aux (d: nat) : Lemma (requires d < bigD - 1)
                               (ensures digit lower_part d base == digit k d base)
        = pow_positive base (bigD - 1);
          pow_positive base d;
          lemma_digit_mod k (bigD - 1) base d
      in
      Classical.forall_intro (Classical.move_requires aux);
      
      // Therefore digit_sum k bigD base (bigD-1) == digit_sum lower_part (bigD-1) base (bigD-1)
      // Note: this is comparing digit_sum with different second parameter
      // digit_sum k bigD base (bigD-1) uses k with bigD as the nominal bound
      // digit_sum lower_part (bigD-1) base (bigD-1) uses lower_part with (bigD-1) as the bound
      // But they compute the same value because the digits 0..(bigD-2) are the same
      lemma_digit_sum_extensional k lower_part (bigD - 1) base (bigD - 1);
      assert (digit_sum k (bigD - 1) base (bigD - 1) == digit_sum lower_part (bigD - 1) base (bigD - 1));
      
      // But wait, I need digit_sum k bigD base (bigD-1), not digit_sum k (bigD-1) base (bigD-1)
      // Let me check if these are actually the same
      // digit_sum k bigD base d only depends on digits 0..(d-1) of k, not on bigD
      // So digit_sum k bigD base (bigD-1) == digit_sum k (bigD-1) base (bigD-1)
      // This should be automatic from the definition
      
      // And digit_sum lower_part (bigD-1) base (bigD-1) == lower_part (by induction hypothesis)
      assert (lower_part == digit_sum lower_part (bigD - 1) base (bigD - 1));
      
      // Now connect to the overall goal
      // digit_sum k bigD base bigD 
      //  = digit k (bigD-1) base * pow base (bigD-1) + digit_sum k bigD base (bigD-1)  (by def)
      assert (digit_sum k bigD base bigD == 
              digit k (bigD - 1) base * pow base (bigD - 1) + digit_sum k bigD base (bigD - 1));
      
      //  = high_digit * pow base (bigD-1) + digit_sum k bigD base (bigD-1)  (since high_digit = digit k (bigD-1) base)
      assert (high_digit == digit k (bigD - 1) base);
      
      // Show that digit_sum k bigD base (bigD-1) == digit_sum k (bigD-1) base (bigD-1)
      lemma_digit_sum_bigD_irrelevant k bigD (bigD - 1) base (bigD - 1);
      
      //  = high_digit * pow base (bigD-1) + digit_sum lower_part (bigD-1) base (bigD-1)  (by digit equality)
      assert (digit_sum k bigD base (bigD - 1) == digit_sum lower_part (bigD - 1) base (bigD - 1));
      
      //  = high_digit * pow base (bigD-1) + lower_part  (by IH)
      //  = (k / pow base (bigD-1)) * pow base (bigD-1) + k % pow base (bigD-1)  (by definitions)
      //  = k (by division lemma which we already applied)
      ()
    )

(* ========== Sorted predicates ========== *)

// Sorted by full value
let rec sorted (s: seq nat) : Tot prop (decreases (length s)) =
  length s <= 1 \/ (index s 0 <= index s 1 /\ sorted (tail s))

// Sorted by d-th digit only
let rec sorted_by_digit (s: seq nat) (d base: nat) : Tot prop (decreases (length s)) =
  base > 0 /\ (
    length s <= 1 \/ 
    (digit (index s 0) d base <= digit (index s 1) d base /\ 
     sorted_by_digit (tail s) d base))

(* ========== Permutation ========== *)

// Count occurrences of x in sequence
let rec count (s: seq nat) (x: nat) : Tot nat (decreases (length s)) =
  if length s = 0 then 0
  else (if index s 0 = x then 1 else 0) + count (tail s) x

// s_out is a permutation of s_in
let permutation (s_in s_out: seq nat) : prop =
  length s_in == length s_out /\
  (forall (x: nat). count s_in x == count s_out x)

(* ========== Stable sorting ========== *)

// Stable sort by key function: maintains relative order for equal keys
// Simplified definition focusing on the key properties
let is_stable_sort_by (s_in s_out: seq nat) (key: nat -> nat) : prop =
  permutation s_in s_out /\
  // Sorted by key
  (forall (i j: nat). i < j /\ j < length s_out ==> 
    key (index s_out i) <= key (index s_out j)) /\
  // Stability: for elements with equal keys, maintain relative order
  (forall (i1 i2 j1 j2: nat).
    i1 < length s_in /\ i2 < length s_in /\
    j1 < length s_out /\ j2 < length s_out /\
    index s_in i1 == index s_out j1 /\
    index s_in i2 == index s_out j2 /\
    i1 < i2 /\
    key (index s_in i1) == key (index s_in i2) ==>
    j1 < j2)

// Stable sort by digit d
let is_stable_sort_by_digit (s_in s_out: seq nat) (d base: nat) : prop =
  base > 0 /\ is_stable_sort_by s_in s_out (fun k -> digit k d base)

(* ========== Radix sort correctness ========== *)

// After sorting by digit d, elements are sorted on digits 0..d
// Uses lexicographic ordering from the most significant digit:
// For every pair i < j in the sequence, either there exists a digit d0 <= max_d
// where s[i] has a strictly smaller digit and all MORE SIGNIFICANT digits (d' > d0)
// agree, or all digits 0..max_d are equal.
// This is the invariant maintained by radix sort (LSD to MSD):
// after sorting by digit max_d, the most significant differing digit determines order.
let sorted_up_to_digit (s: seq nat) (max_d base: nat) : prop =
  base > 0 /\
  (forall (i j: nat). {:pattern (index s i); (index s j)}
    i < j /\ j < length s ==>
    // Either the most significant differing digit favors s[i]
    ((exists (d0: nat). d0 <= max_d /\
       digit (index s i) d0 base < digit (index s j) d0 base /\
       // All more significant digits are equal
       (forall (d': nat). d0 < d' /\ d' <= max_d ==> digit (index s i) d' base == digit (index s j) d' base)) \/
     // Or all digits up to max_d are equal
     (forall (d: nat). d <= max_d ==> digit (index s i) d base == digit (index s j) d base)))

// Key lemma: stability preserves sorted_up_to_digit property
// This is the heart of CLRS Lemma 8.3
let lemma_stable_sort_preserves_order
  (s_in s_out: seq nat)
  (d base: nat)
  : Lemma (requires base >= 2 /\
                    is_stable_sort_by_digit s_in s_out d base /\
                    (d == 0 \/ (d > 0 /\ sorted_up_to_digit s_in (d - 1) base)))
          (ensures sorted_up_to_digit s_out d base)
  = admit() // Core stability reasoning - requires detailed proof

// Main theorem: d passes of stable digit sort yields sorted array
let radix_sort_correctness
  (s0: seq nat)
  (steps: list (seq nat))
  (bigD base: nat)
  : Lemma (requires 
            bigD > 0 /\
            base >= 2 /\
            // Initial sequence has values bounded by base^bigD
            (forall (i: nat). i < length s0 ==> index s0 i < pow base bigD) /\
            // We have bigD intermediate sequences
            List.Tot.length steps == bigD /\
            // Each step is a stable sort by the corresponding digit
            (forall (step_num: nat). step_num < bigD ==>
              (let s_in = (if step_num = 0 then s0 else List.Tot.index steps (step_num - 1)) in
               let s_out = List.Tot.index steps step_num in
               is_stable_sort_by_digit s_in s_out step_num base)))
          (ensures 
            (let final = List.Tot.index steps (bigD - 1) in
             permutation s0 final /\
             sorted final))
          (decreases bigD)
  = admit() // Induction on bigD using lemma_stable_sort_preserves_order

(* ========== Digit comparison implies value comparison ========== *)

// If all digits are equal, values are equal
let digits_equal_implies_equal (k1 k2 bigD base: nat)
  : Lemma (requires bigD > 0 /\
                    base >= 2 /\
                    k1 < pow base bigD /\
                    k2 < pow base bigD /\
                    (forall (d: nat). d < bigD ==> digit k1 d base == digit k2 d base))
          (ensures k1 == k2)
  = digit_decomposition k1 bigD base;
    digit_decomposition k2 bigD base;
    lemma_digit_sum_extensional k1 k2 bigD base bigD

// digit_sum is monotone when all digits are <=
private let rec lemma_digit_sum_le (k1 k2 bigD base d: nat)
  : Lemma (requires d <= bigD /\ base >= 2 /\
    (forall (i:nat). i < d ==> digit k1 i base <= digit k2 i base))
    (ensures digit_sum k1 bigD base d <= digit_sum k2 bigD base d)
    (decreases d)
  = if d = 0 || base = 0 then ()
    else begin
      lemma_digit_sum_le k1 k2 bigD base (d - 1);
      pow_positive base (d - 1);
      lemma_mult_le_right (pow base (d - 1)) (digit k1 (d - 1) base) (digit k2 (d - 1) base)
    end

// Upper bound: digit_sum k bigD base d < pow base d
// Each digit is < base, so sum < base^d
private let rec lemma_digit_sum_bound (k bigD base d: nat)
  : Lemma (requires d <= bigD /\ base >= 2)
          (ensures digit_sum k bigD base d < pow base d)
          (decreases d)
  = if d = 0 || base = 0 then (
      pow_positive base 0;
      ()
    ) else (
      lemma_digit_sum_bound k bigD base (d - 1);
      digit_bound k (d - 1) base;
      pow_positive base (d - 1);
      // digit k (d-1) base < base
      // digit k (d-1) base * pow base (d-1) <= (base - 1) * pow base (d-1)
      lemma_mult_le_right (pow base (d - 1)) (digit k (d - 1) base) (base - 1);
      // (base - 1) * pow base (d-1) + pow base (d-1) = base * pow base (d-1) = pow base d
      pow_succ base (d - 1);
      ()
    )

// digit_sum splits: digit_sum k bigD base d = digit(k,d-1)*base^(d-1) + digit_sum k bigD base (d-1)
// (This is just the definition, but useful to state)

// Key helper: if digits from d0+1 to d-1 are equal, then
// digit_sum k1 bigD base d - digit_sum k1 bigD base (d0+1) == 
// digit_sum k2 bigD base d - digit_sum k2 bigD base (d0+1)
private let rec lemma_digit_sum_equal_upper (k1 k2 bigD base d d0: nat)
  : Lemma (requires d0 < d /\ d <= bigD /\ base >= 2 /\
                    (forall (i: nat). d0 < i /\ i < d ==> digit k1 i base == digit k2 i base))
          (ensures digit_sum k1 bigD base d - digit_sum k1 bigD base (d0 + 1) ==
                   digit_sum k2 bigD base d - digit_sum k2 bigD base (d0 + 1))
          (decreases d)
  = if d = d0 + 1 then ()
    else (
      // digit_sum k bigD base d = digit(k,d-1)*base^(d-1) + digit_sum k bigD base (d-1)
      // digit(k1, d-1) == digit(k2, d-1) since d-1 > d0
      assert (digit k1 (d - 1) base == digit k2 (d - 1) base);
      lemma_digit_sum_equal_upper k1 k2 bigD base (d - 1) d0
    )

// Helper for the MSD proof: digit_sum ordering when exists a separating digit
#push-options "--z3rlimit 30 --fuel 2"
private let rec lemma_digit_sum_msd_le (x y bigD base d d0: nat)
  : Lemma (requires base >= 2 /\ d0 < d /\ d <= bigD /\
                    digit x d0 base < digit y d0 base /\
                    (forall (d': nat). d0 < d' /\ d' < d ==> digit x d' base == digit y d' base))
          (ensures digit_sum x bigD base d <= digit_sum y bigD base d)
          (decreases d)
  = if d = d0 + 1 then (
      // digit_sum k bigD base (d0+1) = digit(k, d0) * base^d0 + digit_sum k bigD base d0
      pow_positive base d0;
      lemma_digit_sum_bound x bigD base d0;
      // digit(x,d0) < digit(y,d0), so digit(x,d0) <= digit(y,d0) - 1
      // digit(x,d0) * base^d0 + digit_sum x bigD base d0
      //   <= (digit(y,d0) - 1) * base^d0 + (base^d0 - 1)
      //   = digit(y,d0) * base^d0 - 1
      //   <= digit(y,d0) * base^d0 + digit_sum y bigD base d0
      lemma_mult_le_right (pow base d0) (digit x d0 base) (digit y d0 base - 1);
      ()
    ) else (
      // d > d0 + 1, so d - 1 > d0
      // digit_sum k bigD base d = digit(k, d-1) * base^(d-1) + digit_sum k bigD base (d-1)
      // digit(x, d-1) == digit(y, d-1) since d-1 > d0
      assert (digit x (d - 1) base == digit y (d - 1) base);
      lemma_digit_sum_msd_le x y bigD base (d - 1) d0;
      ()
    )
#pop-options

// Main lemma: MSD lexicographic ordering implies value ordering
#push-options "--z3rlimit 20"
let lemma_digits_le_implies_value_le (x y bigD base: nat)
  : Lemma (requires bigD > 0 /\
                    base >= 2 /\
                    x < pow base bigD /\
                    y < pow base bigD /\
                    // Lexicographic: the most significant differing digit favors x, or all equal
                    ((exists (d0: nat). d0 < bigD /\ digit x d0 base < digit y d0 base /\
                      (forall (d': nat). d0 < d' /\ d' < bigD ==> digit x d' base == digit y d' base)) \/
                     (forall (d: nat). d < bigD ==> digit x d base == digit y d base)))
          (ensures x <= y)
  = digit_decomposition x bigD base;
    digit_decomposition y bigD base;
    match FStar.StrongExcludedMiddle.strong_excluded_middle
      (forall (d: nat). d < bigD ==> digit x d base == digit y d base) with
    | true -> lemma_digit_sum_extensional x y bigD base bigD
    | false ->
      assert (exists (d0: nat). d0 < bigD /\ digit x d0 base < digit y d0 base /\
              (forall (d': nat). d0 < d' /\ d' < bigD ==> digit x d' base == digit y d' base));
      eliminate exists (d0: nat).
        d0 < bigD /\ digit x d0 base < digit y d0 base /\
        (forall (d': nat). d0 < d' /\ d' < bigD ==> digit x d' base == digit y d' base)
      returns digit_sum x bigD base bigD <= digit_sum y bigD base bigD
      with _. lemma_digit_sum_msd_le x y bigD base bigD d0
#pop-options

// Helper: if all adjacent pairs are ordered, the sequence is sorted
private let rec lemma_pairwise_implies_sorted (s: seq nat)
  : Lemma
    (requires forall (i: nat). i + 1 < length s ==> index s i <= index s (i + 1))
    (ensures sorted s)
    (decreases length s)
  = if length s <= 1 then ()
    else begin
      let t = tail s in
      let aux (i: nat{i + 1 < length t}) : Lemma (index t i <= index t (i + 1))
        = assert (index t i == index s (i + 1));
          assert (index t (i + 1) == index s (i + 2))
      in
      Classical.forall_intro (Classical.move_requires aux);
      lemma_pairwise_implies_sorted t
    end

// Sorted up to all digits implies fully sorted
let lemma_sorted_all_digits_is_sorted
  (s: seq nat) (bigD base: nat)
  : Lemma (requires bigD > 0 /\
                    base >= 2 /\
                    (forall (i: nat). i < length s ==> index s i < pow base bigD) /\
                    sorted_up_to_digit s (bigD - 1) base)
          (ensures sorted s)
  = // sorted_up_to_digit gives: for every pair i < j, either
    //   (a) exists d0 where digit(s[i], d0) < digit(s[j], d0) with lower digits equal, or
    //   (b) all digits equal
    // In both cases, lemma_digits_le_implies_value_le gives s[i] <= s[j]
    let aux (i: nat{i + 1 < length s}) : Lemma (index s i <= index s (i + 1))
      = let x = index s i in
        let y = index s (i + 1) in
        // sorted_up_to_digit s (bigD-1) base gives the disjunction for pair (i, i+1)
        assert (index s i == x);  // trigger pattern
        assert (index s (i + 1) == y);  // trigger pattern
        lemma_digits_le_implies_value_le x y bigD base
    in
    Classical.forall_intro (Classical.move_requires aux);
    lemma_pairwise_implies_sorted s

(* ========== Final correctness statement ========== *)

// Complete radix sort correctness: combines all the pieces
let radix_sort_correct
  (s0 s_final: seq nat)
  (bigD base: nat)
  (steps: list (seq nat))
  : Lemma (requires
            bigD > 0 /\
            base >= 2 /\
            (forall (i: nat). i < length s0 ==> index s0 i < pow base bigD) /\
            List.Tot.length steps == bigD /\
            (forall (step_num: nat). step_num < bigD ==>
              (let s_in = (if step_num = 0 then s0 else List.Tot.index steps (step_num - 1)) in
               let s_out = List.Tot.index steps step_num in
               is_stable_sort_by_digit s_in s_out step_num base)) /\
            s_final == List.Tot.index steps (bigD - 1))
          (ensures
            permutation s0 s_final /\
            sorted s_final)
  = radix_sort_correctness s0 steps bigD base
    // The sortedness follows from sorted_up_to_digit for all digits
