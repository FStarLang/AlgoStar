(*
   Radix Sort Specification - Multi-digit correctness theory
   
   This module provides the mathematical foundation for CLRS Radix Sort
   (Section 8.3) with d digits in base b.
   
   Key results:
   1. Digit extraction and decomposition (any k can be written as sum of digits)
   2. Stable sorting preserves relative order for equal keys
   3. CLRS Lemma 8.3: After d passes of stable sort (by digit 0, 1, ..., d-1),
      the array is sorted by the full key value.
   
   NO admits. All proofs are complete.
*)

module CLRS.Ch08.RadixSort.Spec

open FStar.Seq
open FStar.Math.Lemmas
open FStar.Classical
open FStar.IndefiniteDescription
open CLRS.Ch08.RadixSort.Base
module Seq = FStar.Seq

(* ========== Digit helpers (Spec-specific) ========== *)

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

(* ========== Stable sorting ========== *)

//SNIPPET_START: is_stable_sort_by
let is_stable_sort_by (s_in s_out: seq nat) (key: nat -> nat) : prop =
  permutation s_in s_out /\
  (forall (i j: nat). i < j /\ j < length s_out ==> 
    key (index s_out i) <= key (index s_out j)) /\
  (forall (i1 i2 j1 j2: nat).
    i1 < length s_in /\ i2 < length s_in /\
    j1 < length s_out /\ j2 < length s_out /\
    index s_in i1 == index s_out j1 /\
    index s_in i2 == index s_out j2 /\
    i1 < i2 /\
    key (index s_in i1) == key (index s_in i2) ==>
    j1 < j2)
//SNIPPET_END: is_stable_sort_by

// Stable sort by digit d — inlined to avoid lambda beta-reduction issues in SMT
[@@"opaque_to_smt"]
let is_stable_sort_by_digit (s_in s_out: seq nat) (d base: nat) : prop =
  base > 0 /\
  permutation s_in s_out /\
  (forall (i j: nat). {:pattern (index s_out i); (index s_out j)}
    i < j /\ j < length s_out ==> 
    digit (index s_out i) d base <= digit (index s_out j) d base) /\
  (forall (i1 i2 j1 j2: nat). {:pattern (index s_in i1); (index s_in i2); (index s_out j1); (index s_out j2)}
    i1 < length s_in /\ i2 < length s_in /\
    j1 < length s_out /\ j2 < length s_out /\
    index s_in i1 == index s_out j1 /\
    index s_in i2 == index s_out j2 /\
    i1 < i2 /\
    index s_in i1 <> index s_in i2 /\
    digit (index s_in i1) d base == digit (index s_in i2) d base ==>
    j1 < j2)

// Helper: unpack sorted property from is_stable_sort_by_digit
let unpack_sorted (s_in s_out: seq nat) (d base: nat) (i j: nat)
  : Lemma (requires is_stable_sort_by_digit s_in s_out d base /\
                    i < j /\ j < length s_out)
          (ensures digit (index s_out i) d base <= digit (index s_out j) d base)
  = reveal_opaque (`%is_stable_sort_by_digit) (is_stable_sort_by_digit s_in s_out d base)

// Helper: unpack stability from is_stable_sort_by_digit
let unpack_stability (s_in s_out: seq nat) (d base: nat) (i1 i2 j1 j2: nat)
  : Lemma (requires is_stable_sort_by_digit s_in s_out d base /\
                    i1 < length s_in /\ i2 < length s_in /\
                    j1 < length s_out /\ j2 < length s_out /\
                    index s_in i1 == index s_out j1 /\
                    index s_in i2 == index s_out j2 /\
                    i1 < i2 /\
                    index s_in i1 <> index s_in i2 /\
                    digit (index s_in i1) d base == digit (index s_in i2) d base)
          (ensures j1 < j2)
  = reveal_opaque (`%is_stable_sort_by_digit) (is_stable_sort_by_digit s_in s_out d base)

// Helper: unpack permutation from is_stable_sort_by_digit
let unpack_perm (s_in s_out: seq nat) (d base: nat)
  : Lemma (requires is_stable_sort_by_digit s_in s_out d base)
          (ensures permutation s_in s_out)
  = reveal_opaque (`%is_stable_sort_by_digit) (is_stable_sort_by_digit s_in s_out d base)

(* ========== Radix sort correctness ========== *)

// After sorting by digit d, elements are sorted on digits 0..d
// Uses lexicographic ordering from the most significant digit:
// For every pair i < j in the sequence, either there exists a digit d0 <= max_d
// where s[i] has a strictly smaller digit and all MORE SIGNIFICANT digits (d' > d0)
// agree, or all digits 0..max_d are equal.
// This is the invariant maintained by radix sort (LSD to MSD):
// after sorting by digit max_d, the most significant differing digit determines order.
[@@"opaque_to_smt"]
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

// Helper: given concrete witness positions, prove a < b from stability
#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let order_witnesses (s_in s_out: seq nat) (d base: nat) (a b i j: nat)
  : Lemma 
    (requires is_stable_sort_by_digit s_in s_out d base /\
              a < length s_in /\ b < length s_in /\
              i < j /\ j < length s_out /\
              index s_in a == index s_out i /\ index s_in b == index s_out j /\
              digit (index s_out i) d base == digit (index s_out j) d base /\
              index s_out i <> index s_out j)
    (ensures a < b)
  = reveal_opaque (`%is_stable_sort_by_digit) (is_stable_sort_by_digit s_in s_out d base)
#pop-options

// Helper: find ordered input witnesses for distinct output elements with same digit.
// Uses order_witnesses to keep reveal_opaque isolated from count_pos skolemization.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let find_input_witnesses (s_in s_out: seq nat) (d base: nat) (i j: nat)
  : Lemma 
    (requires base >= 2 /\ is_stable_sort_by_digit s_in s_out d base /\
              i < j /\ j < length s_out /\
              digit (index s_out i) d base == digit (index s_out j) d base /\
              index s_out i <> index s_out j)
    (ensures exists (a b: nat). a < b /\ b < length s_in /\
              index s_in a == index s_out i /\ index s_in b == index s_out j)
  = let v = index s_out i in
    let w = index s_out j in
    unpack_perm s_in s_out d base;
    element_appears_means_count_positive s_out i;
    count_positive_means_appears s_in v;
    let a = indefinite_description_ghost nat (fun a -> a < length s_in /\ index s_in a == v) in
    element_appears_means_count_positive s_out j;
    count_positive_means_appears s_in w;
    let b = indefinite_description_ghost nat (fun b -> b < length s_in /\ index s_in b == w) in
    order_witnesses s_in s_out d base a b i j
#pop-options

// Extract ordering for VALUES from sorted_up_to_digit (no index terms in postcondition)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let sorted_up_to_values (s: seq nat) (max_d base: nat) (v w: nat) (a b: nat)
  : Lemma 
    (requires sorted_up_to_digit s max_d base /\
              a < b /\ b < length s /\ index s a == v /\ index s b == w)
    (ensures ((exists (d0: nat). d0 <= max_d /\
                digit v d0 base < digit w d0 base /\
                (forall (d': nat). d0 < d' /\ d' <= max_d ==> digit v d' base == digit w d' base)) \/
              (forall (d: nat). d <= max_d ==> digit v d base == digit w d base)))
  = reveal_opaque (`%sorted_up_to_digit) (sorted_up_to_digit s max_d base)
#pop-options

// Establish sorted_up_to_digit from universally quantified property
let sorted_up_to_intro (s: seq nat) (max_d base: nat)
  : Lemma 
    (requires base > 0 /\
              (forall (i j: nat). {:pattern (index s i); (index s j)}
                i < j /\ j < length s ==>
                ((exists (d0: nat). d0 <= max_d /\
                    digit (index s i) d0 base < digit (index s j) d0 base /\
                    (forall (d': nat). d0 < d' /\ d' <= max_d ==>
                      digit (index s i) d' base == digit (index s j) d' base)) \/
                 (forall (d: nat). d <= max_d ==>
                    digit (index s i) d base == digit (index s j) d base))))
    (ensures sorted_up_to_digit s max_d base)
  = reveal_opaque (`%sorted_up_to_digit) (sorted_up_to_digit s max_d base)

// Combine find_input_witnesses + sorted_up_to_values + extend ordering from d-1 to d
#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
let get_lower_ordering (s_in s_out: seq nat) (d base: nat) (i j: nat)
  : Lemma 
    (requires base >= 2 /\ is_stable_sort_by_digit s_in s_out d base /\
              d > 0 /\ sorted_up_to_digit s_in (d - 1) base /\
              i < j /\ j < length s_out /\
              digit (index s_out i) d base == digit (index s_out j) d base /\
              index s_out i <> index s_out j)
    (ensures (exists (d0: nat). d0 <= d /\
                digit (index s_out i) d0 base < digit (index s_out j) d0 base /\
                (forall (d': nat). d0 < d' /\ d' <= d ==>
                  digit (index s_out i) d' base == digit (index s_out j) d' base)) \/
             (forall (dd: nat). dd <= d ==>
                digit (index s_out i) dd base == digit (index s_out j) dd base))
  = let v = index s_out i in
    let w = index s_out j in
    find_input_witnesses s_in s_out d base i j;
    let a = indefinite_description_ghost nat
      (fun a -> exists (b: nat). a < b /\ b < length s_in /\
        index s_in a == v /\ index s_in b == w) in
    let b = indefinite_description_ghost nat
      (fun b -> a < b /\ b < length s_in /\
        index s_in a == v /\ index s_in b == w) in
    sorted_up_to_values s_in (d - 1) base v w a b;
    match FStar.IndefiniteDescription.strong_excluded_middle
      (exists (d0: nat). d0 <= d - 1 /\
        digit v d0 base < digit w d0 base /\
        (forall (d': nat). d0 < d' /\ d' <= d - 1 ==> digit v d' base == digit w d' base)) with
    | true ->
      let d0 = indefinite_description_ghost nat
        (fun d0 -> d0 <= d - 1 /\ digit v d0 base < digit w d0 base /\
          (forall (d': nat). d0 < d' /\ d' <= d - 1 ==> digit v d' base == digit w d' base)) in
      let aux (d': nat) : Lemma (requires d0 < d' /\ d' <= d) (ensures digit v d' base == digit w d' base) =
        if d' = d then () else ()
      in forall_intro (move_requires aux)
    | false ->
      let aux (dd: nat) : Lemma (requires dd <= d) (ensures digit v dd base == digit w dd base) =
        if dd = d then () else ()
      in forall_intro (move_requires aux)
#pop-options

// Key lemma: stability preserves sorted_up_to_digit property
// This is the heart of CLRS Lemma 8.3
#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let lemma_stable_sort_preserves_order
  (s_in s_out: seq nat)
  (d base: nat)
  : Lemma (requires base >= 2 /\
                    is_stable_sort_by_digit s_in s_out d base /\
                    (d == 0 \/ (d > 0 /\ sorted_up_to_digit s_in (d - 1) base)))
          (ensures sorted_up_to_digit s_out d base)
  = let aux (i j: nat) : Lemma
      (requires i < j /\ j < length s_out)
      (ensures (exists (d0: nat). d0 <= d /\
                  digit (index s_out i) d0 base < digit (index s_out j) d0 base /\
                  (forall (d': nat). d0 < d' /\ d' <= d ==>
                    digit (index s_out i) d' base == digit (index s_out j) d' base)) \/
               (forall (dd: nat). dd <= d ==>
                  digit (index s_out i) dd base == digit (index s_out j) dd base))
      [SMTPat (index s_out i); SMTPat (index s_out j)]
      = let v = index s_out i in
        let w = index s_out j in
        unpack_sorted s_in s_out d base i j;
        if digit v d base < digit w d base then ()
        else if v = w then (
          let aux2 (dd: nat) : Lemma (requires dd <= d) (ensures digit v dd base == digit w dd base) = ()
          in forall_intro (move_requires aux2)
        ) else (
          assert (digit v d base == digit w d base);
          if d = 0 then (
            let aux2 (dd: nat) : Lemma (requires dd <= 0) (ensures digit v dd base == digit w dd base) = ()
            in forall_intro (move_requires aux2)
          ) else
            get_lower_ordering s_in s_out d base i j
        )
    in
    sorted_up_to_intro s_out d base
#pop-options

// Helper: extract the stable sort property for a specific step
let extract_step_property
  (s0: seq nat) (steps: list (seq nat)) (step_num bigD base: nat)
  : Lemma (requires
            step_num < bigD /\
            bigD <= List.Tot.length steps /\
            (forall (i: nat). i < bigD ==>
              (let s_in = (if i = 0 then s0 else List.Tot.index steps (i - 1)) in
               let s_out = List.Tot.index steps i in
               is_stable_sort_by_digit s_in s_out i base)))
          (ensures
            (let s_in = (if step_num = 0 then s0 else List.Tot.index steps (step_num - 1)) in
             let s_out = List.Tot.index steps step_num in
             is_stable_sort_by_digit s_in s_out step_num base))
  = ()

// Inductive invariant: after d passes, sorted_up_to_digit on digits 0..d-1
let rec radix_invariant
  (s0: seq nat) (steps: list (seq nat)) (d bigD base: nat)
  : Lemma (requires
            base >= 2 /\
            d <= bigD /\
            bigD <= List.Tot.length steps /\
            (forall (step_num: nat). step_num < bigD ==>
              (let s_in = (if step_num = 0 then s0 else List.Tot.index steps (step_num - 1)) in
               let s_out = List.Tot.index steps step_num in
               is_stable_sort_by_digit s_in s_out step_num base)))
          (ensures d = 0 \/
                   (d > 0 /\ sorted_up_to_digit (List.Tot.index steps (d - 1)) (d - 1) base))
          (decreases d)
  = if d = 0 then ()
    else if d = 1 then (
      extract_step_property s0 steps 0 bigD base;
      lemma_stable_sort_preserves_order s0 (List.Tot.index steps 0) 0 base
    ) else (
      radix_invariant s0 steps (d - 1) bigD base;
      extract_step_property s0 steps (d - 1) bigD base;
      lemma_stable_sort_preserves_order
        (List.Tot.index steps (d - 2)) (List.Tot.index steps (d - 1)) (d - 1) base
    )

// Permutation chain: after d passes, result is a permutation of input
let rec perm_chain
  (s0: seq nat) (steps: list (seq nat)) (d bigD base: nat)
  : Lemma (requires
            base >= 2 /\
            d <= bigD /\
            bigD <= List.Tot.length steps /\
            (forall (step_num: nat). step_num < bigD ==>
              (let s_in = (if step_num = 0 then s0 else List.Tot.index steps (step_num - 1)) in
               let s_out = List.Tot.index steps step_num in
               is_stable_sort_by_digit s_in s_out step_num base)))
          (ensures d = 0 \/ permutation s0 (List.Tot.index steps (d - 1)))
          (decreases d)
  = if d = 0 then ()
    else if d = 1 then (
      extract_step_property s0 steps 0 bigD base;
      unpack_perm s0 (List.Tot.index steps 0) 0 base
    ) else (
      perm_chain s0 steps (d - 1) bigD base;
      extract_step_property s0 steps (d - 1) bigD base;
      unpack_perm (List.Tot.index steps (d - 2)) (List.Tot.index steps (d - 1)) (d - 1) base;
      permutation_transitive s0 (List.Tot.index steps (d - 2)) (List.Tot.index steps (d - 1))
    )


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
    match FStar.IndefiniteDescription.strong_excluded_middle
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
  = let aux (i: nat{i + 1 < length s}) : Lemma (index s i <= index s (i + 1))
      = reveal_opaque (`%sorted_up_to_digit) (sorted_up_to_digit s (bigD - 1) base);
        lemma_digits_le_implies_value_le (index s i) (index s (i + 1)) bigD base
    in
    Classical.forall_intro (Classical.move_requires aux);
    lemma_pairwise_implies_sorted s

(* ========== Final correctness statement ========== *)

// Main theorem: d passes of stable digit sort yields sorted array
let radix_sort_correctness
  (s0: seq nat)
  (steps: list (seq nat))
  (bigD base: nat)
  : Lemma (requires 
            bigD > 0 /\
            base >= 2 /\
            (forall (i: nat). i < length s0 ==> index s0 i < pow base bigD) /\
            List.Tot.length steps == bigD /\
            (forall (step_num: nat). step_num < bigD ==>
              (let s_in = (if step_num = 0 then s0 else List.Tot.index steps (step_num - 1)) in
               let s_out = List.Tot.index steps step_num in
               is_stable_sort_by_digit s_in s_out step_num base)))
          (ensures 
            (let final = List.Tot.index steps (bigD - 1) in
             permutation s0 final /\
             sorted final))
          (decreases bigD)
  = let final = List.Tot.index steps (bigD - 1) in
    radix_invariant s0 steps bigD bigD base;
    assert (sorted_up_to_digit final (bigD - 1) base);
    perm_chain s0 steps bigD bigD base;
    assert (permutation s0 final);
    permutation_preserves_bounds s0 final (pow base bigD);
    lemma_sorted_all_digits_is_sorted final bigD base

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
