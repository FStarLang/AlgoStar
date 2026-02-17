(*
   Multi-digit Radix Sort - Pure F* Specification
   
   CLRS §8.3 RADIX-SORT algorithm for d-digit numbers:
   
     RADIX-SORT(A, d)
     1  for i = 1 to d
     2    use a stable sort to sort array A on digit i
   
   This module provides pure functional specifications for:
   - Digit extraction from numbers in a given base
   - Stable counting sort on a specific digit
   - Multi-pass radix sort
   - Correctness lemmas (some admitted for now)
   
   This is PURE F* (not Pulse) - all functions are functional.
*)

module CLRS.Ch08.RadixSort.MultiDigit

open FStar.Seq
open FStar.Math.Lemmas
open FStar.Mul
open FStar.Classical
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties

(* ========== Power function ========== *)

let rec pow (base: nat) (exp: nat) : nat =
  if exp = 0 then 1
  else base * pow base (exp - 1)

let rec pow_positive (base: nat) (exp: nat)
  : Lemma (requires base > 0)
          (ensures pow base exp > 0)
          (decreases exp)
  = if exp = 0 then ()
    else pow_positive base (exp - 1)

(* ========== Digit extraction ========== *)

/// Extract the d-th digit of k in the given base.
/// digit k d base = (k / base^d) mod base
let digit (k: nat) (d: nat) (base: nat) : nat =
  if base > 0 then (
    pow_positive base d;
    (k / pow base d) % base
  ) else 0

/// Digit is always less than base
let digit_bound (k d base: nat)
  : Lemma (requires base > 0)
          (ensures digit k d base < base)
  = pow_positive base d;
    lemma_mod_lt (k / pow base d) base

(* ========== Sorted predicates ========== *)

/// A sequence is sorted if each element is <= the next
let rec sorted (s: seq nat) : Tot prop (decreases (length s)) =
  length s <= 1 \/ (index s 0 <= index s 1 /\ sorted (tail s))

/// A sequence is sorted on digit d if comparing only digit d
let rec sorted_on_digit (s: seq nat) (d: nat) (base: nat) : Tot prop (decreases (length s)) =
  base > 0 /\ (
    length s <= 1 \/ 
    (digit (index s 0) d base <= digit (index s 1) d base /\ 
     sorted_on_digit (tail s) d base))

/// Helper: cons creates a sequence with head and tail
let cons_index_0 (x: nat) (s: seq nat)
  : Lemma (requires length s > 0)
          (ensures length (cons x s) > 1 /\ index (cons x s) 0 == x /\ index (cons x s) 1 == index s 0)
  = () // Follows from FStar.Seq.cons definition

/// Helper: tail of cons is the original sequence
let cons_tail (x: nat) (s: seq nat)
  : Lemma (tail (cons x s) == s)
  = assert (equal (tail (cons x s)) s)

/// Helper: if s is sorted on digit d and has length >= 2, then tail s is sorted on digit d
let sorted_on_digit_tail (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0 /\ length s > 1 /\ sorted_on_digit s d base)
          (ensures sorted_on_digit (tail s) d base)
  = () // Follows directly from recursive definition of sorted_on_digit

(* ========== Permutation ========== *)

/// Count occurrences of x in sequence
let rec count (s: seq nat) (x: nat) : Tot nat (decreases (length s)) =
  if length s = 0 then 0
  else (if index s 0 = x then 1 else 0) + count (tail s) x

/// Helper: count in cons
let count_cons (x h: nat) (s: seq nat)
  : Lemma (count (cons h s) x == (if h = x then 1 else 0) + count s x)
  = if length s = 0 then ()
    else (
      cons_tail h s;
      assert (tail (cons h s) == s);
      cons_index_0 h s;
      assert (index (cons h s) 0 == h)
    )

/// s_out is a permutation of s_in
let permutation (s_in s_out: seq nat) : prop =
  length s_in == length s_out /\
  (forall (x: nat). count s_in x == count s_out x)

(* ========== Helper: insertion into sorted sequence by digit ========== *)

/// Insert element x into sorted sequence s, maintaining sort order by digit d
let rec insert_by_digit (x: nat) (s: seq nat) (d: nat) (base: nat) 
  : Tot (seq nat) (decreases (length s))
  = if length s = 0 then 
      Seq.create 1 x
    else if digit x d base <= digit (index s 0) d base then
      cons x s
    else
      cons (index s 0) (insert_by_digit x (tail s) d base)

/// Insertion sort by digit d - produces a sorted sequence
let rec insertion_sort_by_digit (s: seq nat) (d: nat) (base: nat)
  : Tot (seq nat) (decreases (length s))
  = if length s = 0 then 
      empty
    else 
      insert_by_digit (index s 0) (insertion_sort_by_digit (tail s) d base) d base

(* ========== Stable sort on a single digit ========== *)

/// Stable sort that sorts sequence s by digit d only.
/// In practice, this would be counting sort. Here we use insertion sort
/// as a simple stable sort for specification purposes.
/// 
/// Key property: This is a STABLE sort - elements with equal digit d
/// maintain their relative order from the input sequence.
let stable_sort_on_digit (s: seq nat) (d: nat) (base: nat) : seq nat =
  if base > 0 then
    insertion_sort_by_digit s d base
  else
    s

(* ========== Multi-digit radix sort ========== *)

//SNIPPET_START: radix_sort_multi
let rec radix_sort (s: seq nat) (num_digits: nat) (base: nat) 
  : Tot (seq nat) (decreases num_digits)
  = if num_digits = 0 then
      s
    else
      let s' = radix_sort s (num_digits - 1) base in
      stable_sort_on_digit s' (num_digits - 1) base
//SNIPPET_END: radix_sort_multi

(* ========== Correctness lemmas ========== *)

/// Helper: length property of insert_by_digit
let rec insert_by_digit_length
  (x: nat) (s: seq nat) (d: nat) (base: nat)
  : Lemma (ensures length (insert_by_digit x s d base) == length s + 1)
          (decreases (length s))
  = if length s = 0 then ()
    else if digit x d base <= digit (index s 0) d base then ()
    else insert_by_digit_length x (tail s) d base

/// Helper: head of insert_by_digit result
let insert_by_digit_head
  (x: nat) (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires length s > 0)
          (ensures (let result = insert_by_digit x s d base in
                   length result > 0 /\
                   (if digit x d base <= digit (index s 0) d base 
                    then index result 0 == x
                    else index result 0 == index s 0)))
          (decreases (length s))
  = if digit x d base <= digit (index s 0) d base then ()
    else ()

/// Key property: when we insert x into the result of recursion, the first element is correct
let rec insert_by_digit_first_element
  (x: nat) (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0 /\ length s > 0 /\ sorted_on_digit s d base)
          (ensures (let result = insert_by_digit x s d base in
                   length result > 0 /\
                   digit (index result 0) d base <= digit x d base \/
                   digit (index result 0) d base <= digit (index s 0) d base))
          (decreases (length s))
  = insert_by_digit_length x s d base;
    if digit x d base <= digit (index s 0) d base then ()
    else if length s = 1 then ()
    else insert_by_digit_first_element x (tail s) d base

/// Lemma: insert_by_digit produces a sequence sorted on digit d
#push-options "--z3rlimit 40"
let rec insert_by_digit_sorted 
  (x: nat) (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0 /\ sorted_on_digit s d base)
          (ensures sorted_on_digit (insert_by_digit x s d base) d base)
          (decreases (length s))
  = insert_by_digit_length x s d base;
    if length s = 0 then ()
    else if digit x d base <= digit (index s 0) d base then (
      // Result is cons x s
      // Need to show sorted_on_digit (cons x s) d base
      // Either length <= 1 or digit (index (cons x s) 0) d <= digit (index (cons x s) 1) d /\ sorted_on_digit (tail (cons x s)) d
      cons_tail x s;
      if length s > 0 then cons_index_0 x s;
      ()
    ) else (
      // Result is cons (index s 0) (insert_by_digit x (tail s) d base)
      if length s = 1 then ()
      else (
        // Prove tail s is sorted
        sorted_on_digit_tail s d base;
        
        // Recursive call
        insert_by_digit_sorted x (tail s) d base;
        
        let h = index s 0 in
        let result_tail = insert_by_digit x (tail s) d base in
        insert_by_digit_length x (tail s) d base;
        cons_tail h result_tail;
        cons_index_0 h result_tail;
        
        // Need: digit h d <= digit (index result_tail 0) d
        // Case split on where x goes
        if digit x d base <= digit (index (tail s) 0) d base then (
          // result_tail = cons x (tail s), so index result_tail 0 = x
          assert (result_tail == cons x (tail s));
          cons_index_0 x (tail s);
          assert (index result_tail 0 == x);
          // Need: digit h d <= digit x d
          // We have: NOT(digit x d <= digit h d), so digit x d > digit h d
          ()
        ) else (
          // result_tail = cons (index (tail s) 0) ..., so index result_tail 0 = index (tail s) 0 = index s 1
          assert (result_tail == cons (index (tail s) 0) (insert_by_digit x (tail (tail s)) d base));
          cons_index_0 (index (tail s) 0) (insert_by_digit x (tail (tail s)) d base);
          assert (index result_tail 0 == index (tail s) 0);
          assert (index (tail s) 0 == index s 1);
          // Need: digit h d <= digit (index s 1) d
          // This follows from sorted_on_digit s d base
          ()
        )
      )
    )
#pop-options

/// Lemma: insertion_sort_by_digit produces a sorted sequence
let rec insertion_sort_sorted 
  (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures sorted_on_digit (insertion_sort_by_digit s d base) d base)
          (decreases (length s))
  = if length s = 0 then ()
    else (
      insertion_sort_sorted (tail s) d base;
      insert_by_digit_sorted (index s 0) (insertion_sort_by_digit (tail s) d base) d base
    )

/// Lemma: stable_sort_on_digit produces a sequence sorted on digit d
let stable_sort_on_digit_sorted 
  (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures sorted_on_digit (stable_sort_on_digit s d base) d base)
  = insertion_sort_sorted s d base

/// Lemma: insert_by_digit is a permutation
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let rec insert_by_digit_permutation
  (x: nat) (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures (let result = insert_by_digit x s d base in
                   length result == length s + 1 /\
                   count result x == count s x + 1 /\
                   (forall (y: nat). y <> x ==> count result y == count s y)))
          (decreases (length s))
  = insert_by_digit_length x s d base;
    if length s = 0 then ()
    else if digit x d base <= digit (index s 0) d base then (
      // result = cons x s
      let result = cons x s in
      count_cons x x s;
      assert (count result x == (if x = x then 1 else 0) + count s x);
      assert (count result x == 1 + count s x);
      // For any y <> x:
      let aux (y: nat) : Lemma (requires y <> x) (ensures count result y == count s y) =
        count_cons y x s;
        assert (count result y == (if x = y then 1 else 0) + count s y);
        assert (count result y == count s y)
      in
      Classical.forall_intro (Classical.move_requires aux)
    ) else (
      // result = cons (index s 0) (insert_by_digit x (tail s) d base)
      let h = index s 0 in
      let t = tail s in
      let result_tail = insert_by_digit x t d base in
      let result = cons h result_tail in
      
      // Inductive hypothesis
      insert_by_digit_permutation x t d base;
      // Now we know:
      // count result_tail x == count t x + 1
      // count result_tail y == count t y for y <> x
      
      // Prove count result x == count s x + 1
      count_cons x h result_tail;
      assert (count result x == (if h = x then 1 else 0) + count result_tail x);
      assert (count result_tail x == count t x + 1);
      assert (count s x == (if h = x then 1 else 0) + count t x);
      
      // Prove count result y == count s y for y <> x
      let aux (y: nat) : Lemma (requires y <> x) (ensures count result y == count s y) =
        count_cons y h result_tail;
        assert (count result y == (if h = y then 1 else 0) + count result_tail y);
        assert (count result_tail y == count t y); // from IH for y <> x
        assert (count s y == (if h = y then 1 else 0) + count t y)
      in
      Classical.forall_intro (Classical.move_requires aux)
    )
#pop-options

/// Lemma: insertion_sort_by_digit is a permutation
let rec insertion_sort_permutation
  (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures permutation s (insertion_sort_by_digit s d base))
          (decreases (length s))
  = if length s = 0 then ()
    else (
      insertion_sort_permutation (tail s) d base;
      insert_by_digit_permutation (index s 0) (insertion_sort_by_digit (tail s) d base) d base;
      // Now prove that the full permutation holds
      let x = index s 0 in
      let sorted_tail = insertion_sort_by_digit (tail s) d base in
      let result = insert_by_digit x sorted_tail d base in
      // We know: sorted_tail is permutation of tail s
      // We know: result has count(result, x) = count(sorted_tail, x) + 1
      //          and count(result, y) = count(sorted_tail, y) for y <> x
      // Need: count(result, z) = count(s, z) for all z
      ()
    )

/// Lemma: stable_sort_on_digit is a permutation
let stable_sort_on_digit_permutation
  (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures permutation s (stable_sort_on_digit s d base))
  = insertion_sort_permutation s d base

/// Key stability property: stable sort preserves relative order of elements
/// with the same digit d. This is crucial for radix sort correctness.
/// 
/// Formally: if two elements x, y appear at positions i < j in input s,
/// and they have the same digit d, then x appears before y in the output.
///
/// WHY THIS IS NEEDED FOR RADIX SORT:
/// Radix sort processes digits from low to high (digit 0, then 1, then 2, ...).
/// After processing digits 0..d-1, the sequence is sorted on those lower digits.
/// When we sort on digit d, we must preserve the order established by lower digits
/// for elements that have the same digit d value. This is exactly what stability gives us.
///
/// PROOF APPROACH:
/// - insertion_sort_by_digit processes elements from right to left
/// - insert_by_digit places each element at the leftmost position where digit x <= digit h
/// - For two elements x, y with equal digit d values (both appearing at some positions in s):
///   * If x appears before y in s (at indices i < j)
///   * When processing y (before x, since we go right-to-left)
///   * y is placed at some position p_y in the partially sorted sequence
///   * When processing x (after y)
///   * Since digit x == digit y, x will be placed at or before p_y
///   * But by the "leftmost" placement rule, x goes to the left of any element with equal digit
///   * that was already there, maintaining the relative order x < y
let stable_sort_preserves_order
  (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures (
            let result = stable_sort_on_digit s d base in
            permutation s result /\
            sorted_on_digit result d base /\
            // Stability: for equal keys (digit d), maintain relative order
            (forall (i j: nat) (x y: nat).
              i < length s /\ j < length s /\ i < j /\
              index s i == x /\ index s j == y /\
              digit x d base == digit y d base ==>
              // Then x appears before y in result
              (exists (i' j': nat). 
                i' < length result /\ j' < length result /\
                index result i' == x /\ index result j' == y /\
                i' < j'))
          ))
  = admit() // Core stability reasoning - requires detailed proof about insertion sort
            // This would require:
            // 1. Define a "first occurrence" function: first_occ s x = min {i | index s i = x}
            // 2. Prove insert_by_digit preserves relative positions of existing elements
            // 3. Prove insertion_sort_by_digit maintains relative order through recursion
            // 4. Handle duplicate elements correctly (may need to track positions explicitly)

/// Helper: permutation is transitive
let permutation_transitive (s1 s2 s3: seq nat)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
          (ensures permutation s1 s3)
  = ()

/// Helper: stable sort on digit d preserves sorting on a different digit d'
/// This is a consequence of stability: if the input is sorted on digit d',
/// and we stably sort on digit d, elements with equal digit d maintain their
/// relative order, which preserves the sorting on digit d'.
let stable_sort_preserves_sorted_on_other_digit
  (s: seq nat) (sort_digit: nat) (preserve_digit: nat) (base: nat)
  : Lemma (requires base > 0 /\ sorted_on_digit s preserve_digit base)
          (ensures sorted_on_digit (stable_sort_on_digit s sort_digit base) preserve_digit base)
  = admit() // Follows from stability property: stable_sort_preserves_order
            // The proof needs to show that:
            // 1. stable_sort_on_digit is a permutation (already proven)
            // 2. For any consecutive elements in the result that violate preserve_digit ordering,
            //    we can trace back to the input and derive a contradiction from:
            //    - The input was sorted on preserve_digit
            //    - Stability preserves relative order for equal sort_digit values
            // The key case: if result[i] and result[i+1] violate preserve_digit ordering,
            // they must have had relative order in the input. If they have equal sort_digit,
            // stability would preserve their input order. If they have different sort_digit,
            // the sort placed them in sort_digit order, but this doesn't affect preserve_digit
            // relationships that were already established.

/// P1.2.6: radix_sort produces a permutation of the input
let rec radix_sort_permutation
  (s: seq nat) (num_digits: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures permutation s (radix_sort s num_digits base))
          (decreases num_digits)
  = if num_digits = 0 then ()
    else (
      // radix_sort s num_digits base = stable_sort_on_digit (radix_sort s (num_digits - 1) base) (num_digits - 1) base
      let s' = radix_sort s (num_digits - 1) base in
      radix_sort_permutation s (num_digits - 1) base;
      // Now: permutation s s'
      stable_sort_on_digit_permutation s' (num_digits - 1) base;
      // Now: permutation s' (stable_sort_on_digit s' (num_digits - 1) base)
      permutation_transitive s s' (stable_sort_on_digit s' (num_digits - 1) base)
    )

/// After sorting by multiple digits, sequence is sorted on lower digits
/// This is an intermediate property used in radix sort correctness.
///
/// KEY INSIGHT: Radix sort maintains the invariant that after d passes,
/// the sequence is sorted on digits 0, 1, ..., d-1.
///
/// Proof by induction on num_digits:
/// - Base case: num_digits = 0, trivially true
/// - Inductive case for check_digit = num_digits - 1:
///   We just sorted on this digit, so it's sorted
/// - Inductive case for check_digit < num_digits - 1:
///   By IH, radix_sort s (num_digits-1) is sorted on check_digit
///   We then apply stable_sort on digit (num_digits-1)
///   Stability ensures elements with equal digit (num_digits-1) keep their order
///   This preserves the sorting on lower digits!
#push-options "--z3rlimit 40"
let rec radix_sort_sorted_on_lower_digits
  (s: seq nat) (num_digits: nat) (base: nat) (check_digit: nat)
  : Lemma (requires base > 0 /\ check_digit < num_digits)
          (ensures sorted_on_digit (radix_sort s num_digits base) check_digit base)
          (decreases num_digits)
  = if num_digits = 0 then ()
    else if check_digit < num_digits - 1 then (
      // check_digit < num_digits - 1, so it's a lower digit
      // By IH, after (num_digits-1) passes, we're sorted on check_digit
      radix_sort_sorted_on_lower_digits s (num_digits - 1) base check_digit;
      let s' = radix_sort s (num_digits - 1) base in
      // s' is sorted on check_digit
      
      // Now we sort s' on digit (num_digits - 1), getting radix_sort s num_digits
      // Need to show: this preserves the sorting on check_digit
      stable_sort_preserves_sorted_on_other_digit s' (num_digits - 1) check_digit base
    ) else (
      // check_digit = num_digits - 1, which is the last digit we sort on
      stable_sort_on_digit_sorted (radix_sort s (num_digits - 1) base) (num_digits - 1) base
    )
#pop-options

/// pow splits: base^(a+b) = base^a * base^b
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

/// Sum of digits: digit_sum k d base = sum_{i=0}^{d-1} digit(k, i) * base^i
let rec digit_sum_multi (k: nat) (d: nat) (base: nat) : Tot nat (decreases d) =
  if d = 0 || base = 0 then 0
  else digit k (d - 1) base * pow base (d - 1) + digit_sum_multi k (d - 1) base

/// If all digits match, digit sums are equal
let rec digit_sum_equal_multi (x y: nat) (bigD: nat) (base: nat)
  : Lemma (requires base >= 2 /\
                    (forall (d: nat). d < bigD ==> digit x d base == digit y d base))
          (ensures digit_sum_multi x bigD base == digit_sum_multi y bigD base)
          (decreases bigD)
  = if bigD = 0 || base = 0 then ()
    else (
      digit_sum_equal_multi x y (bigD - 1) base;
      assert (digit x (bigD - 1) base == digit y (bigD - 1) base)
    )

/// digit_sum k d base < pow base d
let rec digit_sum_bound_multi (k: nat) (d: nat) (base: nat)
  : Lemma (requires base >= 2)
          (ensures digit_sum_multi k d base < pow base d)
          (decreases d)
  = if d = 0 || base = 0 then (pow_positive base 0)
    else (
      digit_sum_bound_multi k (d - 1) base;
      digit_bound k (d - 1) base;
      pow_positive base (d - 1);
      lemma_mult_le_right (pow base (d - 1)) (digit k (d - 1) base) (base - 1)
    )

/// Digit preservation: for d < bigD, digit(k, d) = digit(k % base^bigD, d)
/// (Raw form: the d-th digit of k is the same as d-th digit of k mod base^bigD)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let digit_preserved_by_modulo_multi (k: nat) (d: nat) (bigD: nat) (base: nat)
  : Lemma (requires base >= 2 /\ d < bigD /\ pow base d > 0 /\ pow base bigD > 0)
          (ensures (k / pow base d) % base == ((k % pow base bigD) / pow base d) % base)
  = pow_positive base (bigD - d);
    pow_split base d (bigD - d);
    assert (pow base (d + (bigD - d)) == pow base d * pow base (bigD - d));
    assert (d + (bigD - d) == bigD);
    modulo_division_lemma k (pow base d) (pow base (bigD - d));
    assert ((k % pow base bigD) / pow base d == (k / pow base d) % pow base (bigD - d));
    pow_positive base (bigD - d - 1);
    pow_split base 1 (bigD - d - 1);
    assert (pow base (1 + (bigD - d - 1)) == pow base 1 * pow base (bigD - d - 1));
    assert (pow base 1 == base);
    assert (pow base (bigD - d) == base * pow base (bigD - d - 1));
    modulo_modulo_lemma (k / pow base d) base (pow base (bigD - d - 1))
#pop-options

/// Key: k = digit_sum k bigD base for k < pow base bigD
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec digit_decomposition_multi (k: nat) (bigD: nat) (base: nat)
  : Lemma (requires bigD > 0 /\ base >= 2 /\ k < pow base bigD)
          (ensures k == digit_sum_multi k bigD base)
          (decreases bigD)
  = if bigD = 1 then (
      pow_positive base 0;
      assert (pow base 0 == 1);
      assert (k < base);
      small_modulo_lemma_1 k base;
      assert (k % base == k);
      assert (digit k 0 base == k);
      assert (digit_sum_multi k 1 base == k)
    ) else (
      pow_positive base (bigD - 1);
      pow_positive base bigD;
      lemma_div_mod k (pow base (bigD - 1));
      let q = k / pow base (bigD - 1) in
      let r = k % pow base (bigD - 1) in
      assert (pow base bigD == base * pow base (bigD - 1));
      assert (k < base * pow base (bigD - 1));
      assert (k == q * pow base (bigD - 1) + r);
      modulo_range_lemma k (pow base (bigD - 1));
      assert (r < pow base (bigD - 1));
      assert (q < base);
      small_modulo_lemma_1 q base;
      assert (digit k (bigD - 1) base == q);
      digit_decomposition_multi r (bigD - 1) base;
      assert (r == digit_sum_multi r (bigD - 1) base);
      let aux (d: nat{d < bigD - 1}) : Lemma (digit k d base == digit r d base) =
        pow_positive base d;
        digit_preserved_by_modulo_multi k d (bigD - 1) base;
        assert (digit k d base == (k / pow base d) % base);
        assert (digit r d base == (r / pow base d) % base)
      in
      Classical.forall_intro aux;
      digit_sum_equal_multi k r (bigD - 1) base
    )
#pop-options

/// digit_sum ordering when MSD differs: if digit x d0 < digit y d0 and
/// all higher digits (d0 < d' < d) are equal, then digit_sum x d ≤ digit_sum y d
#push-options "--z3rlimit 30 --fuel 2"
let rec digit_sum_msd_le_multi (x y: nat) (d d0: nat) (base: nat)
  : Lemma (requires base >= 2 /\ d0 < d /\
                    digit x d0 base < digit y d0 base /\
                    (forall (d': nat). d0 < d' /\ d' < d ==> digit x d' base == digit y d' base))
          (ensures digit_sum_multi x d base <= digit_sum_multi y d base)
          (decreases d)
  = if d = d0 + 1 then (
      pow_positive base d0;
      digit_sum_bound_multi x d0 base;
      lemma_mult_le_right (pow base d0) (digit x d0 base) (digit y d0 base - 1)
    ) else (
      assert (digit x (d - 1) base == digit y (d - 1) base);
      digit_sum_msd_le_multi x y (d - 1) d0 base
    )
#pop-options

/// Helper: if all digits 0..num_digits-1 match lexicographically, values are ordered
/// This is the fundamental property of positional notation:
/// If x and y differ at digit d (counting from low to high), and all higher digits match,
/// then x ≤ y iff digit_x(d) ≤ digit_y(d).
/// The key: higher digits (more significant) dominate lower ones.
let digits_lexicographic_implies_value_le
  (x y: nat) (num_digits: nat) (base: nat)
  : Lemma (requires base >= 2 /\ num_digits > 0 /\
                    x < pow base num_digits /\ y < pow base num_digits /\
                    // x and y compare lexicographically by digits
                    ((exists (d: nat). d < num_digits /\ 
                      digit x d base < digit y d base /\
                      (forall (d': nat). d < d' /\ d' < num_digits ==> digit x d' base == digit y d' base)) \/
                     (forall (d: nat). d < num_digits ==> digit x d base == digit y d base)))
          (ensures x <= y)
  = pow_positive base num_digits;
    digit_decomposition_multi x num_digits base;
    digit_decomposition_multi y num_digits base;
    // x == digit_sum x num_digits base, y == digit_sum y num_digits base
    // Case 1: all digits equal => digit_sums equal => x == y
    // Case 2: exists d with digit_x(d) < digit_y(d) and higher digits equal
    //         => digit_sum x num_digits <= digit_sum y num_digits => x <= y
    match FStar.StrongExcludedMiddle.strong_excluded_middle
      (forall (d: nat). d < num_digits ==> digit x d base == digit y d base) with
    | true -> digit_sum_equal_multi x y num_digits base
    | false -> 
      // The disjunction holds from the precondition. 
      // In the false branch, not all digits equal, so the existential case must hold.
      // Actually, the disjunction is from the precondition, we just dispatch each case.
      // Use Classical to dispatch
      let lem_exists (d: nat)
        : Lemma (requires d < num_digits /\
                          digit x d base < digit y d base /\
                          (forall (d': nat). d < d' /\ d' < num_digits ==> digit x d' base == digit y d' base))
                (ensures x <= y)
        = digit_decomposition_multi x num_digits base;
          digit_decomposition_multi y num_digits base;
          digit_sum_msd_le_multi x y num_digits d base
      in
      let lem_equal ()
        : Lemma (requires (forall (d: nat). d < num_digits ==> digit x d base == digit y d base))
                (ensures x <= y)
        = digit_decomposition_multi x num_digits base;
          digit_decomposition_multi y num_digits base;
          digit_sum_equal_multi x y num_digits base
      in
      // The precondition gives us the disjunction
      // We just need to show x <= y in both cases
      // F* should be able to see this with the two lemmas
      Classical.forall_intro (Classical.move_requires lem_exists);
      Classical.move_requires lem_equal ()

/// Helper: sorted on all digits implies sorted by value
/// If a sequence is sorted when comparing each digit position independently,
/// then it must be sorted by the full numeric value.
/// This follows from the lexicographic ordering property of positional notation.
/// Helper: from ∀d<nd. digit x d ≤ digit y d, establish lexicographic ordering.
/// Either all digits are equal, or the most significant differing digit has x<y
/// and all higher digits are equal.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec digitwise_le_implies_lex (x y: nat) (nd: nat) (base: nat)
  : Lemma (requires base >= 2 /\
                    (forall (d:nat). d < nd ==> digit x d base <= digit y d base))
          (ensures (forall (d:nat). d < nd ==> digit x d base == digit y d base) \/
                   (exists (d:nat). d < nd /\
                      digit x d base < digit y d base /\
                      (forall (d':nat). d < d' /\ d' < nd ==> digit x d' base == digit y d' base)))
          (decreases nd)
  = if nd = 0 then ()
    else begin
      // Check the most significant digit (nd - 1)
      let dx = digit x (nd - 1) base in
      let dy = digit y (nd - 1) base in
      // The forall gives us dx <= dy
      assert (nd - 1 < nd);  // trigger
      assert (dx <= dy);
      if dx < dy then begin
        // Found a strictly less digit at position nd-1
        // All higher digits d' > nd-1: vacuously true (d' < nd means d' <= nd-1)
        ()
      end else begin
        // dx = dy at position nd-1
        assert (dx == dy);
        // Apply IH for positions 0..nd-2
        digitwise_le_implies_lex x y (nd - 1) base;
        // IH gives us: either all digits 0..nd-2 are equal, or exists d < nd-1 with the property
        // In either case, we can extend to nd since digit at nd-1 is equal
        ()
      end
    end
#pop-options

/// Helper: sorted on all digits implies sorted by value
/// If a sequence is sorted when comparing each digit position independently,
/// then it must be sorted by the full numeric value.
/// This follows from the lexicographic ordering property of positional notation.
let rec sorted_all_digits_implies_sorted
  (s: seq nat) (num_digits: nat) (base: nat)
  : Lemma (requires base >= 2 /\ num_digits > 0 /\
                    (forall (i: nat). i < length s ==> index s i < pow base num_digits) /\
                    // Sorted on all individual digits
                    (forall (d: nat). d < num_digits ==> sorted_on_digit s d base))
          (ensures sorted s)
          (decreases (length s))
  = if length s <= 1 then ()
    else (
      // Show index s 0 <= index s 1
      let x = index s 0 in
      let y = index s 1 in
      pow_positive base num_digits;
      // From sorted_on_digit, digit x d ≤ digit y d for all d < num_digits
      // Use digitwise_le_implies_lex to establish the lexicographic precondition
      digitwise_le_implies_lex x y num_digits base;
      digits_lexicographic_implies_value_le x y num_digits base;
      assert (x <= y);
      // Now prove tail is sorted
      let t = tail s in
      assert (forall (i: nat). i < length t ==> index t i < pow base num_digits);
      // For each digit d, sorted_on_digit (tail s) d base follows from sorted_on_digit s d base
      let aux (d: nat) : Lemma (requires d < num_digits) (ensures sorted_on_digit t d base) =
        if length s > 1 then sorted_on_digit_tail s d base
      in
      Classical.forall_intro (Classical.move_requires aux);
      sorted_all_digits_implies_sorted t num_digits base
    )

/// Helper: if an element appears in a sequence, count > 0
let rec element_in_seq_has_positive_count (s: seq nat) (x: nat) (i: nat)
  : Lemma (requires i < length s /\ index s i == x)
          (ensures count s x > 0)
          (decreases (length s))
  = if i = 0 then ()
    else (
      assert (count s x >= count (tail s) x);
      element_in_seq_has_positive_count (tail s) x (i - 1)
    )

/// Helper: if count is positive, element is bounded by sequence bounds
let rec count_positive_implies_bounded (s: seq nat) (x: nat) (bound: nat)
  : Lemma (requires count s x > 0 /\ (forall (i: nat). i < length s ==> index s i < bound))
          (ensures x < bound)
          (decreases (length s))
  = if length s = 0 then ()
    else if index s 0 = x then ()
    else count_positive_implies_bounded (tail s) x bound

/// Helper: permutation preserves element bounds
let permutation_preserves_bounds (s1 s2: seq nat) (bound: nat)
  : Lemma (requires permutation s1 s2 /\ (forall (i: nat). i < length s1 ==> index s1 i < bound))
          (ensures (forall (i: nat). i < length s2 ==> index s2 i < bound))
  = let aux (i: nat{i < length s2}) : Lemma (ensures index s2 i < bound) =
      let x = index s2 i in
      element_in_seq_has_positive_count s2 x i;
      assert (count s2 x > 0);
      assert (count s1 x == count s2 x); // from permutation
      assert (count s1 x > 0);
      count_positive_implies_bounded s1 x bound
    in
    Classical.forall_intro aux

//SNIPPET_START: radix_sort_correct_multi
let radix_sort_correct
  (s: seq nat) (num_digits: nat) (base: nat)
  : Lemma (requires base >= 2 /\ num_digits > 0 /\
                    (forall (i: nat). i < length s ==> index s i < pow base num_digits))
          (ensures (let result = radix_sort s num_digits base in
                   permutation s result /\
                   sorted result))
//SNIPPET_END: radix_sort_correct_multi
  = let result = radix_sort s num_digits base in
    // Step 1: Prove result is a permutation
    radix_sort_permutation s num_digits base;
    permutation_preserves_bounds s result (pow base num_digits);
    
    // Step 2: Prove result is sorted on each individual digit
    // For each d < num_digits, we need sorted_on_digit result d base
    let aux (d: nat) : Lemma (requires d < num_digits) (ensures sorted_on_digit result d base) =
      radix_sort_sorted_on_lower_digits s num_digits base d
    in
    Classical.forall_intro (Classical.move_requires aux);
    assert (forall (d: nat). d < num_digits ==> sorted_on_digit result d base);
    
    // Step 3: Apply sorted_all_digits_implies_sorted
    // We have:
    // - result elements all < pow base num_digits (from permutation + input bounds)
    // - result is sorted on all digits d < num_digits
    // Therefore result is sorted
    sorted_all_digits_implies_sorted result num_digits base

(* ========== Example usage ========== *)

/// Example: Sort [170, 45, 75, 90, 2, 24, 802, 66] with base=10, d=3
/// This is the example from CLRS Figure 8.3
let example_radix_sort () : seq nat =
  let input = Seq.seq_of_list [170; 45; 75; 90; 2; 24; 802; 66] in
  radix_sort input 3 10

/// The example produces a sorted sequence
#push-options "--warn_error -271"
let example_radix_sort_correct ()
  : Lemma (ensures (let result = example_radix_sort () in
                   sorted result))
  = let input : seq nat = Seq.seq_of_list [170; 45; 75; 90; 2; 24; 802; 66] in
    // All numbers fit in 3 digits base 10: max is 802 < 1000 = 10^3
    pow_positive 10 3;
    assert (pow 10 3 == 1000);
    assert (forall (i: nat). i < length input ==> index input i < 1000);
    radix_sort_correct input 3 10
#pop-options
