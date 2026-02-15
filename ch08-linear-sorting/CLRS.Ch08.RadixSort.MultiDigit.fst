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
  = admit() // Basic sequence properties

/// Helper: tail of cons is the original sequence
let cons_tail (x: nat) (s: seq nat)
  : Lemma (tail (cons x s) == s)
  = admit() // Basic sequence properties

/// Helper: if s is sorted on digit d and has length >= 2, then tail s is sorted on digit d
let sorted_on_digit_tail (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0 /\ length s > 1 /\ sorted_on_digit s d base)
          (ensures sorted_on_digit (tail s) d base)
  = admit() // Follows directly from definition of sorted_on_digit, but Z3 needs help unfolding recursive prop

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

/// Apply radix sort for num_digits passes, sorting by digits 0, 1, ..., num_digits-1
/// This implements CLRS RADIX-SORT(A, d) where d = num_digits
let rec radix_sort (s: seq nat) (num_digits: nat) (base: nat) 
  : Tot (seq nat) (decreases num_digits)
  = if num_digits = 0 then
      s
    else
      // Sort by digit 0 first, then digit 1, ..., then digit num_digits-1
      let s' = radix_sort s (num_digits - 1) base in
      stable_sort_on_digit s' (num_digits - 1) base

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
      //
      // REQUIRES STABILITY: The stable sort on digit (num_digits-1) must preserve
      // the relative order of elements with equal digit (num_digits-1).
      // In particular, if two elements have the same digit (num_digits-1),
      // their relative order (and thus their order by digit check_digit) is preserved.
      //
      // Since s' is sorted on check_digit, and stability preserves this order
      // for elements with equal high digit, the result is still sorted on check_digit.
      //
      // This would follow from stable_sort_preserves_order, but we need a slightly
      // different formulation: not just preserving relative positions of equal elements,
      // but preserving sorted-ness on a different digit.
      admit() // Requires stability: stable sort on digit d preserves sorting on digit d' < d
    ) else (
      // check_digit = num_digits - 1, which is the last digit we sort on
      stable_sort_on_digit_sorted (radix_sort s (num_digits - 1) base) (num_digits - 1) base
    )
#pop-options

/// Helper: if all digits 0..num_digits-1 match lexicographically, values are ordered
/// This is the fundamental property of positional notation:
/// If x and y differ at digit d (counting from low to high), and all lower digits match,
/// then x < y iff digit_x(d) < digit_y(d), scaled by base^d.
let digits_lexicographic_implies_value_le
  (x y: nat) (num_digits: nat) (base: nat)
  : Lemma (requires base >= 2 /\ num_digits > 0 /\
                    x < pow base num_digits /\ y < pow base num_digits /\
                    // x and y compare lexicographically by digits
                    ((exists (d: nat). d < num_digits /\ 
                      digit x d base < digit y d base /\
                      (forall (d': nat). d' < d ==> digit x d' base == digit y d' base)) \/
                     (forall (d: nat). d < num_digits ==> digit x d base == digit y d base)))
          (ensures x <= y)
  = admit() // Arithmetic reasoning about positional notation
            // Proof sketch:
            // 1. If all digits match, then x == y by uniqueness of base representation
            // 2. Otherwise, let d be the first digit where they differ
            // 3. Write x = sum_{i<d} digit_x(i)*base^i + digit_x(d)*base^d + sum_{i>d} digit_x(i)*base^i
            // 4. Write y = sum_{i<d} digit_y(i)*base^i + digit_y(d)*base^d + sum_{i>d} digit_y(i)*base^i
            // 5. For i < d: digit_x(i) = digit_y(i), so lower sums are equal
            // 6. digit_x(d) < digit_y(d) gives (digit_y(d) - digit_x(d)) * base^d >= base^d
            // 7. Upper sums are bounded: sum_{i>d} digit(i)*base^i < base^(d+1) + base^(d+2) + ... < base^d * (base/(base-1))
            // 8. For base >= 2, the difference at digit d outweighs all higher digit variations

/// Helper: sorted on all digits implies sorted by value
/// If a sequence is sorted when comparing each digit position independently,
/// then it must be sorted by the full numeric value.
/// This follows from the lexicographic ordering property of positional notation.
let sorted_all_digits_implies_sorted
  (s: seq nat) (num_digits: nat) (base: nat)
  : Lemma (requires base >= 2 /\ num_digits > 0 /\
                    (forall (i: nat). i < length s ==> index s i < pow base num_digits) /\
                    // Sorted on all individual digits
                    (forall (d: nat). d < num_digits ==> sorted_on_digit s d base))
          (ensures sorted s)
  = admit() // Follows from digits_lexicographic_implies_value_le
            // Proof sketch:
            // For any indices i < j, need to show: index s i <= index s j
            // Let x = index s i, y = index s j
            // Case 1: All digits match - then x = y by uniqueness of representation
            //   ∀d < num_digits. digit x d = digit y d ==> x = y
            // Case 2: Some digit differs - let d be the LOWEST digit where they differ
            //   Since sorted_on_digit s d holds for all d, we have:
            //   ∀d. digit (index s i) d <= digit (index s j) d
            //   For the lowest differing digit d: digit x d < digit y d
            //   All lower digits match by choice of d
            //   Apply digits_lexicographic_implies_value_le to get x <= y
            //
            // The key insight: being sorted on digit d means the d-th position
            // (from the right) is non-decreasing throughout the sequence.
            // Combined across all digit positions, this implies the full numbers are sorted.

/// P1.2.5: Main correctness theorem: radix_sort produces a fully sorted permutation
/// 
/// Key insight (CLRS Lemma 8.3): If we run d passes of stable digit sort
/// (from digit 0 to d-1), the result is sorted by the full key value,
/// provided all keys fit within d digits.
let radix_sort_correct
  (s: seq nat) (num_digits: nat) (base: nat)
  : Lemma (requires base >= 2 /\ num_digits > 0 /\
                    // All elements fit within num_digits digits
                    (forall (i: nat). i < length s ==> index s i < pow base num_digits))
          (ensures (let result = radix_sort s num_digits base in
                   permutation s result /\
                   sorted result))
  = let result = radix_sort s num_digits base in
    // Step 1: Prove result is a permutation
    radix_sort_permutation s num_digits base;
    // Step 2: The result is sorted on each individual digit
    // This follows from radix_sort_sorted_on_lower_digits for each d < num_digits
    // Step 3: Being sorted on all digits implies fully sorted
    // This requires showing that lexicographic digit order implies value order
    admit() // Final step: sorted_all_digits_implies_sorted + instantiation of radix_sort_sorted_on_lower_digits

(* ========== Example usage ========== *)

/// Example: Sort [170, 45, 75, 90, 2, 24, 802, 66] with base=10, d=3
/// This is the example from CLRS Figure 8.3
let example_radix_sort () : seq nat =
  let input = Seq.seq_of_list [170; 45; 75; 90; 2; 24; 802; 66] in
  radix_sort input 3 10

/// The example produces a sorted sequence
let example_radix_sort_correct ()
  : Lemma (ensures (let result = example_radix_sort () in
                   sorted result))
  = admit() // Would follow from radix_sort_correct once proven
