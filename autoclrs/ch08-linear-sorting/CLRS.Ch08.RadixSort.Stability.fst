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
open FStar.Classical
open FStar.IndefiniteDescription
open CLRS.Ch08.RadixSort.Base
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties

(* ========== Sorted predicates (Stability-specific) ========== *)

/// Sorted by multiple digits 0..max_d (lexicographic order, MSD-primary)
/// This is the key property maintained by radix sort:
/// After sorting by digit max_d, the most significant differing digit determines order.
/// Made opaque to prevent Z3 matching loop between its internal pattern and
/// is_stable_sort_on_digit's pattern.
[@@"opaque_to_smt"]
let sorted_up_to_digit (s: seq nat) (max_d: nat) (base: nat) : prop =
  base > 0 /\
  (forall (i j: nat). {:pattern (index s i); (index s j)}
    i < j /\ j < length s ==>
    ((exists (d0: nat). d0 <= max_d /\
       digit (index s i) d0 base < digit (index s j) d0 base /\
       (forall (d': nat). d0 < d' /\ d' <= max_d ==> digit (index s i) d' base == digit (index s j) d' base)) \/
     (forall (d: nat). d <= max_d ==> digit (index s i) d base == digit (index s j) d base)))

/// Instantiate sorted_up_to_digit for a specific pair (unfold/reveal).
let sorted_up_to_digit_at (s: seq nat) (max_d: nat) (base: nat) (i j: nat)
  : Lemma (requires sorted_up_to_digit s max_d base /\ i < j /\ j < length s)
          (ensures (exists (d0: nat). d0 <= max_d /\
                      digit (index s i) d0 base < digit (index s j) d0 base /\
                      (forall (d': nat). d0 < d' /\ d' <= max_d ==> digit (index s i) d' base == digit (index s j) d' base)) \/
                   (forall (d: nat). d <= max_d ==> digit (index s i) d base == digit (index s j) d base))
  = reveal_opaque (`%sorted_up_to_digit) (sorted_up_to_digit s max_d base)

/// Fold back: prove sorted_up_to_digit from pointwise property.
/// Caller provides an SMTPat-guided aux lemma for each pair.
let sorted_up_to_digit_intro (s: seq nat) (max_d: nat) (base: nat)
  : Lemma (requires base > 0 /\
            (forall (i j: nat). {:pattern (index s i); (index s j)}
              i < j /\ j < length s ==>
              ((exists (d0: nat). d0 <= max_d /\
                 digit (index s i) d0 base < digit (index s j) d0 base /\
                 (forall (d': nat). d0 < d' /\ d' <= max_d ==> digit (index s i) d' base == digit (index s j) d' base)) \/
               (forall (d: nat). d <= max_d ==> digit (index s i) d base == digit (index s j) d base))))
          (ensures sorted_up_to_digit s max_d base)
  = reveal_opaque (`%sorted_up_to_digit) (sorted_up_to_digit s max_d base)

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

(* ========== Stability definition ========== *)

/// A stable sort maintains relative order of elements with equal keys.
/// Made opaque to prevent Z3 matching loop between sorted_on_digit unfolding
/// and the stability forall pattern.
[@@"opaque_to_smt"]
let is_stable_sort_on_digit (s_in s_out: seq nat) (d: nat) (base: nat) : prop =
  base > 0 /\
  permutation s_in s_out /\
  sorted_on_digit s_out d base /\
  (forall (j1 j2: nat). {:pattern (index s_out j1); (index s_out j2)}
    j1 < j2 /\ j2 < length s_out /\
    digit (index s_out j1) d base == digit (index s_out j2) d base /\
    index s_out j1 <> index s_out j2 ==>
    (exists (i1 i2: nat). i1 < i2 /\ i2 < length s_in /\
      index s_in i1 == index s_out j1 /\ index s_in i2 == index s_out j2))

/// Extract permutation from is_stable_sort_on_digit
let is_stable_get_perm (s_in s_out: seq nat) (d base: nat)
  : Lemma (requires is_stable_sort_on_digit s_in s_out d base)
          (ensures permutation s_in s_out)
  = reveal_opaque (`%is_stable_sort_on_digit) (is_stable_sort_on_digit s_in s_out d base)

/// Extract sorted_on_digit from is_stable_sort_on_digit
let is_stable_get_sorted (s_in s_out: seq nat) (d base: nat)
  : Lemma (requires is_stable_sort_on_digit s_in s_out d base)
          (ensures sorted_on_digit s_out d base)
  = reveal_opaque (`%is_stable_sort_on_digit) (is_stable_sort_on_digit s_in s_out d base)

/// Extract stability witnesses for a specific pair
let is_stable_get_witnesses (s_in s_out: seq nat) (d base: nat) (j1 j2: nat)
  : Lemma (requires is_stable_sort_on_digit s_in s_out d base /\
                    j1 < j2 /\ j2 < length s_out /\
                    digit (index s_out j1) d base == digit (index s_out j2) d base /\
                    index s_out j1 <> index s_out j2)
          (ensures exists (i1 i2: nat). i1 < i2 /\ i2 < length s_in /\
                    index s_in i1 == index s_out j1 /\ index s_in i2 == index s_out j2)
  = reveal_opaque (`%is_stable_sort_on_digit) (is_stable_sort_on_digit s_in s_out d base)

/// Pack components into is_stable_sort_on_digit.
/// The order_proof function provides stability witnesses for each pair.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --split_queries always"
let pack_is_stable (s_in s_out: seq nat) (d base: nat)
  (order_proof: (j1: nat) -> (j2: nat) -> Lemma
    (requires j1 < j2 /\ j2 < length s_out /\
      digit (index s_out j1) d base == digit (index s_out j2) d base /\
      index s_out j1 <> index s_out j2)
    (ensures exists (i1 i2: nat). i1 < i2 /\ i2 < length s_in /\
      index s_in i1 == index s_out j1 /\ index s_in i2 == index s_out j2))
  : Lemma (requires base > 0 /\ permutation s_in s_out /\ sorted_on_digit s_out d base)
    (ensures is_stable_sort_on_digit s_in s_out d base)
  = reveal_opaque (`%is_stable_sort_on_digit) (is_stable_sort_on_digit s_in s_out d base);
    introduce forall (j1: nat) (j2: nat).
      j1 < j2 /\ j2 < length s_out /\
      digit (index s_out j1) d base == digit (index s_out j2) d base /\
      index s_out j1 <> index s_out j2 ==>
      (exists (i1 i2: nat). i1 < i2 /\ i2 < length s_in /\
        index s_in i1 == index s_out j1 /\ index s_in i2 == index s_out j2)
    with introduce _ ==> _ with _.
      order_proof j1 j2
#pop-options

(* ========== Helper lemmas for sorted_up_to_digit ========== *)

/// Base case: empty sequence is sorted up to any digit
let sorted_up_to_digit_empty (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures sorted_up_to_digit empty d base)
  = reveal_opaque (`%sorted_up_to_digit) (sorted_up_to_digit empty d base)

/// Single element is sorted up to any digit
let sorted_up_to_digit_singleton (x: nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures sorted_up_to_digit (create 1 x) d base)
  = reveal_opaque (`%sorted_up_to_digit) (sorted_up_to_digit (create 1 x) d base)


// Note: monotonicity (sorted_up_to_digit s d base ==> sorted_up_to_digit s d' base for d' <= d)
// does NOT hold for the MSD-primary formulation. This is correct behavior:
// sorted_up_to_digit s 1 base does not imply sorted_up_to_digit s 0 base
// because the digit-1 ordering may override digit-0 ordering.
// Each pass of radix sort builds the property from scratch for the new max_d.

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
  = let aux (i: nat) (j: nat) : Lemma
      (requires i < j /\ j < length s)
      (ensures (exists (d0: nat). d0 <= 0 /\
                   digit (index s i) d0 base < digit (index s j) d0 base /\
                   (forall (d': nat). d0 < d' /\ d' <= 0 ==> digit (index s i) d' base == digit (index s j) d' base)) \/
               (forall (d: nat). d <= 0 ==> digit (index s i) d base == digit (index s j) d base))
      [SMTPat (index s i); SMTPat (index s j)]
      = sorted_on_digit_at s 0 base i j
    in
    sorted_up_to_digit_intro s 0 base

/// Helper: sorted_up_to_digit at witnesses gives lex ordering on values
#push-options "--fuel 1 --ifuel 1 --z3rlimit 5"
let lemma_sorted_implies_lex_values (s_in: seq nat) (d: nat) (base: nat) (v w: nat) (i1 i2: nat)
  : Lemma (requires d > 0 /\ base > 0 /\
                    i1 < i2 /\ i2 < length s_in /\
                    index s_in i1 == v /\ index s_in i2 == w /\
                    sorted_up_to_digit s_in (d - 1) base)
          (ensures (exists (d0: nat). d0 < d /\
                      digit v d0 base < digit w d0 base /\
                      (forall (d': nat). d0 < d' /\ d' < d ==> digit v d' base == digit w d' base)) \/
                   (forall (d': nat). d' < d ==> digit v d' base == digit w d' base))
  = sorted_up_to_digit_at s_in (d - 1) base i1 i2
#pop-options

/// LEMMA 1: Key insight - stability preserves existing order structure
/// 
/// Isolated per-pair proof: given specific output positions i < j with equal digit d,
/// derive lower-digit ordering using stability + sorted_up_to_digit.
/// This is isolated so Z3 only sees the minimal set of hypotheses.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 5"
let stable_preserves_lower_order_pair
  (s_in s_out: seq nat) (d base: nat) (i j: nat)
  : Lemma 
    (requires base > 0 /\ d > 0 /\
              is_stable_sort_on_digit s_in s_out d base /\
              sorted_up_to_digit s_in (d - 1) base /\
              i < j /\ j < length s_out /\
              digit (index s_out i) d base == digit (index s_out j) d base)
    (ensures (exists (d0: nat). d0 < d /\
                digit (index s_out i) d0 base < digit (index s_out j) d0 base /\
                (forall (d': nat). d0 < d' /\ d' < d ==> 
                  digit (index s_out i) d' base == digit (index s_out j) d' base)) \/
             (forall (d': nat). d' < d ==> 
                digit (index s_out i) d' base == digit (index s_out j) d' base))
  = let v = index s_out i in
    let w = index s_out j in
    if v = w then ()
    else begin
      // Extract stability witnesses (reveals is_stable_sort_on_digit only here)
      is_stable_get_witnesses s_in s_out d base i j;
      let i1 = indefinite_description_ghost nat
        (fun i1 -> exists (i2: nat). i1 < i2 /\ i2 < length s_in /\
          index s_in i1 == v /\ index s_in i2 == w) in
      let i2 = indefinite_description_ghost nat
        (fun i2 -> i1 < i2 /\ i2 < length s_in /\
          index s_in i1 == v /\ index s_in i2 == w) in
      sorted_up_to_digit_at s_in (d - 1) base i1 i2
    end
#pop-options

/// LEMMA: Stability preserves existing order structure.
let lemma_stable_sort_preserves_lower_order
  (s_in s_out: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0 /\ d > 0 /\
                    is_stable_sort_on_digit s_in s_out d base /\
                    sorted_up_to_digit s_in (d - 1) base)
          (ensures 
            (forall (i j: nat). {:pattern (index s_out i); (index s_out j)}
               i < j /\ j < length s_out /\
               digit (index s_out i) d base == digit (index s_out j) d base ==>
               ((exists (d0: nat). d0 < d /\
                  digit (index s_out i) d0 base < digit (index s_out j) d0 base /\
                  (forall (d': nat). d0 < d' /\ d' < d ==> 
                    digit (index s_out i) d' base == digit (index s_out j) d' base)) \/
                (forall (d': nat). d' < d ==> 
                  digit (index s_out i) d' base == digit (index s_out j) d' base))))
  = let aux (i j: nat) : Lemma
      (requires i < j /\ j < length s_out /\
                digit (index s_out i) d base == digit (index s_out j) d base)
      (ensures (exists (d0: nat). d0 < d /\
                  digit (index s_out i) d0 base < digit (index s_out j) d0 base /\
                  (forall (d': nat). d0 < d' /\ d' < d ==>
                    digit (index s_out i) d' base == digit (index s_out j) d' base)) \/
               (forall (d': nat). d' < d ==>
                  digit (index s_out i) d' base == digit (index s_out j) d' base))
      [SMTPat (index s_out i); SMTPat (index s_out j)]
      = stable_preserves_lower_order_pair s_in s_out d base i j
    in
    ()

/// Helper: extends lower-digit ordering (digits 0..d-1) to full ordering (digits 0..d)
/// when digit d is equal and all lower digits are equal.
let extend_all_equal
  (v w: nat) (d: nat) (base: nat)
  : Lemma 
    (requires d > 0 /\ base > 0 /\
              digit v d base == digit w d base /\
              (forall (d': nat). d' < d ==> digit v d' base == digit w d' base))
    (ensures forall (dd: nat). dd <= d ==> digit v dd base == digit w dd base)
  = ()

/// Helper: extends lower-digit strict ordering to include digit d when equal.
#push-options "--z3rlimit 10"
let extend_exists_case
  (v w: nat) (d: nat) (base: nat)
  : Lemma 
    (requires d > 0 /\ base > 0 /\
              digit v d base == digit w d base /\
              (exists (d0: nat). d0 < d /\
                digit v d0 base < digit w d0 base /\
                (forall (d': nat). d0 < d' /\ d' < d ==> digit v d' base == digit w d' base)))
    (ensures exists (d0: nat). d0 <= d /\
                digit v d0 base < digit w d0 base /\
                (forall (d': nat). d0 < d' /\ d' <= d ==> digit v d' base == digit w d' base))
  = let d0 = indefinite_description_ghost nat
      (fun d0 -> d0 < d /\
        digit v d0 base < digit w d0 base /\
        (forall (d': nat). d0 < d' /\ d' < d ==> digit v d' base == digit w d' base)) in
    assert (d0 <= d);
    assert (digit v d0 base < digit w d0 base);
    assert (forall (d': nat). d0 < d' /\ d' <= d ==> digit v d' base == digit w d' base)
#pop-options

/// Helper: for digit strictly less case
let digit_strict_lt_gives_lex
  (v w: nat) (d: nat) (base: nat)
  : Lemma 
    (requires digit v d base < digit w d base)
    (ensures exists (d0: nat). d0 <= d /\
                digit v d0 base < digit w d0 base /\
                (forall (d': nat). d0 < d' /\ d' <= d ==> digit v d' base == digit w d' base))
  = ()

/// MAIN THEOREM: Each pass of stable digit sort extends sorted range by one digit
///
/// If input is sorted on digits 0..d-1, and we apply a stable sort on digit d,
/// then output is sorted on digits 0..d.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 120"
let lemma_stable_pass_preserves_ordering
  (s_in s_out: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0 /\
                    is_stable_sort_on_digit s_in s_out d base /\
                    (d = 0 \/ (d > 0 /\ sorted_up_to_digit s_in (d - 1) base)))
          (ensures sorted_up_to_digit s_out d base)
  = if d = 0 then (
      is_stable_get_sorted s_in s_out 0 base;
      sorted_on_to_up_to_base_case s_out base
    ) else (
      is_stable_get_sorted s_in s_out d base;
      lemma_stable_sort_preserves_lower_order s_in s_out d base;
      let aux (i j: nat) : Lemma
        (requires i < j /\ j < length s_out)
        (ensures (exists (d0: nat). d0 <= d /\
                    digit (index s_out i) d0 base < digit (index s_out j) d0 base /\
                    (forall (d': nat). d0 < d' /\ d' <= d ==>
                      digit (index s_out i) d' base == digit (index s_out j) d' base)) \/
                 (forall (dd: nat). dd <= d ==>
                    digit (index s_out i) dd base == digit (index s_out j) dd base))
        [SMTPat (index s_out i); SMTPat (index s_out j)]
        = sorted_on_digit_at s_out d base i j;
          let v = index s_out i in
          let w = index s_out j in
          assert (digit v d base <= digit w d base);
          if digit v d base < digit w d base then
            digit_strict_lt_gives_lex v w d base
          else begin
            assert (digit v d base == digit w d base);
            match FStar.IndefiniteDescription.strong_excluded_middle
              (exists (d0: nat). d0 < d /\
                digit v d0 base < digit w d0 base /\
                (forall (d': nat). d0 < d' /\ d' < d ==> digit v d' base == digit w d' base)) with
            | true -> extend_exists_case v w d base
            | false -> extend_all_equal v w d base
          end
      in
      sorted_up_to_digit_intro s_out d base
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
    else if d = 1 then (
      extract_stable_sort_property s0 steps 0 d base;
      is_stable_get_perm s0 (List.Tot.index steps 0) 0 base
    )
    else (
      stable_sort_chain_permutation s0 steps (d - 1) base;
      extract_stable_sort_property s0 steps (d - 1) d base;
      let s_prev = List.Tot.index steps (d - 2) in
      let s_curr = List.Tot.index steps (d - 1) in
      is_stable_get_perm s_prev s_curr (d - 1) base;
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
    forall (j1 j2: nat).
      j1 < j2 /\ j2 < length s_out /\
      digit (index s_out j1) d base == digit (index s_out j2) d base /\
      index s_out j1 <> index s_out j2 ==>
      (exists (i1 i2: nat). i1 < i2 /\ i2 < length s_in /\
        index s_in i1 == index s_out j1 /\ index s_in i2 == index s_out j2)))
  : Lemma (ensures is_stable_sort_on_digit s_in s_out d base)
  = reveal_opaque (`%is_stable_sort_on_digit) (is_stable_sort_on_digit s_in s_out d base)

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
  = lemma_stable_pass_preserves_ordering s_in s_out d base;
    is_stable_get_perm s_in s_out d base

