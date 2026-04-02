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
   - Correctness lemmas (fully verified)
   
   This is PURE F* (not Pulse) - all functions are functional.
*)

module CLRS.Ch08.RadixSort.MultiDigit

open FStar.Seq
open FStar.Math.Lemmas
open FStar.Mul
open FStar.Classical
open CLRS.Ch08.RadixSort.Base
module ID = FStar.IndefiniteDescription
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties

(* ========== Seq helpers ========== *)

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

/// Helper: count in cons
let count_cons (x h: nat) (s: seq nat)
  : Lemma (count (cons h s) x == (if h = x then 1 else 0) + count s x)
  = count_unfold (cons h s) x;
    SeqP.head_cons h s;
    SeqP.lemma_tl h s

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
      s
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
    let result = insert_by_digit x s d base in
    if length s = 0 then (
      // result = create 1 x
      count_unfold s x;     // count empty x == 0
      count_unfold result x; // count (create 1 x) x == 1 + count (tail (create 1 x)) x
      count_unfold (tail result) x; // count empty x == 0
      // For y <> x: count result y == count s y == 0
      let aux (y: nat) : Lemma (requires y <> x) (ensures count result y == count s y) =
        count_unfold s y;
        count_unfold result y;
        count_unfold (tail result) y
      in
      Classical.forall_intro (Classical.move_requires aux)
    )
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
      count_unfold s x;
      assert (count result x == (if h = x then 1 else 0) + count result_tail x);
      assert (count result_tail x == count t x + 1);
      assert (count s x == (if h = x then 1 else 0) + count t x);
      
      // Prove count result y == count s y for y <> x
      let aux (y: nat) : Lemma (requires y <> x) (ensures count result y == count s y) =
        count_cons y h result_tail;
        count_unfold s y;
        assert (count result y == (if h = y then 1 else 0) + count result_tail y);
        assert (count result_tail y == count t y); // from IH for y <> x
        assert (count s y == (if h = y then 1 else 0) + count t y)
      in
      Classical.forall_intro (Classical.move_requires aux)
    )
#pop-options

/// Lemma: insertion_sort_by_digit is a permutation
#restart-solver
#push-options "--z3rlimit 30 --split_queries always"
let insertion_sort_permutation_base
  (s: seq nat{length s = 0}) (d: nat) (base: pos)
  : Lemma (permutation s (insertion_sort_by_digit s d base))
  = () // insertion_sort_by_digit s d base = s by fuel reduction

let rec insertion_sort_permutation
  (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures permutation s (insertion_sort_by_digit s d base))
          (decreases (length s))
  = if length s = 0 then
      insertion_sort_permutation_base s d base
    else (
      insertion_sort_permutation (tail s) d base;
      let x = index s 0 in
      let sorted_tail = insertion_sort_by_digit (tail s) d base in
      insert_by_digit_permutation x sorted_tail d base;
      let result = insert_by_digit x sorted_tail d base in
      let aux (z: nat) : Lemma (count s z == count result z) =
        count_unfold s z;
        permutation_count (tail s) sorted_tail z
        // count s z == (if x=z then 1 else 0) + count sorted_tail z
        // From insert_by_digit_permutation:
        //   count result x == count sorted_tail x + 1
        //   z<>x ==> count result z == count sorted_tail z
      in
      Classical.forall_intro aux
    )
#pop-options

/// Lemma: stable_sort_on_digit is a permutation
let stable_sort_on_digit_permutation
  (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures permutation s (stable_sort_on_digit s d base))
  = insertion_sort_permutation s d base

/// Helper: if an element appears in a sequence, count > 0
let rec element_in_seq_has_positive_count (s: seq nat) (x: nat) (i: nat)
  : Lemma (requires i < length s /\ index s i == x)
          (ensures count s x > 0)
          (decreases (length s))
  = count_unfold s x;
    if i = 0 then ()
    else element_in_seq_has_positive_count (tail s) x (i - 1)

/// Element at position k in s appears somewhere in insert_by_digit h s
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec insert_contains (h: nat) (s: seq nat) (d base: nat) (k: nat)
  : Lemma (requires base > 0 /\ k < length s)
          (ensures (insert_by_digit_length h s d base;
                    let result = insert_by_digit h s d base in
                    exists (k': nat). k' < length result /\ index result k' == index s k))
          (decreases (length s))
  = insert_by_digit_length h s d base;
    if length s = 0 then ()
    else if digit h d base <= digit (index s 0) d base then cons_tail h s
    else (insert_by_digit_length h (tail s) d base;
          cons_tail (index s 0) (insert_by_digit h (tail s) d base);
          if k = 0 then () else insert_contains h (tail s) d base (k - 1))
#pop-options

/// Insert x before equal-digit element
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec insert_before_equal (x: nat) (s: seq nat) (d base: nat) (py: nat)
  : Lemma (requires base > 0 /\ py < length s /\ digit x d base == digit (index s py) d base)
          (ensures (insert_by_digit_length x s d base;
                    let result = insert_by_digit x s d base in
                    exists (px' py': nat). px' < py' /\ py' < length result /\
                      index result px' == x /\ index result py' == index s py))
          (decreases (length s))
  = insert_by_digit_length x s d base;
    if length s = 0 then ()
    else if digit x d base <= digit (index s 0) d base then cons_tail x s
    else (if py = 0 then ()
          else (insert_before_equal x (tail s) d base (py - 1);
                insert_by_digit_length x (tail s) d base;
                cons_tail (index s 0) (insert_by_digit x (tail s) d base);
                let rt = insert_by_digit x (tail s) d base in
                let px'' = ID.indefinite_description_ghost nat
                  (fun px'' -> exists (py'': nat). px'' < py'' /\ py'' < length rt /\
                    index rt px'' == x /\ index rt py'' == index (tail s) (py - 1)) in
                let _py'' = ID.indefinite_description_ghost nat
                  (fun py'' -> px'' < py'' /\ py'' < length rt /\
                    index rt px'' == x /\ index rt py'' == index (tail s) (py - 1)) in
                ()))
#pop-options

/// Insert preserves relative order of existing elements.
/// Explicit witness shifting needed: the existential postcondition with
/// insert_by_digit creates a refinement matching loop (~4M quantifier
/// instances) when Z3 attempts to find witnesses implicitly.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 80 --split_queries always"
let rec insert_preserves_order (h: nat) (s: seq nat) (d base: nat) (px py: nat)
  : Lemma (requires base > 0 /\ px < py /\ py < length s)
          (ensures (insert_by_digit_length h s d base;
                    let result = insert_by_digit h s d base in
                    exists (px' py': nat). px' < py' /\ py' < length result /\
                      index result px' == index s px /\ index result py' == index s py))
          (decreases (length s))
  = insert_by_digit_length h s d base;
    if length s = 0 then ()
    else if digit h d base <= digit (index s 0) d base then cons_tail h s
    else (let t = tail s in
          insert_by_digit_length h t d base;
          cons_tail (index s 0) (insert_by_digit h t d base);
          if px = 0 then insert_contains h t d base (py - 1)
          else (insert_preserves_order h t d base (px - 1) (py - 1);
                let rt = insert_by_digit h t d base in
                let result = insert_by_digit h s d base in
                assert (result == Seq.cons (index s 0) rt);
                let px'' = ID.indefinite_description_ghost nat
                  (fun px'' -> exists (py'': nat). px'' < py'' /\ py'' < length rt /\
                    index rt px'' == index t (px - 1) /\ index rt py'' == index t (py - 1)) in
                let py'' = ID.indefinite_description_ghost nat
                  (fun py'' -> px'' < py'' /\ py'' < length rt /\
                    index rt px'' == index t (px - 1) /\ index rt py'' == index t (py - 1)) in
                // Witnesses for result = cons (head s) rt: shift +1
                // result[px''+1] = rt[px''] = t[px-1] = s[px]
                // result[py''+1] = rt[py''] = t[py-1] = s[py]
                assert (px'' + 1 < py'' + 1 /\ py'' + 1 < length result /\
                        index result (px'' + 1) == index s px /\
                        index result (py'' + 1) == index s py)))
#pop-options

/// Length of insertion sort result equals input length
let rec insertion_sort_length (s: seq nat) (d base: nat)
  : Lemma (requires base > 0) (ensures length (insertion_sort_by_digit s d base) == length s)
          (decreases (length s))
  = if length s = 0 then ()
    else (insertion_sort_length (tail s) d base;
          insert_by_digit_length (index s 0) (insertion_sort_by_digit (tail s) d base) d base)

/// Unfold insertion sort one step
let insertion_sort_unfold (s: seq nat) (d base: nat)
  : Lemma (requires base > 0 /\ length s > 0)
          (ensures insertion_sort_by_digit s d base == 
                   insert_by_digit (index s 0) (insertion_sort_by_digit (tail s) d base) d base)
  = ()

/// Insertion sort is stable for distinct elements
#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
let rec insertion_sort_stable (s: seq nat) (d base: nat) (i j: nat)
  : Lemma
    (requires base > 0 /\ i < j /\ j < length s /\
              index s i <> index s j /\
              digit (index s i) d base == digit (index s j) d base)
    (ensures (insertion_sort_length s d base;
              let result = insertion_sort_by_digit s d base in
              exists (i' j': nat). i' < j' /\ j' < length result /\
                index result i' == index s i /\ index result j' == index s j))
    (decreases (length s))
  = insertion_sort_length s d base;
    insertion_sort_length (tail s) d base;
    insertion_sort_unfold s d base;
    let sorted_tail = insertion_sort_by_digit (tail s) d base in
    insert_by_digit_length (index s 0) sorted_tail d base;
    if i = 0 then (
      insertion_sort_permutation (tail s) d base;
      element_in_seq_has_positive_count (tail s) (index s j) (j - 1);
      count_positive_means_appears sorted_tail (index s j);
      let pos = ID.indefinite_description_ghost nat
        (fun pos -> pos < length sorted_tail /\ index sorted_tail pos == index s j) in
      insert_before_equal (index s 0) sorted_tail d base pos
    ) else (
      insertion_sort_stable (tail s) d base (i - 1) (j - 1);
      let i'' = ID.indefinite_description_ghost nat 
        (fun i'' -> exists (j'': nat). i'' < j'' /\ j'' < length sorted_tail /\
          index sorted_tail i'' == index s i /\ index sorted_tail j'' == index s j) in
      let j'' = ID.indefinite_description_ghost nat
        (fun j'' -> i'' < j'' /\ j'' < length sorted_tail /\
          index sorted_tail i'' == index s i /\ index sorted_tail j'' == index s j) in
      insert_preserves_order (index s 0) sorted_tail d base i'' j''
    )
#pop-options

/// Two occurrences means count >= 2
let rec two_elem_count (s: seq nat) (x: nat) (i j: nat)
  : Lemma (requires i < j /\ j < length s /\ index s i == x /\ index s j == x)
          (ensures count s x >= 2) (decreases (length s))
  = count_unfold s x;
    if i = 0 then element_in_seq_has_positive_count (tail s) x (j - 1)
    else two_elem_count (tail s) x (i - 1) (j - 1)

/// If count >= 2, find two positions
let rec two_positions (s: seq nat) (v: nat)
  : Lemma (requires count s v >= 2)
          (ensures exists (i j: nat). i < j /\ j < length s /\ index s i == v /\ index s j == v)
          (decreases (length s))
  = count_unfold s v;
    if length s = 0 then ()
    else if index s 0 = v then (
      count_positive_means_appears (tail s) v
    ) else two_positions (tail s) v

/// Stable sort preserves relative order (proven via insertion sort stability)
/// Stability for a specific pair: if i < j in input with same digit, 
/// then there exist positions i' < j' in output with same values
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let stable_sort_preserves_order_pair
  (s: seq nat) (d: nat) (base: nat) (i: nat{i < length s}) (j: nat{j < length s /\ i < j})
  : Lemma (requires base > 0 /\ digit (index s i) d base == digit (index s j) d base)
          (ensures (let result = stable_sort_on_digit s d base in
                    exists (i' j': nat). i' < length result /\ j' < length result /\
                      index result i' == index s i /\ index result j' == index s j /\ i' < j'))
  = let result = stable_sort_on_digit s d base in
    let x = index s i in
    let y = index s j in
    if x = y then (
      two_elem_count s x i j;
      stable_sort_on_digit_permutation s d base;
      two_positions result x
    ) else (
      insertion_sort_length s d base;
      insertion_sort_stable s d base i j
    )
#pop-options

/// Full stability: permutation + sorted + stability for all pairs
let stable_sort_preserves_order
  (s: seq nat) (d: nat) (base: nat)
  : Lemma (requires base > 0)
          (ensures 
            permutation s (stable_sort_on_digit s d base) /\
            sorted_on_digit (stable_sort_on_digit s d base) d base)
  = stable_sort_on_digit_permutation s d base;
    stable_sort_on_digit_sorted s d base

/// All elements in s are pairwise distinct
let distinct (s: seq nat) : prop =
  forall (i j: nat). i < j /\ j < length s ==> index s i <> index s j

/// Distinctness is preserved by permutation
let distinct_preserved_by_permutation (s1 s2: seq nat)
  : Lemma (requires distinct s1 /\ permutation s1 s2)
          (ensures distinct s2)
  = let aux (i j: nat) : Lemma
      (ensures (i < j /\ j < length s2) ==> index s2 i <> index s2 j) =
      if i < j && j < length s2 then (
        if index s2 i = index s2 j then (
          two_elem_count s2 (index s2 i) i j;
          two_positions s1 (index s2 i)
        )
      )
    in
    Classical.forall_intro_2 aux

/// Recursive lexicographic ordering on digit max_d (MSD-first comparison)
let rec lex_le_r (v w: nat) (max_d base: nat) : Tot prop (decreases (max_d + 1)) =
  if max_d = 0 then digit v 0 base <= digit w 0 base
  else digit v max_d base < digit w max_d base \/
       (digit v max_d base == digit w max_d base /\ lex_le_r v w (max_d - 1) base)

/// Lexicographic ordering on digits 0..max_d (radix sort invariant)
/// Consecutive-pair recursive definition avoids quantifier trigger issues
let rec sorted_up_to_digit (s: seq nat) (max_d base: nat) : Tot prop (decreases (length s)) =
  base > 0 /\
  (length s <= 1 \/
   (lex_le_r (index s 0) (index s 1) max_d base /\ sorted_up_to_digit (tail s) max_d base))

/// lex_le_r reflexivity
let rec lex_le_r_refl (v: nat) (max_d base: nat)
  : Lemma (ensures lex_le_r v v max_d base) (decreases max_d)
  = if max_d = 0 then () else lex_le_r_refl v (max_d - 1) base

/// lex_le_r transitivity
let rec lex_le_r_transitive (u v w: nat) (max_d base: nat)
  : Lemma (requires lex_le_r u v max_d base /\ lex_le_r v w max_d base)
          (ensures lex_le_r u w max_d base) (decreases max_d)
  = if max_d = 0 then ()
    else if digit u max_d base < digit w max_d base then ()
    else if digit u max_d base = digit w max_d base then begin
      assert (digit u max_d base == digit v max_d base);
      lex_le_r_transitive u v w (max_d - 1) base
    end else ()

/// Extract lex_le_r for arbitrary index pairs from sorted_up_to_digit
#push-options "--z3rlimit 20"
let rec sorted_up_to_digit_elim (s: seq nat) (max_d base: nat) (i j: nat)
  : Lemma (requires sorted_up_to_digit s max_d base /\ i < j /\ j < length s)
          (ensures lex_le_r (index s i) (index s j) max_d base) (decreases j)
  = if i = 0 && j = 1 then ()
    else if i = 0 then begin
      let t = tail s in
      assert (index t 0 == index s 1); assert (index t (j - 1) == index s j);
      sorted_up_to_digit_elim t max_d base 0 (j - 1);
      lex_le_r_transitive (index s 0) (index s 1) (index s j) max_d base
    end else begin
      let t = tail s in
      assert (i - 1 < length t);
      assert (j - 1 < length t);
      assert (index t (i - 1) == index s i); assert (index t (j - 1) == index s j);
      sorted_up_to_digit_elim t max_d base (i - 1) (j - 1)
    end
#pop-options

/// Establish sorted_up_to_digit from consecutive pair proofs
let rec sorted_up_to_digit_intro (s: seq nat) (max_d base: nat)
  (h: (i: nat) -> Lemma (requires i + 1 < length s) (ensures lex_le_r (index s i) (index s (i + 1)) max_d base))
  : Lemma (requires base > 0) (ensures sorted_up_to_digit s max_d base) (decreases (length s))
  = if length s <= 1 then ()
    else begin
      h 0;
      let t = tail s in
      let h' (i: nat) : Lemma (requires i + 1 < length t) (ensures lex_le_r (index t i) (index t (i + 1)) max_d base) =
        assert (index t i == index s (i + 1)); assert (index t (i + 1) == index s (i + 2)); h (i + 1) in
      sorted_up_to_digit_intro t max_d base h'
    end

/// Backward stability for distinct elements: if v before w in output, then v before w in input
#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
let backward_stability (s: seq nat) (d base: nat) (i j: nat)
  : Lemma 
    (requires base > 0 /\ distinct s /\
              i < j /\ j < length (stable_sort_on_digit s d base) /\
              index (stable_sort_on_digit s d base) i <> index (stable_sort_on_digit s d base) j /\
              digit (index (stable_sort_on_digit s d base) i) d base == 
              digit (index (stable_sort_on_digit s d base) j) d base)
    (ensures (exists (a b: nat). a < b /\ b < length s /\
                index s a == index (stable_sort_on_digit s d base) i /\ 
                index s b == index (stable_sort_on_digit s d base) j))
  = let result = stable_sort_on_digit s d base in
    let v = index result i in
    let w = index result j in
    stable_sort_on_digit_permutation s d base;
    element_in_seq_has_positive_count result v i;
    count_positive_means_appears s v;
    let a = ID.indefinite_description_ghost nat (fun a -> a < length s /\ index s a == v) in
    element_in_seq_has_positive_count result w j;
    count_positive_means_appears s w;
    let b = ID.indefinite_description_ghost nat (fun b -> b < length s /\ index s b == w) in
    if b < a then (
      stable_sort_preserves_order_pair s d base b a;
      distinct_preserved_by_permutation s result;
      insertion_sort_length s d base;
      let j' = ID.indefinite_description_ghost nat 
        (fun j' -> exists (i': nat). j' < i' /\ i' < length result /\
          index result j' == w /\ index result i' == v) in
      let i' = ID.indefinite_description_ghost nat
        (fun i' -> j' < i' /\ i' < length result /\
          index result j' == w /\ index result i' == v) in
      assert (i' <> i \/ j' <> j \/ j < i);
      ()
    ) else ()
#pop-options

/// sorted_on_digit implies digit-monotonicity for all pairs
let rec sorted_on_digit_le (s: seq nat) (d base: nat) (i j: nat)
  : Lemma (requires sorted_on_digit s d base /\ i < j /\ j < length s)
          (ensures digit (index s i) d base <= digit (index s j) d base)
          (decreases j)
  = if i = 0 && j = 1 then ()
    else if i = 0 then (
      sorted_on_digit_tail s d base;
      sorted_on_digit_le (tail s) d base 0 (j - 1)
    ) else (
      sorted_on_digit_tail s d base;
      sorted_on_digit_le (tail s) d base (i - 1) (j - 1)
    )

/// Helper: backward stability + lex ordering extraction (separated for VC size)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let backward_stability_with_order (s: seq nat) (d base: nat) (i: nat)
  : Lemma
    (requires base >= 2 /\ d > 0 /\ distinct s /\
              sorted_up_to_digit s (d - 1) base /\
              (let result = stable_sort_on_digit s d base in
               i + 1 < length result /\
               index result i <> index result (i + 1) /\
               digit (index result i) d base == digit (index result (i + 1)) d base))
    (ensures (let result = stable_sort_on_digit s d base in
              lex_le_r (index result i) (index result (i + 1)) (d - 1) base))
  = let result = stable_sort_on_digit s d base in
    let vi = index result i in
    let vj = index result (i + 1) in
    stable_sort_on_digit_permutation s d base;
    insertion_sort_length s d base;
    backward_stability s d base i (i + 1);
    let a = ID.indefinite_description_ghost nat 
      (fun a -> exists b. a < b /\ b < length s /\ index s a == vi /\ index s b == vj) in
    let b = ID.indefinite_description_ghost nat 
      (fun b -> a < b /\ b < length s /\ index s a == vi /\ index s b == vj) in
    sorted_up_to_digit_elim s (d - 1) base a b
#pop-options

/// Stable sort on distinct sequences preserves sorted_up_to_digit ordering
#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let stable_sort_preserves_sorted_up_to
  (s: seq nat) (d base: nat)
  : Lemma 
    (requires base >= 2 /\ distinct s /\
              sorted_on_digit (stable_sort_on_digit s d base) d base /\
              (d == 0 \/ (d > 0 /\ sorted_up_to_digit s (d - 1) base)))
    (ensures sorted_up_to_digit (stable_sort_on_digit s d base) d base)
  = let result = stable_sort_on_digit s d base in
    stable_sort_on_digit_permutation s d base;
    insertion_sort_length s d base;
    distinct_preserved_by_permutation s result;
    let pair_proof (i: nat) 
      : Lemma (requires i + 1 < length result)
              (ensures lex_le_r (index result i) (index result (i + 1)) d base) =
      let vi = index result i in
      let vj = index result (i + 1) in
      sorted_on_digit_le result d base i (i + 1);
      if digit vi d base < digit vj d base then ()
      else if d = 0 then ()
      else if vi = vj then lex_le_r_refl vi d base
      else backward_stability_with_order s d base i
    in
    sorted_up_to_digit_intro result d base pair_proof
#pop-options

/// P1.2.6: radix_sort produces a permutation of the input
#push-options "--z3rlimit 40"
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
#pop-options

/// Helper for radix_sort_invariant inductive step
#push-options "--z3rlimit 20 --split_queries always"
let radix_sort_invariant_step
  (s: seq nat) (num_digits: nat) (base: nat)
  : Lemma (requires base >= 2 /\ distinct s /\ num_digits > 1 /\
                    (let s' = radix_sort s (num_digits - 1) base in
                     distinct s' /\ sorted_up_to_digit s' (num_digits - 2) base /\
                     permutation s s'))
          (ensures distinct (radix_sort s num_digits base) /\
                   sorted_up_to_digit (radix_sort s num_digits base) (num_digits - 1) base)
  = let d = num_digits - 1 in
    let s' = radix_sort s (num_digits - 1) base in
    assert (distinct s');
    assert (sorted_up_to_digit s' (d - 1) base);
    stable_sort_on_digit_permutation s' d base;
    insertion_sort_length s' d base;
    let result = stable_sort_on_digit s' d base in
    distinct_preserved_by_permutation s' result;
    assert (distinct result);
    stable_sort_on_digit_sorted s' d base;
    assert (sorted_on_digit result d base);
    assert (d > 0 /\ sorted_up_to_digit s' (d - 1) base);
    stable_sort_preserves_sorted_up_to s' d base
#pop-options

/// Radix sort invariant: after d passes on distinct sequence, sorted_up_to_digit
#push-options "--z3rlimit 40"
let rec radix_sort_invariant
  (s: seq nat) (num_digits: nat) (base: nat)
  : Lemma (requires base >= 2 /\ distinct s /\ num_digits > 0)
          (ensures distinct (radix_sort s num_digits base) /\
                   sorted_up_to_digit (radix_sort s num_digits base) (num_digits - 1) base)
          (decreases num_digits)
  = if num_digits = 1 then begin
      stable_sort_on_digit_permutation s 0 base;
      insertion_sort_length s 0 base;
      distinct_preserved_by_permutation s (stable_sort_on_digit s 0 base);
      stable_sort_on_digit_sorted s 0 base;
      stable_sort_preserves_sorted_up_to s 0 base
    end else begin
      radix_sort_invariant s (num_digits - 1) base;
      radix_sort_permutation s (num_digits - 1) base;
      radix_sort_invariant_step s num_digits base
    end
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
#restart-solver
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1 --split_queries always"
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
      let dx = digit x (nd - 1) base in
      let dy = digit y (nd - 1) base in
      assert (nd - 1 < nd);  // trigger
      assert (dx <= dy);
      if dx < dy then begin
        assert (digit x (nd - 1) base < digit y (nd - 1) base);
        assert (forall (d':nat). (nd - 1) < d' /\ d' < nd ==> digit x d' base == digit y d' base);
        ()
      end else begin
        assert (dx == dy);
        digitwise_le_implies_lex x y (nd - 1) base;
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


/// Helper: if count is positive, element is bounded by sequence bounds
let rec count_positive_implies_bounded (s: seq nat) (x: nat) (bound: nat)
  : Lemma (requires count s x > 0 /\ (forall (i: nat). i < length s ==> index s i < bound))
          (ensures x < bound)
          (decreases (length s))
  = count_unfold s x;
    if length s = 0 then ()
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

/// Transfer lex_le_r when all digits match (used for modular arithmetic decomposition)
let rec lex_le_r_transfer (v w v' w': nat) (max_d base: nat)
  : Lemma (requires lex_le_r v w max_d base /\
                    (forall (i: nat{i <= max_d}). digit v' i base == digit v i base) /\
                    (forall (i: nat{i <= max_d}). digit w' i base == digit w i base))
          (ensures lex_le_r v' w' max_d base) (decreases max_d)
  = if max_d = 0 then ()
    else if digit v max_d base < digit w max_d base then ()
    else lex_le_r_transfer v w v' w' (max_d - 1) base

/// lex_le_r implies value ≤ (via digit decomposition)
#push-options "--z3rlimit 20"
let rec lex_le_r_to_value_le (v w: nat) (num_digits base: nat)
  : Lemma (requires base >= 2 /\ num_digits > 0 /\ v < pow base num_digits /\ w < pow base num_digits /\
                    lex_le_r v w (num_digits - 1) base)
          (ensures v <= w) (decreases num_digits)
  = pow_positive base num_digits;
    digit_decomposition_multi v num_digits base;
    digit_decomposition_multi w num_digits base;
    if num_digits = 1 then ()
    else begin
      let d = num_digits - 1 in
      if digit v d base < digit w d base then
        digit_sum_msd_le_multi v w num_digits d base
      else begin
        let v' = v % pow base d in
        let w' = w % pow base d in
        pow_positive base d;
        modulo_range_lemma v (pow base d);
        modulo_range_lemma w (pow base d);
        let aux (i: nat{i < d}) : Lemma (digit v' i base == digit v i base /\ digit w' i base == digit w i base) =
          pow_positive base i;
          digit_preserved_by_modulo_multi v i d base;
          digit_preserved_by_modulo_multi w i d base
        in
        Classical.forall_intro aux;
        lex_le_r_transfer v w v' w' (d - 1) base;
        lex_le_r_to_value_le v' w' d base;
        lemma_div_mod v (pow base d);
        lemma_div_mod w (pow base d)
      end
    end
#pop-options

/// Helper: pairwise ≤ implies sorted (callback style avoids quantifier trigger issues)
let rec pairwise_le_implies_sorted (s: seq nat)
  (hyp: (i: nat) -> Lemma (requires i + 1 < length s) (ensures index s i <= index s (i + 1)))
  : Lemma (ensures sorted s) (decreases (length s))
  = if length s <= 1 then ()
    else begin
      hyp 0;
      let t = tail s in
      let hyp' (i: nat) : Lemma (requires i + 1 < length t) (ensures index t i <= index t (i + 1)) =
        assert (index t i == index s (i + 1));
        assert (index t (i + 1) == index s (i + 2));
        hyp (i + 1)
      in
      pairwise_le_implies_sorted t hyp'
    end

/// sorted_up_to_digit implies sorted by value
#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
let sorted_up_to_digit_implies_sorted (s: seq nat) (num_digits: nat) (base: nat)
  : Lemma (requires base >= 2 /\ num_digits > 0 /\
                    (forall (i: nat). i < length s ==> index s i < pow base num_digits) /\
                    sorted_up_to_digit s (num_digits - 1) base)
          (ensures sorted s)
  = let aux (i: nat) : Lemma (requires i + 1 < length s) (ensures index s i <= index s (i + 1))
      = pow_positive base num_digits;
        sorted_up_to_digit_elim s (num_digits - 1) base i (i + 1);
        lex_le_r_to_value_le (index s i) (index s (i + 1)) num_digits base
    in
    pairwise_le_implies_sorted s aux
#pop-options

//SNIPPET_START: radix_sort_correct_multi
let radix_sort_correct
  (s: seq nat) (num_digits: nat) (base: nat)
  : Lemma (requires base >= 2 /\ num_digits > 0 /\ distinct s /\
                    (forall (i: nat). i < length s ==> index s i < pow base num_digits))
          (ensures (let result = radix_sort s num_digits base in
                   permutation s result /\
                   sorted result))
//SNIPPET_END: radix_sort_correct_multi
  = let result = radix_sort s num_digits base in
    radix_sort_permutation s num_digits base;
    permutation_preserves_bounds s result (pow base num_digits);
    radix_sort_invariant s num_digits base;
    sorted_up_to_digit_implies_sorted result num_digits base

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
    pow_positive 10 3;
    assert (pow 10 3 == 1000);
    assert (forall (i: nat). i < length input ==> index input i < 1000);
    assert (distinct input);
    radix_sort_correct input 3 10
#pop-options
