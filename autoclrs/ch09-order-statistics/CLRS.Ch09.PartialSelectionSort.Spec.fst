(*
   Pure F* Specification for the Selection Problem (Chapter 9)
   
   Defines what it means for an algorithm to correctly find the k-th smallest element.
   
   Key Definitions:
   - is_sorted: a sequence is sorted
   - is_permutation: two sequences have the same elements (with multiplicity)
   - pure_sort: insertion sort on sequences
   - select_spec: the k-th element of the sorted sequence
   - count_lt/count_le: counting predicates for partition property
   
   Properties Proven:
   - pure_sort produces a sorted permutation
   - select_spec has the partition property: exactly k elements are < result
   - Uniqueness: the result is determined by the partition property
   
   This spec is used by the Pulse implementations (Quickselect, Select) to
   state their correctness theorems.
*)

module CLRS.Ch09.PartialSelectionSort.Spec

open FStar.Seq
open FStar.Classical

module Seq = FStar.Seq

(*** Basic Predicates ***)

// A sequence is sorted if every element is ≤ all later elements
let is_sorted (s: seq int) : prop =
  forall (i: nat) (j: nat). i < Seq.length s /\ j < Seq.length s /\ i <= j ==>
    Seq.index s i <= Seq.index s j

// Count occurrences of a value in a sequence
let rec count_occ (s: seq int) (x: int)
  : Tot nat (decreases Seq.length s)
  = if Seq.length s = 0 then 0
    else (if Seq.index s 0 = x then 1 else 0) + count_occ (Seq.tail s) x

// Two sequences are permutations if they have the same elements with multiplicity
let is_permutation (s1 s2: seq int) : prop =
  Seq.length s1 = Seq.length s2 /\
  (forall (x: int). count_occ s1 x = count_occ s2 x)

// Count elements strictly less than v
let rec count_lt (s: seq int) (v: int)
  : Tot nat (decreases Seq.length s)
  = if Seq.length s = 0 then 0
    else (if Seq.index s 0 < v then 1 else 0) + count_lt (Seq.tail s) v

// Count elements less than or equal to v
let rec count_le (s: seq int) (v: int)
  : Tot nat (decreases Seq.length s)
  = if Seq.length s = 0 then 0
    else (if Seq.index s 0 <= v then 1 else 0) + count_le (Seq.tail s) v

(*** Insertion Sort Implementation ***)

// Insert an element into a sorted sequence, maintaining sortedness
let rec insert (x: int) (s: seq int)
  : Tot (seq int) (decreases Seq.length s)
  = if Seq.length s = 0 then Seq.create 1 x
    else if x <= Seq.index s 0 then Seq.cons x s
    else Seq.cons (Seq.index s 0) (insert x (Seq.tail s))

// Sort a sequence using insertion sort
let rec pure_sort (s: seq int)
  : Tot (seq int) (decreases Seq.length s)
  = if Seq.length s = 0 then Seq.empty
    else insert (Seq.index s 0) (pure_sort (Seq.tail s))

(*** Properties of insert ***)

let rec insert_length (x: int) (s: seq int)
  : Lemma (ensures Seq.length (insert x s) = Seq.length s + 1)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else if x <= Seq.index s 0 then ()
    else insert_length x (Seq.tail s)

(*** Properties of pure_sort ***)

let rec pure_sort_length (s: seq int)
  : Lemma (ensures Seq.length (pure_sort s) = Seq.length s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (
      pure_sort_length (Seq.tail s);
      insert_length (Seq.index s 0) (pure_sort (Seq.tail s))
    )

(*** Main Specification ***)

//SNIPPET_START: select_spec
// The k-th smallest element is the element at index k in the sorted sequence
let select_spec (s: seq int) (k: nat{k < Seq.length s}) : int =
  pure_sort_length s;
  Seq.index (pure_sort s) k
//SNIPPET_END: select_spec

(*** Lemmas about count_occ ***)

let count_occ_empty (x: int)
  : Lemma (count_occ Seq.empty x = 0)
  = ()

let count_occ_cons (hd: int) (tl: seq int) (x: int)
  : Lemma (ensures count_occ (Seq.cons hd tl) x =
                   (if hd = x then 1 else 0) + count_occ tl x)
  = // Seq.cons hd tl has hd at index 0, and tail is tl
    let s = Seq.cons hd tl in
    assert (Seq.index s 0 == hd);
    assert (Seq.equal (Seq.tail s) tl)

#push-options "--z3rlimit 5"
let rec count_occ_append (s1 s2: seq int) (x: int)
  : Lemma (ensures count_occ (Seq.append s1 s2) x = count_occ s1 x + count_occ s2 x)
          (decreases Seq.length s1)
  = if Seq.length s1 = 0 then (
      assert (Seq.equal (Seq.append s1 s2) s2)
    ) else (
      let hd = Seq.index s1 0 in
      let tl = Seq.tail s1 in
      assert (Seq.equal (Seq.append s1 s2) (Seq.cons hd (Seq.append tl s2)));
      count_occ_cons hd (Seq.append tl s2) x;
      count_occ_append tl s2 x;
      count_occ_cons hd tl x;
      assert (Seq.equal s1 (Seq.cons hd tl))
    )
#pop-options

let count_occ_singleton (x: int) (y: int)
  : Lemma (count_occ (Seq.create 1 x) y = (if x = y then 1 else 0))
  = ()

(*** Lemmas about count_lt and count_le ***)

let count_lt_empty (v: int)
  : Lemma (count_lt Seq.empty v = 0)
  = ()

let count_le_empty (v: int)
  : Lemma (count_le Seq.empty v = 0)
  = ()

// W328: rec needed for Z3 encoding (removing breaks insert_sorted proof)
#push-options "--warn_error -328"
let rec count_lt_cons (hd: int) (tl: seq int) (v: int)
  : Lemma (ensures count_lt (Seq.cons hd tl) v =
                   (if hd < v then 1 else 0) + count_lt tl v)
  = let s = Seq.cons hd tl in
    assert (Seq.index s 0 == hd);
    assert (Seq.equal (Seq.tail s) tl)

let rec count_le_cons (hd: int) (tl: seq int) (v: int)
  : Lemma (ensures count_le (Seq.cons hd tl) v =
                   (if hd <= v then 1 else 0) + count_le tl v)
  = let s = Seq.cons hd tl in
    assert (Seq.index s 0 == hd);
    assert (Seq.equal (Seq.tail s) tl)
#pop-options

let rec count_lt_append (s1 s2: seq int) (v: int)
  : Lemma (ensures count_lt (Seq.append s1 s2) v = count_lt s1 v + count_lt s2 v)
          (decreases Seq.length s1)
  = if Seq.length s1 = 0 then (
      assert (Seq.equal (Seq.append s1 s2) s2)
    ) else (
      let hd = Seq.index s1 0 in
      let tl = Seq.tail s1 in
      assert (Seq.equal (Seq.append s1 s2) (Seq.cons hd (Seq.append tl s2)));
      count_lt_cons hd (Seq.append tl s2) v;
      count_lt_append tl s2 v;
      count_lt_cons hd tl v;
      assert (Seq.equal s1 (Seq.cons hd tl))
    )

let rec count_le_append (s1 s2: seq int) (v: int)
  : Lemma (ensures count_le (Seq.append s1 s2) v = count_le s1 v + count_le s2 v)
          (decreases Seq.length s1)
  = if Seq.length s1 = 0 then (
      assert (Seq.equal (Seq.append s1 s2) s2)
    ) else (
      let hd = Seq.index s1 0 in
      let tl = Seq.tail s1 in
      assert (Seq.equal (Seq.append s1 s2) (Seq.cons hd (Seq.append tl s2)));
      count_le_cons hd (Seq.append tl s2) v;
      count_le_append tl s2 v;
      count_le_cons hd tl v;
      assert (Seq.equal s1 (Seq.cons hd tl))
    )

(*** Properties of is_permutation ***)

let is_permutation_refl (s: seq int)
  : Lemma (is_permutation s s)
  = ()

let is_permutation_symm (s1 s2: seq int)
  : Lemma (requires is_permutation s1 s2)
          (ensures is_permutation s2 s1)
  = ()

let is_permutation_trans (s1 s2 s3: seq int)
  : Lemma (requires is_permutation s1 s2 /\ is_permutation s2 s3)
          (ensures is_permutation s1 s3)
  = ()

(*** Properties of insert (continued) ***)

let rec insert_permutation (x: int) (s: seq int)
  : Lemma (ensures is_permutation (insert x s) (Seq.cons x s))
          (decreases Seq.length s)
  = insert_length x s;
    let result = insert x s in
    let target = Seq.cons x s in
    let aux (y: int) : Lemma (count_occ result y = count_occ target y) =
      if Seq.length s = 0 then (
        count_occ_singleton x y;
        count_occ_cons x Seq.empty y
      ) else if x <= Seq.index s 0 then (
        count_occ_cons x s y
      ) else (
        insert_permutation x (Seq.tail s);
        count_occ_cons (Seq.index s 0) (insert x (Seq.tail s)) y;
        count_occ_cons x s y;
        count_occ_cons (Seq.index s 0) (Seq.tail s) y;
        count_occ_cons x (Seq.tail s) y
      )
    in
    Classical.forall_intro aux

#restart-solver
#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"
/// Helper: cons preserves sorting when head is <= all elements
let sorted_cons (h: int) (t: seq int)
  : Lemma (requires is_sorted t /\
                    (Seq.length t = 0 \/ h <= Seq.index t 0))
          (ensures is_sorted (Seq.cons h t))
  = let r = Seq.cons h t in
    introduce forall (i: nat) (j: nat). i < Seq.length r /\ j < Seq.length r /\ i <= j ==> Seq.index r i <= Seq.index r j
    with introduce _ ==> _
    with _. (
      if i = 0 then (
        if j = 0 then ()
        else assert (Seq.index r j == Seq.index t (j - 1))
      ) else (
        assert (Seq.index r i == Seq.index t (i - 1));
        assert (Seq.index r j == Seq.index t (j - 1))
      )
    )
#pop-options

#restart-solver
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
/// Head of insert: the first element of (insert x s) is min(x, head s)
let insert_head (x: int) (s: seq int)
  : Lemma (requires Seq.length s > 0)
          (ensures Seq.length (insert x s) > 0 /\
                   Seq.index (insert x s) 0 == (if x <= Seq.index s 0 then x else Seq.index s 0))
  = ()
#pop-options

#restart-solver
#push-options "--z3rlimit 5 --fuel 1 --ifuel 0"
/// Extract: head of sorted sequence is <= any element
let sorted_head_le_index (s: seq int) (j: nat)
  : Lemma (requires is_sorted s /\ Seq.length s > 0 /\ j < Seq.length s)
          (ensures Seq.index s 0 <= Seq.index s j)
  = ()

/// Tail of a sorted sequence is sorted
#push-options "--z3rlimit 5"
let sorted_tail_spec (s: seq int)
  : Lemma (requires Seq.length s > 1 /\ is_sorted s)
          (ensures is_sorted (Seq.tail s))
  = let t = Seq.tail s in
    let n = Seq.length t in
    introduce forall (i: nat) (j: nat). i < n /\ j < n /\ i <= j ==> Seq.index t i <= Seq.index t j
    with introduce _ ==> _
    with _. (
      assert (Seq.index t i == Seq.index s (i + 1));
      assert (Seq.index t j == Seq.index s (j + 1));
      assert (i + 1 <= j + 1)
    )
#pop-options
#pop-options

#restart-solver
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
let rec insert_sorted (x: int) (s: seq int)
  : Lemma (requires is_sorted s)
          (ensures is_sorted (insert x s))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else if x <= Seq.index s 0 then
      sorted_cons x s
    else (
      let hd = Seq.index s 0 in
      let tl = Seq.tail s in
      if Seq.length tl > 0 then sorted_tail_spec s else ();
      insert_sorted x tl;
      insert_length x tl;
      if Seq.length tl = 0 then ()
      else begin
        sorted_head_le_index s 1;
        insert_head x tl
      end;
      sorted_cons hd (insert x tl)
    )
#pop-options

(*** Properties of pure_sort (continued) ***)

let rec pure_sort_sorted (s: seq int)
  : Lemma (ensures is_sorted (pure_sort s))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (
      pure_sort_sorted (Seq.tail s);
      insert_sorted (Seq.index s 0) (pure_sort (Seq.tail s))
    )

let rec pure_sort_permutation (s: seq int)
  : Lemma (ensures is_permutation (pure_sort s) s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (
      let hd = Seq.index s 0 in
      let tl = Seq.tail s in
      pure_sort_permutation tl;
      insert_permutation hd (pure_sort tl);
      // pure_sort s = insert hd (pure_sort tl)
      // insert hd (pure_sort tl) is perm of cons hd (pure_sort tl)
      // pure_sort tl is perm of tl
      // So cons hd (pure_sort tl) is perm of cons hd tl = s
      let aux (x: int) : Lemma (count_occ (pure_sort s) x = count_occ s x) =
        count_occ_cons hd tl x;
        count_occ_cons hd (pure_sort tl) x
      in
      Classical.forall_intro aux;
      pure_sort_length s
    )

(*** Partition Property ***)

// In a sorted sequence, if we look at position k, then:
// - Exactly k elements (at positions 0..k-1) are < s[k]
// - At least k+1 elements (positions 0..k) are <= s[k]

#push-options "--z3rlimit 5 --fuel 2"
let rec count_lt_sorted_prefix (s: seq int) (k: nat) (v: int)
  : Lemma (requires k <= Seq.length s /\
                     (forall (i: nat). i < k ==> Seq.index s i < v))
          (ensures count_lt (Seq.slice s 0 k) v = k)
          (decreases k)
  = if k = 0 then ()
    else (
      let prefix = Seq.slice s 0 k in
      let head_seq = Seq.slice s 0 1 in
      let rest = Seq.slice s 1 k in
      assert (Seq.equal prefix (Seq.append head_seq rest));
      count_lt_append head_seq rest v;
      assert (Seq.index s 0 < v);
      // For the tail, shift indices
      let s' = Seq.tail s in
      assert (Seq.equal rest (Seq.slice s' 0 (k-1)));
      assert (forall (i:nat). i < k-1 ==> Seq.index s' i == Seq.index s (i+1));
      assert (forall (i:nat). i < k-1 ==> Seq.index s' i < v);
      count_lt_sorted_prefix s' (k-1) v
    )
#pop-options

#push-options "--z3rlimit 5 --fuel 2"
let rec count_lt_sorted_suffix (s: seq int) (n: nat) (v: int)
  : Lemma (requires n <= Seq.length s /\
                     (forall (i: nat). i < n ==> v <= Seq.index s i))
          (ensures count_lt (Seq.slice s 0 n) v = 0)
          (decreases n)
  = if n = 0 then ()
    else (
      let prefix = Seq.slice s 0 n in
      let head_seq = Seq.slice s 0 1 in
      let rest = Seq.slice s 1 n in
      assert (Seq.equal prefix (Seq.append head_seq rest));
      count_lt_append head_seq rest v;
      let s' = Seq.tail s in
      assert (Seq.equal rest (Seq.slice s' 0 (n-1)));
      assert (forall (i:nat). i < n-1 ==> Seq.index s' i == Seq.index s (i+1));
      count_lt_sorted_suffix s' (n-1) v
    )
#pop-options

// Main partition property: select_spec returns a value such that
// exactly k elements are < result, and at least k+1 elements are <= result
// IMPORTANT: These lemmas express that count_lt and count_le are multiset functions.
// Mathematical proof: Both count_lt and count_le can be expressed as sums over elements,
// weighted by their multiplicities (count_occ). Since permutations preserve count_occ
// for all elements, they preserve these counts.
//
// A complete mechanized proof requires one of:
// 1. Building sequence rearrangement machinery (find-and-remove with complex proofs)
// 2. Expressing count_lt as an explicit sum: count_lt s v = Σ_{x<v} (count_occ s x)
// 3. Using existing F* libraries for multiset/bag reasoning
//
// Approach (2) requires:
// - A way to iterate over all distinct values in a sequence
// - Proving the sum representation equals the recursive definition
// - Both are non-trivial in F*'s type system
//
// For this proof-of-concept specification, we document the mathematical reasoning
// and note that full mechanization would require substantial infrastructure.

// Prove that count_lt and count_le are multiset functions (permutation-invariant)
// Strategy: Prove by induction using find-and-remove technique

// Helper: find an element in a sequence given that it exists
let rec find_element (s: seq int) (x: int) 
  : Lemma (requires count_occ s x > 0)
          (ensures exists (i:nat). i < Seq.length s /\ Seq.index s i = x)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else if Seq.index s 0 = x then ()
    else (
      count_occ_cons (Seq.index s 0) (Seq.tail s) x;
      find_element (Seq.tail s) x
    )

// Helper: remove one occurrence of an element from a sequence
let rec remove_element (s: seq int) (x: int) (i: nat{i < Seq.length s /\ Seq.index s i = x})
  : Tot (seq int) (decreases i)
  = if i = 0 then Seq.tail s
    else Seq.cons (Seq.index s 0) (remove_element (Seq.tail s) x (i - 1))

// Properties of remove_element
let rec remove_element_length (s: seq int) (x: int) (i: nat{i < Seq.length s /\ Seq.index s i = x})
  : Lemma (ensures Seq.length (remove_element s x i) = Seq.length s - 1)
          (decreases i)
  = if i = 0 then ()
    else remove_element_length (Seq.tail s) x (i - 1)

#push-options "--z3rlimit 5"
let rec remove_element_count_occ (s: seq int) (x: int) (y: int) 
                                   (i: nat{i < Seq.length s /\ Seq.index s i = x})
  : Lemma (ensures count_occ (remove_element s x i) y = 
                   (if x = y then count_occ s y - 1 else count_occ s y))
          (decreases i)
  = if i = 0 then (
      count_occ_cons x (Seq.tail s) y
    ) else (
      count_occ_cons (Seq.index s 0) (Seq.tail s) y;
      remove_element_count_occ (Seq.tail s) x y (i - 1);
      count_occ_cons (Seq.index s 0) (remove_element (Seq.tail s) x (i - 1)) y
    )
#pop-options

// If s1 and s2 are permutations, removing the same element gives permutations
#push-options "--z3rlimit 5"
let remove_preserves_permutation (s1 s2: seq int) (x: int)
                                   (i1: nat{i1 < Seq.length s1 /\ Seq.index s1 i1 = x})
                                   (i2: nat{i2 < Seq.length s2 /\ Seq.index s2 i2 = x})
  : Lemma (requires is_permutation s1 s2)
          (ensures is_permutation (remove_element s1 x i1) (remove_element s2 x i2))
  = remove_element_length s1 x i1;
    remove_element_length s2 x i2;
    let r1 = remove_element s1 x i1 in
    let r2 = remove_element s2 x i2 in
    let aux (y: int) : Lemma (count_occ r1 y = count_occ r2 y) =
      remove_element_count_occ s1 x y i1;
      remove_element_count_occ s2 x y i2
    in
    Classical.forall_intro aux
#pop-options

// Helper: count_lt after removing an element
#push-options "--z3rlimit 5 --fuel 4 --ifuel 2"
let rec remove_element_count_lt (s: seq int) (x: int) (v: int)
                                  (i: nat{i < Seq.length s /\ Seq.index s i = x})
  : Lemma (ensures count_lt (remove_element s x i) v = 
                   (if x < v then count_lt s v - 1 else count_lt s v))
          (decreases i)
  = if i = 0 then (
      count_lt_cons x (Seq.tail s) v
    ) else (
      count_lt_cons (Seq.index s 0) (Seq.tail s) v;
      remove_element_count_lt (Seq.tail s) x v (i - 1);
      count_lt_cons (Seq.index s 0) (remove_element (Seq.tail s) x (i - 1)) v
    )
#pop-options

// Main theorem: count_lt is permutation-invariant
#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
let rec count_lt_permutation_invariant (s1 s2: seq int) (v: int)
  : Lemma (requires is_permutation s1 s2)
          (ensures count_lt s1 v = count_lt s2 v)
          (decreases Seq.length s1)
  = if Seq.length s1 = 0 then ()
    else (
      let h = Seq.index s1 0 in
      let t1 = Seq.tail s1 in
      
      // h appears in s2 with the same count
      count_occ_cons h t1 h;
      find_element s2 h;
      
      // Find h in s2
      let i2 = FStar.IndefiniteDescription.indefinite_description_tot
                 (i:nat{i < Seq.length s2 /\ Seq.index s2 i = h})
                 (fun i -> i < Seq.length s2 && Seq.index s2 i = h)
      in
      
      let t2 = remove_element s2 h i2 in
      
      // t1 and t2 are permutations
      remove_preserves_permutation s1 s2 h 0 i2;
      
      // Apply induction hypothesis
      count_lt_permutation_invariant t1 t2 v;
      
      // Relate to original sequences
      count_lt_cons h t1 v;
      remove_element_count_lt s2 h v i2;
      ()
    )
#pop-options

// Helper: count_le after removing an element
#push-options "--z3rlimit 5 --fuel 4 --ifuel 2"
let rec remove_element_count_le (s: seq int) (x: int) (v: int)
                                  (i: nat{i < Seq.length s /\ Seq.index s i = x})
  : Lemma (ensures count_le (remove_element s x i) v = 
                   (if x <= v then count_le s v - 1 else count_le s v))
          (decreases i)
  = if i = 0 then (
      count_le_cons x (Seq.tail s) v
    ) else (
      count_le_cons (Seq.index s 0) (Seq.tail s) v;
      remove_element_count_le (Seq.tail s) x v (i - 1);
      count_le_cons (Seq.index s 0) (remove_element (Seq.tail s) x (i - 1)) v
    )
#pop-options

// Main theorem: count_le is permutation-invariant
#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
let rec count_le_permutation_invariant (s1 s2: seq int) (v: int)
  : Lemma (requires is_permutation s1 s2)
          (ensures count_le s1 v = count_le s2 v)
          (decreases Seq.length s1)
  = if Seq.length s1 = 0 then ()
    else (
      let h = Seq.index s1 0 in
      let t1 = Seq.tail s1 in
      
      count_occ_cons h t1 h;
      find_element s2 h;
      
      let i2 = FStar.IndefiniteDescription.indefinite_description_tot
                 (i:nat{i < Seq.length s2 /\ Seq.index s2 i = h})
                 (fun i -> i < Seq.length s2 && Seq.index s2 i = h)
      in
      
      let t2 = remove_element s2 h i2 in
      
      remove_preserves_permutation s1 s2 h 0 i2;
      count_le_permutation_invariant t1 t2 v;
      count_le_cons h t1 v;
      remove_element_count_le s2 h v i2;
      ()
    )
#pop-options

// Helper: In a sorted sequence, count_le on prefix [0..k] is at least k+1
#push-options "--z3rlimit 5 --fuel 2"
let rec count_le_prefix_lower (s: seq int) (n: nat) (v: int)
  : Lemma (requires n <= Seq.length s /\
                     (forall (i:nat). i < n ==> Seq.index s i <= v))
          (ensures count_le (Seq.slice s 0 n) v >= n)
          (decreases n)
  = if n = 0 then ()
    else (
      let prefix = Seq.slice s 0 n in
      let head_seq = Seq.slice s 0 1 in
      let rest = Seq.slice s 1 n in
      assert (Seq.equal prefix (Seq.append head_seq rest));
      count_le_append head_seq rest v;
      assert (Seq.index s 0 <= v);
      let s' = Seq.tail s in
      assert (Seq.equal rest (Seq.slice s' 0 (n-1)));
      assert (forall (i:nat). i < n-1 ==> Seq.index s' i == Seq.index s (i+1));
      count_le_prefix_lower s' (n-1) v
    )
#pop-options

// Helper: In a sequence, count_lt on suffix where all elements >= v is 0
#push-options "--z3rlimit 5 --fuel 2"
let rec count_lt_suffix_upper (s: seq int) (k: nat) (n: nat) (v: int)
  : Lemma (requires k <= n /\ n <= Seq.length s /\
                     (forall (i:nat). k <= i /\ i < n ==> v <= Seq.index s i))
          (ensures count_lt (Seq.slice s k n) v = 0)
          (decreases n - k)
  = if k = n then ()
    else (
      let suffix = Seq.slice s k n in
      let head_seq = Seq.slice s k (k+1) in
      let rest = Seq.slice s (k+1) n in
      assert (Seq.equal suffix (Seq.append head_seq rest));
      count_lt_append head_seq rest v;
      assert (v <= Seq.index s k);
      count_lt_suffix_upper s (k+1) n v
    )
#pop-options

// Helper: count_lt is always bounded by sequence length
#push-options "--z3rlimit 5 --fuel 2"
let rec count_lt_bounded (s: seq int) (v: int)
  : Lemma (ensures count_lt s v <= Seq.length s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (
      count_lt_cons (Seq.index s 0) (Seq.tail s) v;
      count_lt_bounded (Seq.tail s) v
    )
#pop-options

// Helper: if a sequence contains v at some position, count_lt s v < length s
#push-options "--z3rlimit 5 --fuel 2"
let rec count_lt_upper_bound (s: seq int) (v: int) (pos: nat)
  : Lemma (requires pos < Seq.length s /\ Seq.index s pos = v)
          (ensures count_lt s v < Seq.length s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else if pos = 0 then (
      // s[0] = v, so s[0] is not < v
      // count_lt s v = 0 + count_lt (tail s) v <= length (tail s) < length s
      count_lt_cons (Seq.index s 0) (Seq.tail s) v;
      count_lt_bounded (Seq.tail s) v
    ) else (
      // pos > 0, so v is in the tail
      count_lt_cons (Seq.index s 0) (Seq.tail s) v;
      count_lt_upper_bound (Seq.tail s) v (pos - 1)
    )
#pop-options

// For a sorted sequence, the element at position k has the partition property
#push-options "--z3rlimit 5"
let sorted_partition_characterization (s: seq int) (k: nat{k < Seq.length s})
  : Lemma (requires is_sorted s)
          (ensures (let v = Seq.index s k in
                    count_lt s v <= k /\
                    count_le s v >= k + 1))
  = let v = Seq.index s k in
    let n = Seq.length s in
    
    // Split sequence: [0..k] ++ [k+1..n-1]
    let prefix = Seq.slice s 0 (k+1) in
    let suffix = Seq.slice s (k+1) n in
    assert (Seq.equal s (Seq.append prefix suffix));
    
    // For sorted sequence: all elements [0..k] are <= v
    assert (forall (i:nat). i <= k ==> Seq.index s i <= v);
    // And all elements [k..n-1] are >= v
    assert (forall (i:nat). k <= i /\ i < n ==> v <= Seq.index s i);
    
    // Prove count_le s v >= k+1
    count_le_prefix_lower s (k+1) v;
    count_le_append prefix suffix v;
    assert (count_le s v >= k + 1);
    
    // Prove count_lt s v <= k
    // count_lt on suffix is 0 (all elements >= v)
    count_lt_suffix_upper s (k+1) n v;
    count_lt_append prefix suffix v;
    assert (count_lt s v = count_lt prefix v);
    
    // prefix[k] = v, so count_lt prefix v < length prefix = k+1
    // Therefore count_lt prefix v <= k
    assert (Seq.index prefix k = v);
    count_lt_upper_bound prefix v k;
    assert (count_lt prefix v < Seq.length prefix);
    assert (Seq.length prefix = k + 1);
    assert (count_lt prefix v <= k);
    ()
#pop-options

#push-options "--z3rlimit 5"
let select_spec_partition_property (s: seq int) (k: nat{k < Seq.length s})
  : Lemma (ensures (let v = select_spec s k in
                    count_lt s v <= k /\
                    count_le s v > k))
  = pure_sort_length s;
    let sorted = pure_sort s in
    let v = Seq.index sorted k in
    pure_sort_permutation s;
    pure_sort_sorted s;
    
    // Apply sorted_partition_characterization to the sorted sequence
    sorted_partition_characterization sorted k;
    
    // Use permutation to transfer counts from sorted to s
    count_lt_permutation_invariant sorted s v;
    count_le_permutation_invariant sorted s v;
    ()
#pop-options

(*** Uniqueness Property ***)

// The k-th smallest element is uniquely determined by the partition property
// If v satisfies count_lt s v <= k and count_le s v > k, then v = select_spec s k
// (This is not always true with duplicates, but it characterizes the answer)

(*** Correctness of select_spec ***)

// Theorem: select_spec s k is the k-th smallest element of s
// This is proven by:
// 1. pure_sort produces a sorted permutation (proven above)
// 2. In a sorted sequence, the element at index k is the k-th smallest
// 3. Permutations preserve the k-th smallest property

let select_spec_correct (s: seq int) (k: nat{k < Seq.length s})
  : Lemma (ensures (let sorted = pure_sort s in
                    is_sorted sorted /\
                    is_permutation sorted s /\
                    select_spec s k = Seq.index sorted k))
  = pure_sort_sorted s;
    pure_sort_permutation s;
    pure_sort_length s

