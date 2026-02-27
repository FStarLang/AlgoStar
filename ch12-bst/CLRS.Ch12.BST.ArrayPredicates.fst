module CLRS.Ch12.BST.ArrayPredicates

(**
 * Shared array-based BST predicates and lemmas
 *
 * Used by both the Pulse implementation (CLRS.Ch12.BST) and the
 * pure search specification (CLRS.Ch12.BST.Spec).
 *)

open FStar.Seq
open FStar.Classical
open FStar.Mul

// Helper lemma to prove that child indices fit in SZ.t
let child_indices_fit (cap: nat) (i: nat)
  : Lemma
    (requires cap < 32768 /\ i < cap)
    (ensures (
      let left = 2 * i + 1 in
      let right = 2 * i + 2 in
      0 <= left /\ left < pow2 16 /\
      0 <= right /\ right < pow2 16
    ))
  = assert_norm (pow2 16 = 65536)

// Stronger BST property: all keys in subtree are bounded by lo and hi
let rec subtree_in_range 
  (keys: seq int) 
  (valid: seq bool) 
  (cap: nat) 
  (i: nat) 
  (lo hi: int)
  : Tot prop (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then True
    else if not (index valid i) then True
    else 
      let k = index keys i in
      let left = 2 * i + 1 in
      let right = 2 * i + 2 in
      lo < k /\ k < hi /\
      subtree_in_range keys valid cap left lo k /\
      subtree_in_range keys valid cap right k hi

// Key membership in subtree rooted at i
let rec key_in_subtree 
  (keys: seq int) 
  (valid: seq bool) 
  (cap: nat) 
  (i: nat) 
  (key: int)
  : Tot prop (decreases (if i < cap then cap - i else 0))
  = i < cap /\ i < length keys /\ i < length valid /\
    index valid i /\
    (index keys i == key \/
     key_in_subtree keys valid cap (2 * i + 1) key \/
     key_in_subtree keys valid cap (2 * i + 2) key)

// Lemma: If key is in a bounded subtree, it must be within the bounds
let rec lemma_key_in_bounded_subtree
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma 
    (requires subtree_in_range keys valid cap i lo hi /\ key_in_subtree keys valid cap i key)
    (ensures lo < key /\ key < hi)
    (decreases (if i < cap then cap - i else 0))
  = let left = 2 * i + 1 in
    let right = 2 * i + 2 in
    or_elim
      #(key_in_subtree keys valid cap left key)
      #(key_in_subtree keys valid cap right key)
      #(fun _ -> lo < key /\ key < hi)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap left lo (index keys i) key)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap right (index keys i) hi key)

// Lemma: If key < current_key and BST property holds, key can only be in left subtree
[@@"opaque_to_smt"]
let lemma_key_not_in_right_if_less
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma
    (requires 
      subtree_in_range keys valid cap i lo hi /\
      i < cap /\ i < length keys /\ i < length valid /\
      index valid i /\
      key < index keys i /\
      key_in_subtree keys valid cap i key)
    (ensures key_in_subtree keys valid cap (2 * i + 1) key)
  = let k = index keys i in
    let right = 2 * i + 2 in
    or_elim
      #(key_in_subtree keys valid cap right key)
      #(~(key_in_subtree keys valid cap right key))
      #(fun _ -> key_in_subtree keys valid cap (2 * i + 1) key)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap right k hi key)
      (fun _ -> ())

// Lemma: If key > current_key and BST property holds, key can only be in right subtree  
[@@"opaque_to_smt"]
let lemma_key_not_in_left_if_greater
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma
    (requires 
      subtree_in_range keys valid cap i lo hi /\
      i < cap /\ i < length keys /\ i < length valid /\
      index valid i /\
      key > index keys i /\
      key_in_subtree keys valid cap i key)
    (ensures key_in_subtree keys valid cap (2 * i + 2) key)
  = let k = index keys i in
    let left = 2 * i + 1 in
    or_elim
      #(key_in_subtree keys valid cap left key)
      #(~(key_in_subtree keys valid cap left key))
      #(fun _ -> key_in_subtree keys valid cap (2 * i + 2) key)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap left lo k key)
      (fun _ -> ())
