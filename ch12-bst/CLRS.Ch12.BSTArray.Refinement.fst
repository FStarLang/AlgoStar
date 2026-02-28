module CLRS.Ch12.BSTArray.Refinement

(**
 * Refinement proof: the array-based BST operations refine
 * the pure inductive BST specification.
 *
 * Defines an abstraction function [array_to_bst] from the array
 * representation to the inductive BST type and proves:
 *   1. Inorder traversal is preserved
 *   2. well_formed_bst ⟹ bst_valid on the abstraction
 *   3. key_in_subtree ⟺ bst_search on the abstraction (under BST property)
 *)

open FStar.List.Tot.Base   // for @ (list append)
open FStar.Seq             // for Seq.length, Seq.index  (shadows List length/index)
open FStar.Mul             // for *
open FStar.Classical
open CLRS.Ch12.BST.Spec.Complete
open CLRS.Ch12.BSTArray.Predicates

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"

(* =========================================================================
   § 1. Abstraction Function: array representation → inductive BST
   ========================================================================= *)

let rec array_to_bst (keys: seq int) (valid: seq bool) (cap: nat) (i: nat)
  : Tot bst (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then Leaf
    else if not (index valid i) then Leaf
    else Node (array_to_bst keys valid cap (2 * i + 1))
              (index keys i)
              (array_to_bst keys valid cap (2 * i + 2))

(* =========================================================================
   § 2. Inorder Refinement
   ========================================================================= *)

/// Local copy of inorder_spec — identical to the definition in
/// CLRS.Ch12.BST (the Pulse module), which cannot be directly imported
/// into a pure F* module.
let rec inorder_spec (keys: seq int) (valid: seq bool) (cap: nat) (i: nat)
  : Tot (list int) (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then []
    else if not (index valid i) then []
    else inorder_spec keys valid cap (2 * i + 1) @
         [index keys i] @
         inorder_spec keys valid cap (2 * i + 2)

/// The inorder traversal of the abstracted tree equals inorder_spec.
let rec lemma_inorder_refinement
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat)
  : Lemma (ensures bst_inorder (array_to_bst keys valid cap i) == inorder_spec keys valid cap i)
          (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then ()
    else if not (index valid i) then ()
    else begin
      lemma_inorder_refinement keys valid cap (2 * i + 1);
      lemma_inorder_refinement keys valid cap (2 * i + 2)
    end

(* =========================================================================
   § 3. Validity Refinement
   ========================================================================= *)

/// Helper: [all] distributes over list append.
let rec lemma_all_append (p: int -> bool) (xs ys: list int)
  : Lemma (all p (xs @ ys) <==> (all p xs && all p ys))
  = match xs with
  | [] -> ()
  | _ :: xs' -> lemma_all_append p xs' ys

/// Helper: if all elements satisfy (lo < · ∧ · < hi), then all_less k
/// whenever hi ≤ k.
let rec lemma_bounded_implies_all_less (lo hi k: int) (xs: list int)
  : Lemma (requires all (fun x -> lo < x && x < hi) xs /\ hi <= k)
          (ensures  all_less k xs == true)
  = match xs with
  | [] -> ()
  | _ :: xs' -> lemma_bounded_implies_all_less lo hi k xs'

/// Helper: if all elements satisfy (lo < · ∧ · < hi), then all_greater k
/// whenever k ≤ lo.
let rec lemma_bounded_implies_all_greater (lo hi k: int) (xs: list int)
  : Lemma (requires all (fun x -> lo < x && x < hi) xs /\ k <= lo)
          (ensures  all_greater k xs == true)
  = match xs with
  | [] -> ()
  | _ :: xs' -> lemma_bounded_implies_all_greater lo hi k xs'

/// Helper: if all elements satisfy (lo < · ∧ · < k) then they also
/// satisfy (lo < · ∧ · < hi) when k ≤ hi.
let rec lemma_widen_upper (lo k hi: int) (xs: list int)
  : Lemma (requires all (fun x -> lo < x && x < k) xs /\ k <= hi)
          (ensures  all (fun x -> lo < x && x < hi) xs == true)
  = match xs with
  | [] -> ()
  | _ :: xs' -> lemma_widen_upper lo k hi xs'

/// Helper: if all elements satisfy (k < · ∧ · < hi) then they also
/// satisfy (lo < · ∧ · < hi) when lo ≤ k.
let rec lemma_widen_lower (lo k hi: int) (xs: list int)
  : Lemma (requires all (fun x -> k < x && x < hi) xs /\ lo <= k)
          (ensures  all (fun x -> lo < x && x < hi) xs == true)
  = match xs with
  | [] -> ()
  | _ :: xs' -> lemma_widen_lower lo k hi xs'

/// Key helper: well_formed_bst implies all keys in the abstracted tree
/// are strictly between lo and hi.
let rec lemma_wfb_keys_bounded
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat) (lo hi: int)
  : Lemma (requires well_formed_bst keys valid cap i lo hi)
          (ensures  all (fun x -> lo < x && x < hi) (bst_inorder (array_to_bst keys valid cap i)))
          (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then ()
    else if not (index valid i) then ()
    else begin
      let k = index keys i in
      let left = 2 * i + 1 in
      let right = 2 * i + 2 in
      // From well_formed_bst: lo < k < hi,
      //   well_formed_bst keys valid cap left lo k,
      //   well_formed_bst keys valid cap right k hi
      lemma_wfb_keys_bounded keys valid cap left lo k;
      lemma_wfb_keys_bounded keys valid cap right k hi;
      // Left subtree: all x in left satisfy lo < x < k
      // Widen upper bound: k <= hi, so lo < x < k ==> lo < x < hi
      let left_inorder = bst_inorder (array_to_bst keys valid cap left) in
      let right_inorder = bst_inorder (array_to_bst keys valid cap right) in
      lemma_widen_upper lo k hi left_inorder;
      // Right subtree: all x in right satisfy k < x < hi
      // Widen lower bound: lo <= k, so k < x < hi ==> lo < x < hi
      lemma_widen_lower lo k hi right_inorder;
      // Root key k satisfies lo < k < hi
      assert (all (fun x -> lo < x && x < hi) [k]);
      // Combine: all over (left_inorder @ [k] @ right_inorder)
      lemma_all_append (fun x -> lo < x && x < hi) left_inorder ([k] @ right_inorder);
      lemma_all_append (fun x -> lo < x && x < hi) [k] right_inorder
    end

/// well_formed_bst implies bst_valid on the abstracted tree.
let rec lemma_valid_refinement
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat) (lo hi: int)
  : Lemma (requires well_formed_bst keys valid cap i lo hi)
          (ensures  bst_valid (array_to_bst keys valid cap i))
          (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then ()
    else if not (index valid i) then ()
    else begin
      let k = index keys i in
      let left = 2 * i + 1 in
      let right = 2 * i + 2 in
      let left_tree  = array_to_bst keys valid cap left in
      let right_tree = array_to_bst keys valid cap right in
      // Recursive validity
      lemma_valid_refinement keys valid cap left lo k;
      lemma_valid_refinement keys valid cap right k hi;
      // Establish all_less k (bst_inorder left_tree):
      //   All elements in left satisfy lo < x < k, hence x < k
      lemma_wfb_keys_bounded keys valid cap left lo k;
      lemma_bounded_implies_all_less lo k k (bst_inorder left_tree);
      // Establish all_greater k (bst_inorder right_tree):
      //   All elements in right satisfy k < x < hi, hence x > k
      lemma_wfb_keys_bounded keys valid cap right k hi;
      lemma_bounded_implies_all_greater k hi k (bst_inorder right_tree)
    end

(* =========================================================================
   § 4. Search Refinement
   ========================================================================= *)

/// Backward direction: bst_search finding a key implies key_in_subtree.
/// No BST property needed — if the search algorithm returns true,
/// the key genuinely exists in the tree.
let rec lemma_search_backward
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat) (key: int)
  : Lemma (requires bst_search (array_to_bst keys valid cap i) key)
          (ensures  key_in_subtree keys valid cap i key)
          (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then ()
    else if not (index valid i) then ()
    else begin
      let k = index keys i in
      if key = k then ()
      else if key < k then
        lemma_search_backward keys valid cap (2 * i + 1) key
      else
        lemma_search_backward keys valid cap (2 * i + 2) key
    end

/// Forward direction: key_in_subtree implies bst_search, given the BST
/// property (subtree_in_range).  Without the BST property, key_in_subtree
/// explores both children while bst_search follows only one branch.
let rec lemma_search_forward
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat) (lo hi: int) (key: int)
  : Lemma
    (requires subtree_in_range keys valid cap i lo hi /\
              key_in_subtree keys valid cap i key /\
              lo < key /\ key < hi)
    (ensures  bst_search (array_to_bst keys valid cap i) key == true)
    (decreases (if i < cap then cap - i else 0))
  = let k = index keys i in
    let left = 2 * i + 1 in
    let right = 2 * i + 2 in
    if key = k then ()
    else if key < k then begin
      // key < k, so bst_search goes left.
      // Need: key_in_subtree ... left key
      // We know key_in_subtree ... i key, which is:
      //   k == key  \/  key_in_subtree ... left key  \/  key_in_subtree ... right key
      // k == key is ruled out (key <> k).
      // key_in_subtree ... right key is ruled out because subtree_in_range
      // on right gives k < x for all x, but key < k.
      or_elim
        #(key_in_subtree keys valid cap left key)
        #(key_in_subtree keys valid cap right key)
        #(fun _ -> bst_search (array_to_bst keys valid cap i) key == true)
        (fun _ -> lemma_search_forward keys valid cap left lo k key)
        (fun _ -> lemma_key_in_bounded_subtree keys valid cap right k hi key)
    end else begin
      // key > k, so bst_search goes right.
      // key_in_subtree ... left key is ruled out because subtree_in_range
      // on left gives x < k for all x, but key > k.
      or_elim
        #(key_in_subtree keys valid cap left key)
        #(key_in_subtree keys valid cap right key)
        #(fun _ -> bst_search (array_to_bst keys valid cap i) key == true)
        (fun _ -> lemma_key_in_bounded_subtree keys valid cap left lo k key)
        (fun _ -> lemma_search_forward keys valid cap right k hi key)
    end

/// Combined search refinement:
///   key_in_subtree ⟺ bst_search (array_to_bst ...)
/// under the BST range invariant.
let lemma_search_refinement
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat) (lo hi: int) (key: int)
  : Lemma
    (requires subtree_in_range keys valid cap i lo hi /\ lo < key /\ key < hi)
    (ensures  key_in_subtree keys valid cap i key <==>
              bst_search (array_to_bst keys valid cap i) key)
  = introduce key_in_subtree keys valid cap i key ==>
              bst_search (array_to_bst keys valid cap i) key == true
    with _h. lemma_search_forward keys valid cap i lo hi key;
    introduce bst_search (array_to_bst keys valid cap i) key == true ==>
              key_in_subtree keys valid cap i key
    with _h. lemma_search_backward keys valid cap i key

#pop-options
