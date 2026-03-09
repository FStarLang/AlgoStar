module CLRS.Ch12.BSTArray.Lemmas

(**
 * Unified Array-Based BST Lemmas
 *
 * Re-exports the key correctness lemmas from the component modules:
 *   - Predicates: well_formed_bst, subtree_in_range, frame lemmas,
 *                 insert/delete preservation
 *   - Refinement: array_to_bst abstraction, inorder/validity/search
 *                 refinement proofs
 *
 * CLRS Reference: §12.1–12.3
 *)

open FStar.Seq
open FStar.Classical
open FStar.Mul
open CLRS.Ch12.BST.Spec
open CLRS.Ch12.BSTArray.Predicates
open CLRS.Ch12.BSTArray.Refinement

(* ========================================================================
   § 1. Validity Refinement (from Refinement)
   
   well_formed_bst on the array representation implies bst_valid on the
   abstracted inductive BST.
   ======================================================================== *)

//SNIPPET_START: valid_refinement
let valid_refinement
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat)
  (lo hi: int)
  : Lemma
    (requires well_formed_bst keys valid cap i lo hi)
    (ensures bst_valid (array_to_bst keys valid cap i))
  = lemma_valid_refinement keys valid cap i lo hi
//SNIPPET_END: valid_refinement

(* ========================================================================
   § 2. Search Refinement (from Refinement)
   
   key_in_subtree ⟺ bst_search (array_to_bst ...) under BST range invariant.
   ======================================================================== *)

//SNIPPET_START: search_refinement
let search_refinement
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat)
  (lo hi: int) (k: int)
  : Lemma
    (requires
      subtree_in_range keys valid cap i lo hi /\
      lo < k /\ k < hi)
    (ensures
      key_in_subtree keys valid cap i k <==>
      bst_search (array_to_bst keys valid cap i) k)
  = lemma_search_refinement keys valid cap i lo hi k
//SNIPPET_END: search_refinement

(* ========================================================================
   § 3. Inorder Refinement (from Refinement)
   
   inorder_spec on the array equals bst_inorder on the abstraction.
   ======================================================================== *)

let inorder_refinement
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat)
  : Lemma
    (requires cap <= length keys /\ cap <= length valid)
    (ensures
      inorder_spec keys valid cap i ==
      bst_inorder (array_to_bst keys valid cap i))
  = lemma_inorder_refinement keys valid cap i

(* ========================================================================
   § 4. well_formed_bst implies subtree_in_range (from Predicates)
   ======================================================================== *)

let well_formed_implies_sir
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat) (lo hi: int)
  : Lemma
    (requires well_formed_bst keys valid cap i lo hi)
    (ensures subtree_in_range keys valid cap i lo hi)
  = lemma_well_formed_implies_sir keys valid cap i lo hi
