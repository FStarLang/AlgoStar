module CLRS.Ch12.BSTArray.Lemmas

(**
 * Interface: Unified Array-Based BST Lemmas
 *
 * Key correctness lemmas for array-backed BSTs:
 *   - Validity refinement: well_formed_bst ⟹ bst_valid on abstraction
 *   - Search refinement: key_in_subtree ⟺ bst_search on abstraction
 *   - Inorder refinement: array inorder = inductive inorder
 *   - well_formed_bst ⟹ subtree_in_range
 *
 * CLRS Reference: §12.1–12.3
 *)

open FStar.Seq
open CLRS.Ch12.BST.Spec
open CLRS.Ch12.BSTArray.Predicates
open CLRS.Ch12.BSTArray.Refinement

(** Validity refinement: well_formed_bst implies bst_valid on abstraction *)
val valid_refinement:
  keys:seq int -> valid:seq bool -> cap:nat -> i:nat -> lo:int -> hi:int ->
  Lemma (requires well_formed_bst keys valid cap i lo hi)
        (ensures bst_valid (array_to_bst keys valid cap i))

(** Search refinement: key_in_subtree ⟺ bst_search (array_to_bst ...) *)
val search_refinement:
  keys:seq int -> valid:seq bool -> cap:nat -> i:nat ->
  lo:int -> hi:int -> k:int ->
  Lemma (requires subtree_in_range keys valid cap i lo hi /\
                  lo < k /\ k < hi)
        (ensures key_in_subtree keys valid cap i k <==>
                 bst_search (array_to_bst keys valid cap i) k)

(** Inorder refinement: array inorder_spec = bst_inorder on abstraction *)
val inorder_refinement:
  keys:seq int -> valid:seq bool -> cap:nat -> i:nat ->
  Lemma (requires cap <= length keys /\ cap <= length valid)
        (ensures inorder_spec keys valid cap i ==
                 bst_inorder (array_to_bst keys valid cap i))

(** well_formed_bst implies the weaker subtree_in_range *)
val well_formed_implies_sir:
  keys:seq int -> valid:seq bool -> cap:nat -> i:nat -> lo:int -> hi:int ->
  Lemma (requires well_formed_bst keys valid cap i lo hi)
        (ensures subtree_in_range keys valid cap i lo hi)
