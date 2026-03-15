module CLRS.Ch12.BST.Impl
(**
 * Interface: Pointer-Based Binary Search Tree (Pulse Implementation)
 *
 * Public types, separation logic predicate, and operation signatures
 * for the pointer-based BST following CLRS §12.1–12.3.
 *
 * Each operation takes a ghost tick counter (GR.ref nat) and its
 * postcondition links the tick increment to the complexity functions
 * in CLRS.Ch12.BST.Complexity, establishing O(h) bounds.
 *)
#lang-pulse
open Pulse.Lib.Pervasives

module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module GR = Pulse.Lib.GhostReference

open CLRS.Ch12.BST.Spec
open CLRS.Ch12.BST.Complexity

// ============================================================
// §12.1 Node type
// ============================================================

noeq
type bst_node = {
  key:   int;
  left:  bst_ptr;
  right: bst_ptr;
  p:     bst_ptr;     // parent pointer (CLRS §12.1)
}

and bst_node_ptr = box bst_node

// Nullable pointer to a node
and bst_ptr = option bst_node_ptr

// ============================================================
// Separation logic predicate: bst_subtree
//
// `bst_subtree ct ft parent` asserts that:
//   - `ct` is the concrete pointer to the root of the subtree
//   - `ft` is the ghost/pure BST shape
//   - `parent` is the expected parent-pointer value for the root
// ============================================================

let rec bst_subtree (ct: bst_ptr) (ft: bst) (parent: bst_ptr)
  : Tot slprop (decreases ft)
  = match ft with
    | Leaf -> pure (ct == None)
    | Node l k r ->
      exists* (bp: bst_node_ptr) (node: bst_node).
        pure (ct == Some bp) **
        (bp |-> node) **
        pure (node.key == k /\ node.p == parent) **
        bst_subtree node.left l (Some bp) **
        bst_subtree node.right r (Some bp)

// ============================================================
// Public Operations — each takes a ghost tick counter
// ============================================================

(** TREE-SEARCH (§12.2): recursive BST search, O(h)
    Postcondition: ticks incremented by bst_search_ticks 'ft k *)
fn rec tree_search (tree: bst_ptr) (k: int) (ticks: GR.ref nat)
  preserves bst_subtree tree 'ft 'parent
  requires GR.pts_to ticks 'n
  returns result: bool
  ensures GR.pts_to ticks ('n + bst_search_ticks 'ft k) **
          pure (result == bst_search 'ft k)

(** TREE-MINIMUM (§12.2): find the minimum key, O(h)
    Postcondition: ticks incremented by bst_minimum_ticks 'ft *)
fn rec tree_minimum (tree: bst_ptr) (bp: bst_node_ptr) (ticks: GR.ref nat)
  preserves bst_subtree tree 'ft 'parent
  requires GR.pts_to ticks 'n ** pure (tree == Some bp)
  returns result: int
  ensures GR.pts_to ticks ('n + bst_minimum_ticks 'ft) **
          pure (bst_minimum 'ft == Some result)

(** TREE-MAXIMUM (§12.2): find the maximum key, O(h)
    Postcondition: ticks incremented by bst_maximum_ticks 'ft *)
fn rec tree_maximum (tree: bst_ptr) (bp: bst_node_ptr) (ticks: GR.ref nat)
  preserves bst_subtree tree 'ft 'parent
  requires GR.pts_to ticks 'n ** pure (tree == Some bp)
  returns result: int
  ensures GR.pts_to ticks ('n + bst_maximum_ticks 'ft) **
          pure (bst_maximum 'ft == Some result)

(** TREE-INSERT (§12.3): recursive insert with parent-pointer maintenance, O(h)
    Postcondition: ticks incremented by bst_insert_ticks 'ft k
    Validity: bst_valid is preserved (addresses Review limitation 1) *)
fn rec tree_insert (tree: bst_ptr) (k: int) (parent: bst_ptr) (ticks: GR.ref nat)
  requires bst_subtree tree 'ft parent ** GR.pts_to ticks 'n
  returns y: bst_ptr
  ensures bst_subtree y (bst_insert 'ft k) parent **
          GR.pts_to ticks ('n + bst_insert_ticks 'ft k) **
          pure (bst_valid 'ft ==> bst_valid (bst_insert 'ft k))

(** TREE-DELETE (§12.3): recursive key-based deletion, O(h)
    Postcondition: ticks incremented by bst_delete_ticks 'ft k
    Validity: bst_valid is preserved (addresses Review limitation 1) *)
fn rec tree_delete (tree: bst_ptr) (k: int) (parent: bst_ptr) (ticks: GR.ref nat)
  requires bst_subtree tree 'ft parent ** GR.pts_to ticks 'n
  returns result: bst_ptr
  ensures bst_subtree result (bst_delete 'ft k) parent **
          GR.pts_to ticks ('n + bst_delete_ticks 'ft k) **
          pure (bst_valid 'ft ==> bst_valid (bst_delete 'ft k))

(** TREE-FREE: recursive deallocation of all nodes *)
fn rec free_bst (tree: bst_ptr)
  requires bst_subtree tree 'ft 'parent
  ensures emp
