module CLRS.Ch12.BST.Impl
(**
 * Interface: Pointer-Based Binary Search Tree (Pulse Implementation)
 *
 * Public types, separation logic predicate, and operation signatures
 * for the pointer-based BST following CLRS §12.1–12.3.
 *
 * Each operation's postcondition links to the pure functional spec
 * in CLRS.Ch12.BST.Spec.
 *)
#lang-pulse
open Pulse.Lib.Pervasives

module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }

open CLRS.Ch12.BST.Spec

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
// Public Operations
// ============================================================

(** TREE-SEARCH (§12.2): recursive BST search, O(h) *)
fn rec tree_search (tree: bst_ptr) (k: int)
  preserves bst_subtree tree 'ft 'parent
  returns result: bool
  ensures pure (result == bst_search 'ft k)

(** TREE-MINIMUM (§12.2): find the minimum key *)
fn rec tree_minimum (tree: bst_ptr) (bp: bst_node_ptr)
  preserves bst_subtree tree 'ft 'parent
  requires pure (tree == Some bp)
  returns result: int
  ensures pure (bst_minimum 'ft == Some result)

(** TREE-MAXIMUM (§12.2): find the maximum key *)
fn rec tree_maximum (tree: bst_ptr) (bp: bst_node_ptr)
  preserves bst_subtree tree 'ft 'parent
  requires pure (tree == Some bp)
  returns result: int
  ensures pure (bst_maximum 'ft == Some result)

(** TREE-INSERT (§12.3): recursive insert with parent-pointer maintenance *)
fn rec tree_insert (tree: bst_ptr) (k: int) (parent: bst_ptr)
  requires bst_subtree tree 'ft parent
  returns y: bst_ptr
  ensures bst_subtree y (bst_insert 'ft k) parent

(** TREE-DELETE (§12.3): recursive key-based deletion *)
fn rec tree_delete (tree: bst_ptr) (k: int) (parent: bst_ptr)
  requires bst_subtree tree 'ft parent
  returns result: bst_ptr
  ensures bst_subtree result (bst_delete 'ft k) parent

(** TREE-FREE: recursive deallocation of all nodes *)
fn rec free_bst (tree: bst_ptr)
  requires bst_subtree tree 'ft 'parent
  ensures emp
