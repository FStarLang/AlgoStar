(*
   CLRS Chapter 13: Red-Black Trees — Public interface for CLRS-faithful Pulse implementation

   Exposes the CLRS parent-pointer red-black tree API:
   - Node type (with parent pointer) and pointer definitions
   - Separation-logic predicates (rbtree_subtree, valid_rbtree)
   - Low-level API: rb_search, rb_minimum, rb_clrs_insert, rb_clrs_delete, free_rbtree
   - Validated API: rb_new, rb_search_v, rb_insert_v, rb_delete_v, free_valid_rbtree
   - Complexity-aware API: rb_search_log, rb_clrs_insert_log, rb_clrs_delete_log

   Internal helpers (fixup, resolve, cases234, set_parent_ptr, etc.) are hidden.
*)
module CLRS.Ch13.RBTree.CLRSImpl
#lang-pulse
open Pulse.Lib.Pervasives

module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }

module S = CLRS.Ch13.RBTree.Spec
module CS = CLRS.Ch13.RBTree.CLRSSpec
module G = FStar.Ghost
module C = CLRS.Ch13.RBTree.Complexity
module CC = CLRS.Ch13.RBTree.CLRSComplexity

// ========== Node type and pointers ==========

noeq
type rb_node = {
  key:   int;
  color: S.color;
  left:  rb_ptr;
  right: rb_ptr;
  p:     rb_ptr;     // parent pointer (CLRS §12.1)
}

and rb_node_ptr = box rb_node

and rb_ptr = option rb_node_ptr

// ========== Separation logic predicates ==========

let rec rbtree_subtree (ct: rb_ptr) (ft: S.rbtree) (parent: rb_ptr)
  : Tot slprop (decreases ft)
  = match ft with
    | S.Leaf -> pure (ct == None)
    | S.Node c l v r ->
      exists* (bp: rb_node_ptr) (node: rb_node).
        pure (ct == Some bp) **
        (bp |-> node) **
        pure (node.key == v /\ node.color == c /\ node.p == parent) **
        rbtree_subtree node.left l (Some bp) **
        rbtree_subtree node.right r (Some bp)

let valid_rbtree (ct: rb_ptr) (ft: S.rbtree) (parent: rb_ptr) : slprop =
  rbtree_subtree ct ft parent ** pure (S.is_rbtree ft /\ S.is_bst ft)

// ========== Low-level API (uses rbtree_subtree directly) ==========

fn rb_search (tree: rb_ptr) (k: int)
  preserves rbtree_subtree tree 'ft 'parent
  returns result: option int
  ensures pure (result == S.search 'ft k)

fn rb_minimum (tree: rb_ptr) (bp: rb_node_ptr)
  preserves rbtree_subtree tree 'ft 'parent
  requires pure (tree == Some bp)
  returns result: int
  ensures pure (S.Node? 'ft /\ result == S.minimum 'ft)

fn rb_clrs_insert (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft parent
  returns y: rb_ptr
  ensures rbtree_subtree y (CS.clrs_insert 'ft k) parent

fn rb_clrs_delete (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft 'old_parent
  returns y: rb_ptr
  ensures rbtree_subtree y (CS.clrs_delete 'ft k) parent

fn free_rbtree (tree: rb_ptr)
  requires rbtree_subtree tree 'ft 'parent
  ensures emp

// ========== Validated API (uses valid_rbtree — bundles invariants) ==========

fn rb_new ()
  requires emp
  returns y: rb_ptr
  ensures valid_rbtree y S.Leaf (None #rb_node_ptr)

fn rb_search_v (tree: rb_ptr) (k: int)
  (#parent: G.erased rb_ptr)
  preserves valid_rbtree tree 'ft parent
  returns result: option int
  ensures pure (result == S.search 'ft k)

fn rb_insert_v (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires valid_rbtree tree 'ft parent
  returns y: rb_ptr
  ensures valid_rbtree y (CS.clrs_insert 'ft k) parent **
          pure (S.mem k (CS.clrs_insert 'ft k) = true)

fn rb_delete_v (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires valid_rbtree tree 'ft parent
  returns y: rb_ptr
  ensures valid_rbtree y (CS.clrs_delete 'ft k) parent **
          pure (S.mem k (CS.clrs_delete 'ft k) = false)

fn free_valid_rbtree (tree: rb_ptr)
  requires valid_rbtree tree 'ft 'parent
  ensures emp

// ========== Complexity-aware API ==========

fn rb_search_log (tree: rb_ptr) (k: int)
  (#parent: G.erased rb_ptr)
  preserves valid_rbtree tree 'ft parent
  returns result: option int
  ensures pure (result == S.search 'ft k /\
                C.search_ticks 'ft k <= S.height 'ft + 1)

fn rb_clrs_insert_log (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires valid_rbtree tree 'ft parent
  returns y: rb_ptr
  ensures valid_rbtree y (CS.clrs_insert 'ft k) parent **
          pure (S.mem k (CS.clrs_insert 'ft k) = true /\
                CC.clrs_insert_ticks 'ft k <= S.height 'ft + 2)

fn rb_clrs_delete_log (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires valid_rbtree tree 'ft parent
  returns y: rb_ptr
  ensures valid_rbtree y (CS.clrs_delete 'ft k) parent **
          pure (S.mem k (CS.clrs_delete 'ft k) = false /\
                CC.clrs_delete_ticks 'ft k <= 2 * S.height 'ft + 2)
