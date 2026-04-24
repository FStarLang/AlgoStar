(*
   CLRS Chapter 13: Red-Black Trees — Public interface for Pulse implementation

   Exposes the Okasaki-style verified red-black tree API:
   - Node type and pointer definitions
   - Separation-logic predicates (is_rbtree, valid_rbtree)
   - Validated API: rb_new, rb_search_v, rb_insert_v, rb_delete_v, free_valid_rbtree
   - Complexity-aware API: rb_search_log, rb_insert_log, rb_delete_log
   - Low-level API: rb_search, rb_insert, rb_delete, free_rbtree

   Internal helpers (balance_ll, classify_runtime, etc.) are hidden.
*)
module CLRS.Ch13.RBTree.Impl
#lang-pulse
open Pulse.Lib.Pervasives

module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }

module S = CLRS.Ch13.RBTree.Spec
module L = CLRS.Ch13.RBTree.Lemmas
module G = FStar.Ghost
module C = CLRS.Ch13.RBTree.Complexity

// ========== Node type and pointers ==========

noeq
type rb_node = {
  key:   int;
  color: S.color;
  left:  rb_ptr;
  right: rb_ptr;
}

and rb_node_ptr = box rb_node

and rb_ptr = option rb_node_ptr

// ========== Separation logic predicates ==========

let rec is_rbtree (ct: rb_ptr) (ft: S.rbtree)
  : Tot slprop (decreases ft)
  = match ft with
    | S.Leaf -> pure (ct == None)
    | S.Node c l v r ->
      exists* (p: rb_node_ptr) (lct: rb_ptr) (rct: rb_ptr).
        pure (ct == Some p) **
        (p |-> { key = v; color = c; left = lct; right = rct }) **
        is_rbtree lct l **
        is_rbtree rct r

let valid_rbtree (ct: rb_ptr) (ft: S.rbtree) : slprop =
  is_rbtree ct ft ** pure (S.is_rbtree ft /\ S.is_bst ft)

// ========== Low-level API (uses is_rbtree slprop directly) ==========

fn rb_search (tree: rb_ptr) (k: int)
  preserves is_rbtree tree 'ft
  returns result: option int
  ensures pure (result == S.search 'ft k)

fn rb_insert (tree: rb_ptr) (k: int)
  requires is_rbtree tree 'ft
  returns y: rb_ptr
  ensures is_rbtree y (S.insert 'ft k)

fn rb_delete (tree: rb_ptr) (k: int)
  requires is_rbtree tree 'ft
  returns y: rb_ptr
  ensures is_rbtree y (S.delete 'ft k)

fn free_rbtree (tree: rb_ptr)
  requires is_rbtree tree 'ft
  ensures emp

// ========== Validated API (uses valid_rbtree slprop — bundles invariants) ==========

fn rb_new ()
  requires emp
  returns y: rb_ptr
  ensures valid_rbtree y S.Leaf

fn rb_search_v (tree: rb_ptr) (k: int)
  preserves valid_rbtree tree 'ft
  returns result: option int
  ensures pure (result == S.search 'ft k /\
                (S.mem k 'ft ==> result == Some k) /\
                (~(S.mem k 'ft) ==> result == None))

fn rb_insert_v (tree: rb_ptr) (k: int)
  requires valid_rbtree tree 'ft
  returns y: rb_ptr
  ensures valid_rbtree y (S.insert 'ft k) **
          pure (S.mem k (S.insert 'ft k) = true /\
                S.search (S.insert 'ft k) k == Some k)

fn rb_delete_v (tree: rb_ptr) (k: int)
  requires valid_rbtree tree 'ft
  returns y: rb_ptr
  ensures valid_rbtree y (S.delete 'ft k) **
          pure (S.mem k (S.delete 'ft k) = false /\
                S.search (S.delete 'ft k) k == None)

fn free_valid_rbtree (tree: rb_ptr)
  requires valid_rbtree tree 'ft
  ensures emp

// ========== Complexity-aware API ==========

fn rb_search_log (tree: rb_ptr) (k: int)
  preserves valid_rbtree tree 'ft
  returns result: option int
  ensures pure (result == S.search 'ft k /\
                (S.mem k 'ft ==> result == Some k) /\
                (~(S.mem k 'ft) ==> result == None) /\
                C.search_ticks 'ft k <= S.height 'ft + 1)

fn rb_insert_log (tree: rb_ptr) (k: int)
  requires valid_rbtree tree 'ft
  returns y: rb_ptr
  ensures valid_rbtree y (S.insert 'ft k) **
          pure (S.mem k (S.insert 'ft k) = true /\
                S.search (S.insert 'ft k) k == Some k /\
                C.insert_ticks 'ft k <= S.height 'ft + 2)

fn rb_delete_log (tree: rb_ptr) (k: int)
  requires valid_rbtree tree 'ft
  returns y: rb_ptr
  ensures valid_rbtree y (S.delete 'ft k) **
          pure (S.mem k (S.delete 'ft k) = false /\
                S.search (S.delete 'ft k) k == None /\
                C.delete_ticks 'ft k <= 2 * S.height 'ft + 2)
