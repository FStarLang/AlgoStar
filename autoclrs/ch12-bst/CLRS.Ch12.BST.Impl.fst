module CLRS.Ch12.BST.Impl
(*
   CLRS Chapter 12: Pointer-Based Binary Search Tree

   Each node has { key, left, right, p } following CLRS §12.1.
   A recursive separation logic predicate `bst_subtree` ties the
   concrete pointer structure to the pure functional `bst` from
   CLRS.Ch12.BST.Spec.

   Operations follow CLRS pseudocode and carry a ghost tick counter
   linked to the complexity functions in CLRS.Ch12.BST.Complexity:
   - TREE-SEARCH   (§12.2): ticks == bst_search_ticks
   - TREE-MINIMUM  (§12.2): ticks == bst_minimum_ticks
   - TREE-MAXIMUM  (§12.2): ticks == bst_maximum_ticks
   - TREE-INSERT   (§12.3): ticks == bst_insert_ticks
   - TREE-DELETE   (§12.3): ticks == bst_delete_ticks
   - TREE-FREE: no ticks

   Types, bst_subtree predicate, and operation signatures are in the .fsti.
   This file contains the implementations.
   NO admits. NO assumes.
*)
#lang-pulse
open Pulse.Lib.Pervasives

module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module GR = Pulse.Lib.GhostReference

open CLRS.Ch12.BST.Spec
open CLRS.Ch12.BST.Complexity

// ============================================================
// Ghost fold/unfold helpers
// ============================================================

ghost fn elim_bst_leaf (x: bst_ptr) (#parent: bst_ptr)
  requires bst_subtree x Leaf parent
  ensures pure (x == None)
{
  unfold (bst_subtree x Leaf parent)
}

ghost fn intro_bst_leaf (x: bst_ptr) (parent: bst_ptr)
  requires pure (x == None)
  ensures bst_subtree x Leaf parent
{
  fold (bst_subtree x Leaf parent)
}

ghost fn intro_bst_node (ct: bst_ptr) (bp: bst_node_ptr)
  (#node: bst_node) (#lt #rt: bst)
  requires
    (bp |-> node) **
    bst_subtree node.left lt (Some bp) **
    bst_subtree node.right rt (Some bp) **
    pure (ct == Some bp)
  ensures
    bst_subtree ct (Node lt node.key rt) node.p
{
  fold (bst_subtree ct (Node lt node.key rt) node.p)
}

// ============================================================
// Case analysis predicate (following RBTree pattern)
// ============================================================

[@@no_mkeys]
let bst_cases (x: bst_ptr) (ft: bst) (parent: bst_ptr)
  = match x with
    | None -> pure (ft == Leaf)
    | Some bp ->
      exists* (node: bst_node) (lt rt: bst).
        (bp |-> node) **
        pure (ft == Node lt node.key rt /\ node.p == parent) **
        bst_subtree node.left lt (Some bp) **
        bst_subtree node.right rt (Some bp)

ghost fn cases_of_bst (x: bst_ptr) (ft: bst) (parent: bst_ptr)
  requires bst_subtree x ft parent
  ensures bst_cases x ft parent
{
  match ft {
    Leaf -> {
      unfold (bst_subtree x Leaf parent);
      fold (bst_cases (None #bst_node_ptr) ft parent);
      rewrite bst_cases (None #bst_node_ptr) ft parent
           as bst_cases x ft parent;
    }
    Node l k r -> {
      unfold (bst_subtree x (Node l k r) parent);
      with bp node. _;
      fold (bst_cases (Some bp) ft parent);
      rewrite (bst_cases (Some bp) ft parent)
           as bst_cases x ft parent;
    }
  }
}

// Learn ft == Leaf from ct == None
ghost fn bst_case_none (x: bst_ptr) (#ft: bst) (#parent: bst_ptr)
  preserves bst_subtree x ft parent
  requires pure (x == None)
  ensures pure (ft == Leaf)
{
  rewrite each x as (None #bst_node_ptr);
  cases_of_bst (None #bst_node_ptr) ft parent;
  unfold bst_cases;
  intro_bst_leaf (None #bst_node_ptr) parent;
  rewrite bst_subtree (None #bst_node_ptr) Leaf parent
       as bst_subtree x ft parent;
  ()
}

// Decompose a non-null subtree into its node + children
ghost fn bst_case_some (x: bst_ptr) (bp: bst_node_ptr)
  (#ft: bst) (#parent: bst_ptr)
  requires bst_subtree x ft parent ** pure (x == Some bp)
  ensures exists* (node: bst_node) (lt rt: bst).
    (bp |-> node) **
    bst_subtree node.left lt (Some bp) **
    bst_subtree node.right rt (Some bp) **
    pure (ft == Node lt node.key rt /\ node.p == parent)
{
  rewrite each x as (Some bp);
  cases_of_bst (Some bp) ft parent;
  unfold bst_cases;
}

// ============================================================
// TREE-SEARCH (§12.2) — recursive, read-only
// ============================================================

//SNIPPET_START: tree_search
fn rec tree_search (tree: bst_ptr) (k: int) (ticks: GR.ref nat)
  preserves bst_subtree tree 'ft 'parent
  requires GR.pts_to ticks 'n
  returns result: bool
  ensures GR.pts_to ticks ('n + bst_search_ticks 'ft k) **
          pure (result == bst_search 'ft k)
{
  match tree {
    None -> {
      bst_case_none (None #bst_node_ptr);
      rewrite bst_subtree (None #bst_node_ptr) 'ft 'parent
           as bst_subtree tree 'ft 'parent;
      false
    }
    Some bp -> {
      bst_case_some (Some bp) bp;
      let node = !bp;
      if (k = node.key) {
        // 1 tick for visiting this node
        with n0. assert (GR.pts_to ticks n0);
        GR.op_Colon_Equals ticks (hide (n0 + 1));
        intro_bst_node (Some bp) bp;
        with t p. rewrite (bst_subtree (Some bp) t p)
                       as bst_subtree tree 'ft 'parent;
        true
      } else if (k < node.key) {
        // 1 tick for visiting this node, then recurse left
        with n0. assert (GR.pts_to ticks n0);
        GR.op_Colon_Equals ticks (hide (n0 + 1));
        let res = tree_search node.left k ticks;
        intro_bst_node (Some bp) bp;
        with t p. rewrite (bst_subtree (Some bp) t p)
                       as bst_subtree tree 'ft 'parent;
        res
      } else {
        // 1 tick for visiting this node, then recurse right
        with n0. assert (GR.pts_to ticks n0);
        GR.op_Colon_Equals ticks (hide (n0 + 1));
        let res = tree_search node.right k ticks;
        intro_bst_node (Some bp) bp;
        with t p. rewrite (bst_subtree (Some bp) t p)
                       as bst_subtree tree 'ft 'parent;
        res
      }
    }
  }
}
//SNIPPET_END: tree_search

// ============================================================
// TREE-MINIMUM (§12.2) — recursive, read-only
//
// Walks left pointers until x.left == NIL, returns the key.
// Requires a non-null tree (Some bp).
// ============================================================

//SNIPPET_START: tree_minimum
fn rec tree_minimum (tree: bst_ptr) (bp: bst_node_ptr) (ticks: GR.ref nat)
  preserves bst_subtree tree 'ft 'parent
  requires GR.pts_to ticks 'n ** pure (tree == Some bp)
  returns result: int
  ensures GR.pts_to ticks ('n + bst_minimum_ticks 'ft) **
          pure (bst_minimum 'ft == Some result)
{
  rewrite each tree as (Some bp);
  bst_case_some (Some bp) bp;
  let nd = !bp;
  match nd.left {
    None -> {
      // 1 tick: check left is Leaf, return key
      with n0. assert (GR.pts_to ticks n0);
      GR.op_Colon_Equals ticks (hide (n0 + 1));
      bst_case_none nd.left;
      intro_bst_node (Some bp) bp;
      with t p. rewrite (bst_subtree (Some bp) t p)
                     as bst_subtree tree 'ft 'parent;
      nd.key
    }
    Some lbp -> {
      // 1 tick: check left, then recurse
      with n0. assert (GR.pts_to ticks n0);
      GR.op_Colon_Equals ticks (hide (n0 + 1));
      let result = tree_minimum nd.left lbp ticks;
      intro_bst_node (Some bp) bp;
      with t p. rewrite (bst_subtree (Some bp) t p)
                     as bst_subtree tree 'ft 'parent;
      result
    }
  }
}
//SNIPPET_END: tree_minimum

// ============================================================
// TREE-MAXIMUM (§12.2) — recursive, read-only
//
// Walks right pointers until x.right == NIL, returns the key.
// Requires a non-null tree (Some bp).
// ============================================================

//SNIPPET_START: tree_maximum
fn rec tree_maximum (tree: bst_ptr) (bp: bst_node_ptr) (ticks: GR.ref nat)
  preserves bst_subtree tree 'ft 'parent
  requires GR.pts_to ticks 'n ** pure (tree == Some bp)
  returns result: int
  ensures GR.pts_to ticks ('n + bst_maximum_ticks 'ft) **
          pure (bst_maximum 'ft == Some result)
{
  rewrite each tree as (Some bp);
  bst_case_some (Some bp) bp;
  let nd = !bp;
  match nd.right {
    None -> {
      // 1 tick: check right is Leaf, return key
      with n0. assert (GR.pts_to ticks n0);
      GR.op_Colon_Equals ticks (hide (n0 + 1));
      bst_case_none nd.right;
      intro_bst_node (Some bp) bp;
      with t p. rewrite (bst_subtree (Some bp) t p)
                     as bst_subtree tree 'ft 'parent;
      nd.key
    }
    Some rbp -> {
      // 1 tick: check right, then recurse
      with n0. assert (GR.pts_to ticks n0);
      GR.op_Colon_Equals ticks (hide (n0 + 1));
      let result = tree_maximum nd.right rbp ticks;
      intro_bst_node (Some bp) bp;
      with t p. rewrite (bst_subtree (Some bp) t p)
                     as bst_subtree tree 'ft 'parent;
      result
    }
  }
}
//SNIPPET_END: tree_maximum

// ============================================================
// TREE-SUCCESSOR and TREE-PREDECESSOR (§12.2) — deferred
//
// These require walking UP the tree via parent pointers:
//
//   TREE-SUCCESSOR(x)
//     if x.right ≠ NIL
//       return TREE-MINIMUM(x.right)
//     y = x.p
//     while y ≠ NIL and x == y.right
//       x = y
//       y = y.p
//     return y
//
// The upward walk needs ownership of ancestor nodes, which is
// not available from `bst_subtree` (it only owns the subtree
// rooted at the given node). A correct implementation would
// require either:
//   (a) a zipper / tree-context decomposition, or
//   (b) a whole-tree predicate with a "focus" cursor
// This is left as future work.
// ============================================================

// ============================================================
// Helper: allocate a new node
// ============================================================

fn new_bst_node (k: int) (parent: bst_ptr)
  requires emp
  returns y: bst_ptr
  ensures bst_subtree y (Node Leaf k Leaf) parent ** pure (Some? y)
{
  let left_nil : bst_ptr = None #bst_node_ptr;
  let right_nil : bst_ptr = None #bst_node_ptr;
  let bp = Box.alloc ({ key = k; left = left_nil; right = right_nil; p = parent } <: bst_node);
  intro_bst_leaf left_nil (Some bp);
  intro_bst_leaf right_nil (Some bp);
  intro_bst_node (Some bp) bp;
  Some bp
}

// ============================================================
// TREE-INSERT (§12.3) — recursive, destructive
//
// Consumes the old tree and produces a new tree with the
// key inserted. Parent pointers are maintained correctly.
// ============================================================

//SNIPPET_START: tree_insert
fn rec tree_insert (tree: bst_ptr) (k: int) (parent: bst_ptr) (ticks: GR.ref nat)
  requires bst_subtree tree 'ft parent ** GR.pts_to ticks 'n
  returns y: bst_ptr
  ensures bst_subtree y (bst_insert 'ft k) parent **
          GR.pts_to ticks ('n + bst_insert_ticks 'ft k)
{
  match tree {
    None -> {
      // Leaf: allocate Node Leaf k Leaf with the given parent
      // bst_insert_ticks Leaf k = 0, so no tick increment
      bst_case_none (None #bst_node_ptr);
      rewrite bst_subtree (None #bst_node_ptr) 'ft parent
           as bst_subtree (None #bst_node_ptr) Leaf parent;
      elim_bst_leaf (None #bst_node_ptr);
      let y = new_bst_node k parent;
      with t. rewrite (bst_subtree y t parent)
                   as (bst_subtree y (bst_insert 'ft k) parent);
      y
    }
    Some vl -> {
      bst_case_some (Some vl) vl;
      let node = !vl;
      if (k < node.key) {
        // 1 tick, then insert into left subtree
        with n0. assert (GR.pts_to ticks n0);
        GR.op_Colon_Equals ticks (hide (n0 + 1));
        let new_left = tree_insert node.left k (Some vl) ticks;
        vl := { node with left = new_left };
        intro_bst_node (Some vl) vl;
        with t p. rewrite (bst_subtree (Some vl) t p)
                       as (bst_subtree (Some vl) (bst_insert 'ft k) parent);
        Some vl
      } else if (k > node.key) {
        // 1 tick, then insert into right subtree
        with n0. assert (GR.pts_to ticks n0);
        GR.op_Colon_Equals ticks (hide (n0 + 1));
        let new_right = tree_insert node.right k (Some vl) ticks;
        vl := { node with right = new_right };
        intro_bst_node (Some vl) vl;
        with t p. rewrite (bst_subtree (Some vl) t p)
                       as (bst_subtree (Some vl) (bst_insert 'ft k) parent);
        Some vl
      } else {
        // 1 tick for duplicate key
        with n0. assert (GR.pts_to ticks n0);
        GR.op_Colon_Equals ticks (hide (n0 + 1));
        intro_bst_node (Some vl) vl;
        with t p. rewrite (bst_subtree (Some vl) t p)
                       as (bst_subtree tree (bst_insert 'ft k) parent);
        tree
      }
    }
  }
}
//SNIPPET_END: tree_insert

// ============================================================
// Helper: set_parent_ptr — update a subtree's parent pointer
//
// When promoting a child to replace a deleted node, we must
// update that child's parent pointer to the deleted node's parent.
// ============================================================

//SNIPPET_START: set_parent_ptr
fn set_parent_ptr (child: bst_ptr) (new_parent: bst_ptr)
  requires bst_subtree child 'ft 'old_parent
  ensures bst_subtree child 'ft new_parent
{
  match child {
    None -> {
      bst_case_none (None #bst_node_ptr);
      rewrite bst_subtree (None #bst_node_ptr) 'ft 'old_parent
           as bst_subtree (None #bst_node_ptr) Leaf 'old_parent;
      elim_bst_leaf (None #bst_node_ptr);
      intro_bst_leaf (None #bst_node_ptr) new_parent;
      rewrite bst_subtree (None #bst_node_ptr) Leaf new_parent
           as bst_subtree child 'ft new_parent;
    }
    Some bp -> {
      bst_case_some (Some bp) bp;
      let nd = !bp;
      bp := { nd with p = new_parent };
      intro_bst_node (Some bp) bp;
      with t p. rewrite (bst_subtree (Some bp) t p)
                     as bst_subtree child 'ft new_parent;
    }
  }
}
//SNIPPET_END: set_parent_ptr

// ============================================================
// Helper: learn that a non-null pointer implies Node ghost tree
//
// If `bst_subtree (Some bp) ft parent` is satisfiable,
// then `ft` must be a Node (not Leaf), since Leaf would
// require `Some bp == None` which is false.
// ============================================================

//SNIPPET_START: bst_subtree_some_is_node
ghost fn bst_subtree_some_is_node (x: bst_ptr) (bp: bst_node_ptr)
  (#ft: bst) (#parent: bst_ptr)
  preserves bst_subtree x ft parent
  requires pure (x == Some bp)
  ensures pure (Node? ft)
{
  bst_case_some x bp;
  intro_bst_node x bp;
  with t p. rewrite (bst_subtree x t p) as (bst_subtree x ft parent);
}
//SNIPPET_END: bst_subtree_some_is_node

// ============================================================
// Helper: consume a Leaf subtree (null pointer)
//
// When deleting a node, we need to discard Leaf children.
// This ghost function consumes the subtree and learns ft == Leaf.
// ============================================================

//SNIPPET_START: consume_bst_leaf
ghost fn consume_bst_leaf (x: bst_ptr) (#ft: bst) (#parent: bst_ptr)
  requires bst_subtree x ft parent ** pure (x == None)
  ensures pure (ft == Leaf)
{
  rewrite each x as (None #bst_node_ptr);
  cases_of_bst (None #bst_node_ptr) ft parent;
  unfold bst_cases;
}
//SNIPPET_END: consume_bst_leaf

// ============================================================
// TREE-DELETE (§12.3) — recursive key-based deletion
//
// Combines search + delete: recurses down to find the key,
// then handles four cases at the target node:
//   1. No children (Leaf, Leaf): free node, return Leaf
//   2. No left child (Leaf, _): free node, promote right
//   3. No right child (_, Leaf): free node, promote left
//   4. Two children (_, _): replace key with successor
//      (minimum of right subtree), delete successor from right
//
// Postcondition links to the pure `bst_delete` spec.
// ============================================================

//SNIPPET_START: tree_delete
#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"

fn rec tree_delete (tree: bst_ptr) (k: int) (parent: bst_ptr) (ticks: GR.ref nat)
  requires bst_subtree tree 'ft parent ** GR.pts_to ticks 'n
  returns result: bst_ptr
  ensures bst_subtree result (bst_delete 'ft k) parent **
          GR.pts_to ticks ('n + bst_delete_ticks 'ft k)
  decreases 'ft
{
  match tree {
    None -> {
      // Leaf: nothing to delete, bst_delete_ticks Leaf k = 0
      bst_case_none (None #bst_node_ptr);
      rewrite bst_subtree (None #bst_node_ptr) 'ft parent
           as bst_subtree (None #bst_node_ptr) Leaf parent;
      rewrite bst_subtree (None #bst_node_ptr) Leaf parent
           as bst_subtree (None #bst_node_ptr) (bst_delete 'ft k) parent;
      None #bst_node_ptr
    }
    Some bp -> {
      bst_case_some (Some bp) bp;
      let nd = !bp;
      if (k < nd.key) {
        // 1 tick, then delete from left subtree
        with n0. assert (GR.pts_to ticks n0);
        GR.op_Colon_Equals ticks (hide (n0 + 1));
        let new_left = tree_delete nd.left k (Some bp) ticks;
        bp := { nd with left = new_left };
        intro_bst_node (Some bp) bp;
        with t p. rewrite (bst_subtree (Some bp) t p)
                       as (bst_subtree (Some bp) (bst_delete 'ft k) parent);
        Some bp
      } else if (k > nd.key) {
        // 1 tick, then delete from right subtree
        with n0. assert (GR.pts_to ticks n0);
        GR.op_Colon_Equals ticks (hide (n0 + 1));
        let new_right = tree_delete nd.right k (Some bp) ticks;
        bp := { nd with right = new_right };
        intro_bst_node (Some bp) bp;
        with t p. rewrite (bst_subtree (Some bp) t p)
                       as (bst_subtree (Some bp) (bst_delete 'ft k) parent);
        Some bp
      } else {
        // k == nd.key: found the node to delete — 1 tick
        with n0. assert (GR.pts_to ticks n0);
        GR.op_Colon_Equals ticks (hide (n0 + 1));
        match nd.left {
          None -> {
            // No left child: promote right child
            consume_bst_leaf nd.left;
            set_parent_ptr nd.right parent;
            Box.free bp;
            with t p. rewrite (bst_subtree nd.right t p)
                           as (bst_subtree nd.right (bst_delete 'ft k) parent);
            nd.right
          }
          Some lbp -> {
            match nd.right {
              None -> {
                // No right child: promote left child
                consume_bst_leaf nd.right;
                set_parent_ptr nd.left parent;
                Box.free bp;
                with t p. rewrite (bst_subtree nd.left t p)
                               as (bst_subtree nd.left (bst_delete 'ft k) parent);
                nd.left
              }
              Some rbp -> {
                // Two children: replace key with successor, delete successor
                bst_subtree_some_is_node nd.left lbp;
                bst_subtree_some_is_node nd.right rbp;
                let sk = tree_minimum nd.right rbp ticks;
                let new_right = tree_delete nd.right sk (Some bp) ticks;
                bp := { nd with key = sk; right = new_right };
                intro_bst_node (Some bp) bp;
                with t p. rewrite (bst_subtree (Some bp) t p)
                               as (bst_subtree (Some bp) (bst_delete 'ft k) parent);
                Some bp
              }
            }
          }
        }
      }
    }
  }
}

#pop-options
//SNIPPET_END: tree_delete

// ============================================================
// TREE-FREE — recursive deallocation of all nodes
// ============================================================

//SNIPPET_START: free_bst
fn rec free_bst (tree: bst_ptr)
  requires bst_subtree tree 'ft 'parent
  ensures emp
  decreases 'ft
{
  match tree {
    None -> {
      cases_of_bst (None #bst_node_ptr) 'ft 'parent;
      unfold bst_cases
    }
    Some bp -> {
      bst_case_some (Some bp) bp;
      let node = !bp;
      free_bst node.left;
      free_bst node.right;
      Box.free bp
    }
  }
}
//SNIPPET_END: free_bst
