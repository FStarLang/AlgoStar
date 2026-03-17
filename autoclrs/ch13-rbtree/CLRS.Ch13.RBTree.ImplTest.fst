(**
 * CLRS Chapter 13: Red-Black Trees — Specification Validation Test
 *
 * Tests the Okasaki-style Pulse API from CLRS.Ch13.RBTree.Impl.fsti
 * using a small concrete instance (insert keys 3, 1, 2; search; delete).
 *
 * Based on the spec-validation methodology from:
 *   https://arxiv.org/abs/2406.09757
 * Adapted from the intent-formalization test patterns at:
 *   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/
 *
 * Goals:
 *   - Prove preconditions of Impl.fsti functions are satisfiable
 *   - Prove postconditions are precise enough to determine concrete outputs
 *   - Zero admits, zero assumes
 *)
module CLRS.Ch13.RBTree.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives

module S = CLRS.Ch13.RBTree.Spec
module L = CLRS.Ch13.RBTree.Lemmas
module I = CLRS.Ch13.RBTree.Impl

(*** Pure spec validation: verify concrete tree shapes and search results ***)

// Build concrete trees by successive inserts
let t0 : S.rbtree = S.Leaf
let t1 : S.rbtree = S.insert t0 3
let t2 : S.rbtree = S.insert t1 1
let t3 : S.rbtree = S.insert t2 2

// Verify concrete tree shapes after each insert
let _ = assert_norm (t1 == S.Node S.Black S.Leaf 3 S.Leaf)
let _ = assert_norm (t2 == S.Node S.Black (S.Node S.Red S.Leaf 1 S.Leaf) 3 S.Leaf)
let _ = assert_norm (t3 == S.Node S.Black (S.Node S.Black S.Leaf 1 S.Leaf) 2
                                          (S.Node S.Black S.Leaf 3 S.Leaf))

// Verify RB and BST properties hold on concrete trees
let _ = assert_norm (S.is_rbtree t0 = true)
let _ = assert_norm (S.is_bst t0 = true)
let _ = assert_norm (S.is_rbtree t1 = true)
let _ = assert_norm (S.is_bst t1 = true)
let _ = assert_norm (S.is_rbtree t2 = true)
let _ = assert_norm (S.is_bst t2 = true)
let _ = assert_norm (S.is_rbtree t3 = true)
let _ = assert_norm (S.is_bst t3 = true)

// Verify search on concrete tree t3 = {1, 2, 3}
let _ = assert_norm (S.search t3 1 == Some 1)
let _ = assert_norm (S.search t3 2 == Some 2)
let _ = assert_norm (S.search t3 3 == Some 3)
let _ = assert_norm (S.search t3 0 == None)
let _ = assert_norm (S.search t3 4 == None)

// Verify membership
let _ = assert_norm (S.mem 1 t3 = true)
let _ = assert_norm (S.mem 2 t3 = true)
let _ = assert_norm (S.mem 3 t3 = true)
let _ = assert_norm (S.mem 0 t3 = false)
let _ = assert_norm (S.mem 4 t3 = false)

// Verify delete
let t4 : S.rbtree = S.delete t3 1
let _ = assert_norm (S.mem 1 t4 = false)
let _ = assert_norm (S.mem 2 t4 = true)
let _ = assert_norm (S.mem 3 t4 = true)
let _ = assert_norm (S.search t4 1 == None)
let _ = assert_norm (S.search t4 2 == Some 2)
let _ = assert_norm (S.search t4 3 == Some 3)
let _ = assert_norm (S.is_rbtree t4 = true)
let _ = assert_norm (S.is_bst t4 = true)

// Verify duplicate insert is identity
let _ = assert_norm (S.insert t3 2 == t3)

// Verify delete of non-existing key
let t5 : S.rbtree = S.delete t3 99
let _ = assert_norm (S.search t5 1 == Some 1)
let _ = assert_norm (S.search t5 2 == Some 2)
let _ = assert_norm (S.search t5 3 == Some 3)

(*** Pulse test: exercise the Impl.fsti API on concrete inputs ***)

#push-options "--fuel 8 --ifuel 2 --z3rlimit 100"

// Helper lemma: after inserting 3, 1, 2 into empty tree, searching for 2 returns Some 2
let search_insert_3_1_2_for_2 ()
  : Lemma (S.search (S.insert (S.insert (S.insert S.Leaf 3) 1) 2) 2 == Some 2)
  = assert_norm (S.search (S.insert (S.insert (S.insert S.Leaf 3) 1) 2) 2 == Some 2)

let search_insert_3_1_2_for_4 ()
  : Lemma (S.search (S.insert (S.insert (S.insert S.Leaf 3) 1) 2) 4 == None)
  = assert_norm (S.search (S.insert (S.insert (S.insert S.Leaf 3) 1) 2) 4 == None)

let search_delete_1_from_3_1_2_for_1 ()
  : Lemma (S.search (S.delete (S.insert (S.insert (S.insert S.Leaf 3) 1) 2) 1) 1 == None)
  = assert_norm (S.search (S.delete (S.insert (S.insert (S.insert S.Leaf 3) 1) 2) 1) 1 == None)

let search_delete_1_from_3_1_2_for_3 ()
  : Lemma (S.search (S.delete (S.insert (S.insert (S.insert S.Leaf 3) 1) 2) 1) 3 == Some 3)
  = assert_norm (S.search (S.delete (S.insert (S.insert (S.insert S.Leaf 3) 1) 2) 1) 3 == Some 3)

```pulse
(** test_rbtree_insert_search_delete
 *
 * Completeness test: exercises rb_new, rb_insert_v, rb_search_v,
 * rb_delete_v, and free_valid_rbtree on a concrete 3-element instance.
 *
 * Proves:
 *  1. Precondition of rb_new is satisfiable (emp)
 *  2. Precondition of rb_insert_v is satisfiable after rb_new
 *  3. Postcondition of rb_search_v is precise: searching for key 2
 *     in tree {1,2,3} returns exactly Some 2
 *  4. Postcondition of rb_search_v is precise: searching for key 4
 *     (not in tree) returns exactly None
 *  5. Postcondition of rb_delete_v: after deleting key 1, search for 1
 *     returns None
 *  6. Postcondition of rb_delete_v: remaining keys (3) still searchable
 *  7. Memory is properly freed via free_valid_rbtree
 *)
fn test_rbtree_insert_search_delete ()
  requires emp
  returns _: unit
  ensures emp
{
  // 1. Create empty RB tree
  let tree0 = I.rb_new ();

  // 2. Insert keys: 3, 1, 2
  let tree1 = I.rb_insert_v tree0 3;
  // Postcondition gives: valid_rbtree tree1 (S.insert S.Leaf 3)
  //                       S.mem 3 (S.insert S.Leaf 3) = true

  let tree2 = I.rb_insert_v tree1 1;
  // Postcondition gives: valid_rbtree tree2 (S.insert (S.insert S.Leaf 3) 1)
  //                       S.mem 1 (S.insert (S.insert S.Leaf 3) 1) = true

  let tree3 = I.rb_insert_v tree2 2;
  // Postcondition gives: valid_rbtree tree3 (S.insert (S.insert (S.insert S.Leaf 3) 1) 2)
  //                       S.mem 2 (S.insert (S.insert (S.insert S.Leaf 3) 1) 2) = true

  // 3. Search for existing key 2 — postcondition says result == S.search 'ft 2
  let r2 = I.rb_search_v tree3 2;
  search_insert_3_1_2_for_2 ();
  assert (pure (r2 == Some 2));

  // 4. Search for non-existing key 4 — should be None
  let r4 = I.rb_search_v tree3 4;
  search_insert_3_1_2_for_4 ();
  assert (pure (r4 == None));

  // 5. Delete key 1
  let tree4 = I.rb_delete_v tree3 1;
  // Postcondition gives: S.mem 1 (S.delete ... 1) = false

  // 6. Search for deleted key 1 — should be None
  let r1_after = I.rb_search_v tree4 1;
  search_delete_1_from_3_1_2_for_1 ();
  assert (pure (r1_after == None));

  // 7. Search for remaining key 3 — should still be found
  let r3_after = I.rb_search_v tree4 3;
  search_delete_1_from_3_1_2_for_3 ();
  assert (pure (r3_after == Some 3));

  // 8. Clean up: free all memory
  I.free_valid_rbtree tree4;
}
```

#pop-options
