(**
 * CLRS Chapter 13: Red-Black Trees — Specification Validation Test (CLRS-style)
 *
 * Tests the CLRS-faithful Pulse API from CLRS.Ch13.RBTree.CLRSImpl.fsti
 * using a small concrete instance (insert keys 3, 1, 2; search; delete).
 *
 * Based on the spec-validation methodology from:
 *   https://arxiv.org/abs/2406.09757
 * Adapted from the intent-formalization test patterns at:
 *   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/
 *
 * Goals:
 *   - Prove preconditions of CLRSImpl.fsti functions are satisfiable
 *   - Prove postconditions are precise enough to determine concrete outputs
 *   - Zero admits, zero assumes
 *)
module CLRS.Ch13.RBTree.CLRSImplTest
#lang-pulse
open Pulse.Lib.Pervasives

module S = CLRS.Ch13.RBTree.Spec
module CS = CLRS.Ch13.RBTree.CLRSSpec
module CI = CLRS.Ch13.RBTree.CLRSImpl

(*** Pure spec validation: verify concrete tree shapes and search results ***)

// Build concrete trees by successive CLRS-style inserts
let t0 : S.rbtree = S.Leaf
let t1 : S.rbtree = CS.clrs_insert t0 3
let t2 : S.rbtree = CS.clrs_insert t1 1
let t3 : S.rbtree = CS.clrs_insert t2 2

// Verify concrete tree shapes after each CLRS insert
let _ = assert_norm (t1 == S.Node S.Black S.Leaf 3 S.Leaf)
let _ = assert_norm (t2 == S.Node S.Black (S.Node S.Red S.Leaf 1 S.Leaf) 3 S.Leaf)
// CLRS insert uses rotate+recolor, producing Red children (vs Okasaki's Black)
let _ = assert_norm (t3 == S.Node S.Black (S.Node S.Red S.Leaf 1 S.Leaf) 2
                                          (S.Node S.Red S.Leaf 3 S.Leaf))

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

// Verify CLRS delete
let t4 : S.rbtree = CS.clrs_delete t3 1
let _ = assert_norm (S.mem 1 t4 = false)
let _ = assert_norm (S.mem 2 t4 = true)
let _ = assert_norm (S.mem 3 t4 = true)
let _ = assert_norm (S.search t4 1 == None)
let _ = assert_norm (S.search t4 2 == Some 2)
let _ = assert_norm (S.search t4 3 == Some 3)
let _ = assert_norm (S.is_rbtree t4 = true)
let _ = assert_norm (S.is_bst t4 = true)

// Both implementations produce valid RB trees, but may differ in color choices.
// For this sequence, they agree on inserts 3 and 1 but diverge on insert 2:
// Okasaki produces Black children, CLRS produces Red children.
let _ = assert_norm (CS.clrs_insert S.Leaf 3 == S.insert S.Leaf 3)
let _ = assert_norm (CS.clrs_insert (CS.clrs_insert S.Leaf 3) 1 ==
                     S.insert (S.insert S.Leaf 3) 1)

(*** Pulse test: exercise the CLRSImpl.fsti API on concrete inputs ***)

#push-options "--fuel 8 --ifuel 2 --z3rlimit 10"

// Helper lemmas for normalizing CLRS spec on concrete inputs
let clrs_search_3_1_2_for_2 ()
  : Lemma (S.search (CS.clrs_insert (CS.clrs_insert (CS.clrs_insert S.Leaf 3) 1) 2) 2 == Some 2)
  = assert_norm (S.search (CS.clrs_insert (CS.clrs_insert (CS.clrs_insert S.Leaf 3) 1) 2) 2 == Some 2)

let clrs_search_3_1_2_for_4 ()
  : Lemma (S.search (CS.clrs_insert (CS.clrs_insert (CS.clrs_insert S.Leaf 3) 1) 2) 4 == None)
  = assert_norm (S.search (CS.clrs_insert (CS.clrs_insert (CS.clrs_insert S.Leaf 3) 1) 2) 4 == None)

let clrs_search_del1_for_1 ()
  : Lemma (S.search (CS.clrs_delete (CS.clrs_insert (CS.clrs_insert (CS.clrs_insert S.Leaf 3) 1) 2) 1) 1 == None)
  = assert_norm (S.search (CS.clrs_delete (CS.clrs_insert (CS.clrs_insert (CS.clrs_insert S.Leaf 3) 1) 2) 1) 1 == None)

let clrs_search_del1_for_3 ()
  : Lemma (S.search (CS.clrs_delete (CS.clrs_insert (CS.clrs_insert (CS.clrs_insert S.Leaf 3) 1) 2) 1) 3 == Some 3)
  = assert_norm (S.search (CS.clrs_delete (CS.clrs_insert (CS.clrs_insert (CS.clrs_insert S.Leaf 3) 1) 2) 1) 3 == Some 3)

```pulse
(** test_clrs_rbtree_insert_search_delete
 *
 * Completeness test for the CLRS-faithful implementation.
 * Exercises rb_new, rb_insert_v, rb_search_v, rb_delete_v,
 * and free_valid_rbtree with a concrete 3-element instance.
 *)
fn test_clrs_rbtree_insert_search_delete ()
  requires emp
  returns _: unit
  ensures emp
{
  // 1. Create empty RB tree (parent = None for root)
  let tree0 = CI.rb_new ();

  // 2. Insert keys: 3, 1, 2
  let tree1 = CI.rb_insert_v tree0 3 (None #CI.rb_node_ptr);
  let tree2 = CI.rb_insert_v tree1 1 (None #CI.rb_node_ptr);
  let tree3 = CI.rb_insert_v tree2 2 (None #CI.rb_node_ptr);

  // 3. Search for existing key 2
  let r2 = CI.rb_search_v tree3 2;
  clrs_search_3_1_2_for_2 ();
  assert (pure (r2 == Some 2));

  // 4. Search for non-existing key 4
  let r4 = CI.rb_search_v tree3 4;
  clrs_search_3_1_2_for_4 ();
  assert (pure (r4 == None));

  // 5. Delete key 1
  let tree4 = CI.rb_delete_v tree3 1 (None #CI.rb_node_ptr);

  // 6. Search for deleted key 1
  let r1_after = CI.rb_search_v tree4 1;
  clrs_search_del1_for_1 ();
  assert (pure (r1_after == None));

  // 7. Search for remaining key 3
  let r3_after = CI.rb_search_v tree4 3;
  clrs_search_del1_for_3 ();
  assert (pure (r3_after == Some 3));

  // 8. Clean up
  CI.free_valid_rbtree tree4;
}
```

#pop-options
