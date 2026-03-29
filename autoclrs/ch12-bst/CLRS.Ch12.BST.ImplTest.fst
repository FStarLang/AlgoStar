(*
   Pointer-Based BST — Spec Validation Test

   Tests the Impl.fsti API using a small concrete instance:
   insert keys {2, 1, 3} into an empty tree, then exercise search,
   minimum, maximum, delete, and free_bst.

   Proves:
   1. All preconditions are satisfiable (by constructing valid calls)
   2. Postconditions are precise enough to determine exact outputs
   3. Validity (bst_valid) is preserved through insert and delete

   Methodology:
     Bhat et al., "Towards Validated Specifications for LLM-Generated Code"
     https://arxiv.org/abs/2406.09757
   Adapted from:
     https://github.com/microsoft/intent-formalization/blob/main/
       eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.DLL.fst

   NO admits. NO assumes.
*)
module CLRS.Ch12.BST.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives

module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module GR = Pulse.Lib.GhostReference

open CLRS.Ch12.BST.Spec
open CLRS.Ch12.BST.Complexity
open CLRS.Ch12.BST.Impl

(* ====================================================================
   § 1. Pure specification validation

   Verify the pure spec functions compute expected results for a
   concrete 3-element tree. These assert_norm's prove postcondition
   precision: for each input, the output is uniquely determined.
   ==================================================================== *)

let t0 : bst = Leaf
let t1 : bst = bst_insert t0 2
let t2 : bst = bst_insert t1 1
let t3 : bst = bst_insert t2 3

// Tree shapes after each insert
let _ = assert_norm (t1 == Node Leaf 2 Leaf)
let _ = assert_norm (t2 == Node (Node Leaf 1 Leaf) 2 Leaf)
let _ = assert_norm (t3 == Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf))

// Validity preserved at each step
let _ = assert_norm (bst_valid t0 == true)
let _ = assert_norm (bst_valid t1 == true)
let _ = assert_norm (bst_valid t2 == true)
let _ = assert_norm (bst_valid t3 == true)

// Search precision on t3 = {1, 2, 3}
let _ = assert_norm (bst_search t3 1 == true)
let _ = assert_norm (bst_search t3 2 == true)
let _ = assert_norm (bst_search t3 3 == true)
let _ = assert_norm (bst_search t3 0 == false)
let _ = assert_norm (bst_search t3 4 == false)

// Minimum and maximum precision
let _ = assert_norm (bst_minimum t3 == Some 1)
let _ = assert_norm (bst_maximum t3 == Some 3)

// Delete key 2 from {1,2,3}: CLRS successor-based deletion
let t4 : bst = bst_delete t3 2
let _ = assert_norm (t4 == Node (Node Leaf 1 Leaf) 3 Leaf)
let _ = assert_norm (bst_valid t4 == true)
let _ = assert_norm (bst_search t4 2 == false)
let _ = assert_norm (bst_search t4 1 == true)
let _ = assert_norm (bst_search t4 3 == true)
let _ = assert_norm (bst_minimum t4 == Some 1)
let _ = assert_norm (bst_maximum t4 == Some 3)

// Delete remaining keys yields empty tree
let _ = assert_norm (bst_delete (bst_delete t4 1) 3 == Leaf)

// Duplicate insert is no-op (from Spec.bst_insert_noop_if_present)
let _ = assert_norm (bst_insert t3 2 == t3)

(* ====================================================================
   § 2. Helper lemmas for Pulse test

   Pulse needs explicit lemmas to bridge pure spec evaluation into
   the separation-logic context.
   ==================================================================== *)

let search_t3_1 ()
  : Lemma (bst_search (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 1 == true)
  = assert_norm (bst_search (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 1 == true)

let search_t3_2 ()
  : Lemma (bst_search (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 2 == true)
  = assert_norm (bst_search (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 2 == true)

let search_t3_3 ()
  : Lemma (bst_search (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 3 == true)
  = assert_norm (bst_search (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 3 == true)

let search_t3_0 ()
  : Lemma (bst_search (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 0 == false)
  = assert_norm (bst_search (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 0 == false)

let search_t3_4 ()
  : Lemma (bst_search (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 4 == false)
  = assert_norm (bst_search (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 4 == false)

let minimum_t3 ()
  : Lemma (bst_minimum (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) == Some 1)
  = assert_norm (bst_minimum (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) == Some 1)

let maximum_t3 ()
  : Lemma (bst_maximum (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) == Some 3)
  = assert_norm (bst_maximum (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) == Some 3)

let search_after_delete_2_for_2 ()
  : Lemma (bst_search (bst_delete (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 2) 2 == false)
  = assert_norm (bst_search (bst_delete (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 2) 2 == false)

let search_after_delete_2_for_1 ()
  : Lemma (bst_search (bst_delete (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 2) 1 == true)
  = assert_norm (bst_search (bst_delete (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 2) 1 == true)

let search_after_delete_2_for_3 ()
  : Lemma (bst_search (bst_delete (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 2) 3 == true)
  = assert_norm (bst_search (bst_delete (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 2) 3 == true)

let minimum_after_delete_2 ()
  : Lemma (bst_minimum (bst_delete (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 2) == Some 1)
  = assert_norm (bst_minimum (bst_delete (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 2) == Some 1)

let maximum_after_delete_2 ()
  : Lemma (bst_maximum (bst_delete (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 2) == Some 3)
  = assert_norm (bst_maximum (bst_delete (bst_insert (bst_insert (bst_insert Leaf 2) 1) 3) 2) == Some 3)

(* ====================================================================
   § 3. Pulse API test — precondition satisfiability + postcondition
   precision for all operations in Impl.fsti
   ==================================================================== *)

#push-options "--fuel 8 --ifuel 4"

```pulse
(** test_bst_ptr
 *
 * Exercises: tree_insert, tree_search, tree_minimum, tree_maximum,
 *            tree_delete, free_bst
 *
 * Instance: insert {2, 1, 3}, search for present/absent keys,
 *           find min/max, delete root key 2, verify deletion,
 *           free entire tree
 *)
fn test_bst_ptr ()
  requires emp
  returns _: unit
  ensures emp
{
  // Ghost tick counter (erased at runtime)
  let ticks = GR.alloc #nat 0;

  // Start with empty tree: bst_subtree None Leaf None
  let empty : bst_ptr = None #bst_node_ptr;
  let parent : bst_ptr = None #bst_node_ptr;
  fold (bst_subtree empty Leaf parent);

  // === Insert 2, 1, 3 ===
  let r1 = tree_insert empty 2 parent ticks;
  let r2 = tree_insert r1 1 parent ticks;
  let r3 = tree_insert r2 3 parent ticks;
  // Ghost tree: bst_insert (bst_insert (bst_insert Leaf 2) 1) 3
  //           = Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)

  // === Search: postcondition gives result == bst_search 'ft k ===
  search_t3_1 ();
  let f1 = tree_search r3 1 ticks;
  assert (pure (f1 == true));

  search_t3_2 ();
  let f2 = tree_search r3 2 ticks;
  assert (pure (f2 == true));

  search_t3_3 ();
  let f3 = tree_search r3 3 ticks;
  assert (pure (f3 == true));

  search_t3_0 ();
  let m0 = tree_search r3 0 ticks;
  assert (pure (m0 == false));

  search_t3_4 ();
  let m4 = tree_search r3 4 ticks;
  assert (pure (m4 == false));

  // === Minimum, Maximum (need Some bp), Delete, post-delete search ===
  match r3 {
    Some bp -> {
      // tree_minimum: postcondition bst_minimum 'ft == Some result
      minimum_t3 ();
      let min_v = tree_minimum (Some bp) bp ticks;
      assert (pure (min_v == 1));

      // tree_maximum: postcondition bst_maximum 'ft == Some result
      maximum_t3 ();
      let max_v = tree_maximum (Some bp) bp ticks;
      assert (pure (max_v == 3));

      // tree_delete: delete root key 2
      // Postcondition: ghost tree = bst_delete 'ft 2
      let r4 = tree_delete (Some bp) 2 parent ticks;

      // After delete: search for deleted key returns false
      search_after_delete_2_for_2 ();
      let g2 = tree_search r4 2 ticks;
      assert (pure (g2 == false));

      // Remaining keys still present
      search_after_delete_2_for_1 ();
      let s1 = tree_search r4 1 ticks;
      assert (pure (s1 == true));

      search_after_delete_2_for_3 ();
      let s3 = tree_search r4 3 ticks;
      assert (pure (s3 == true));

      // Min/max after delete (need Some bp again)
      match r4 {
        Some bp4 -> {
          minimum_after_delete_2 ();
          let min4 = tree_minimum (Some bp4) bp4 ticks;
          assert (pure (min4 == 1));

          maximum_after_delete_2 ();
          let max4 = tree_maximum (Some bp4) bp4 ticks;
          assert (pure (max4 == 3));

          // free_bst: deallocate entire tree
          free_bst (Some bp4);
          GR.free ticks;
        }
        None -> {
          // Dead branch: tree has keys {1, 3} after delete
          free_bst (None #bst_node_ptr);
          GR.free ticks;
        }
      }
    }
    None -> {
      // Dead branch: tree has 3 elements after inserts
      free_bst (None #bst_node_ptr);
      GR.free ticks;
    }
  }
}
```

#pop-options
