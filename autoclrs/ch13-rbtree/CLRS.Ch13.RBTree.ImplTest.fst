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
 * Two layers of assurance:
 *   1. PROOF (ghost, erased at extraction):
 *      ✓ Postconditions from rb_insert_v / rb_search_v / rb_delete_v
 *      ✓ Ghost assertions establish each search result matches expected value
 *      ✓ ensures (r == true): proof guarantees the runtime check passes
 *
 *   2. RUNTIME (computational, survives extraction to C):
 *      ✓ opt_int_eq comparisons check search results against expected values
 *      ✓ Returns bool — caller (test_main.c) verifies at runtime
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

(* option int equality — computational, survives extraction to C *)
inline_for_extraction
let opt_int_eq (a b: option int) : (r:bool{r <==> a == b}) =
  match a, b with
  | None, None -> true
  | Some x, Some y -> x = y
  | _ -> false

#push-options "--fuel 8 --ifuel 2 --z3rlimit 10"

// Helper: membership lemma chain establishes mem 4 (insert(insert(insert Leaf 3) 1) 2) = false
// (Still needed for non-existing key tests where the postcondition gives
//  ~(S.mem k 'ft) ==> result == None, but we must establish ~(S.mem k 'ft))
let mem_4_not_in_t3 ()
  : Lemma (S.mem 4 (S.insert (S.insert (S.insert S.Leaf 3) 1) 2) = false)
  = L.insert_mem S.Leaf 3 4;
    L.insert_mem (S.insert S.Leaf 3) 1 4;
    L.insert_mem (S.insert (S.insert S.Leaf 3) 1) 2 4

// Helper: after deleting 1, key 3 is still a member
// (Demonstrates cross-key reasoning via insert_mem + delete_mem)
let mem_3_after_delete_1 ()
  : Lemma (S.mem 3 (S.delete (S.insert (S.insert (S.insert S.Leaf 3) 1) 2) 1) = true)
  = L.insert_mem S.Leaf 3 3;
    L.insert_mem (S.insert S.Leaf 3) 1 3;
    L.insert_mem (S.insert (S.insert S.Leaf 3) 1) 2 3;
    L.delete_mem (S.insert (S.insert (S.insert S.Leaf 3) 1) 2) 1 3

```pulse
(** test_rbtree_insert_search_delete
 *
 * Completeness test: exercises rb_new, rb_insert_v, rb_search_v,
 * rb_delete_v, and free_valid_rbtree on a concrete 3-element instance.
 *
 * Proves:
 *  1. Preconditions are satisfiable (rb_new → rb_insert_v → rb_search_v → rb_delete_v)
 *  2. After insert, searching for the inserted key returns Some k
 *     — derived DIRECTLY from strengthened postcondition (no assert_norm helper)
 *  3. After insert, searching for a non-existing key returns None
 *     — derived from postcondition + insert_mem chain
 *  4. After delete, searching for the deleted key returns None
 *     — derived DIRECTLY from strengthened postcondition (no assert_norm helper)
 *  5. After delete, remaining keys are still searchable
 *     — derived from postcondition + delete_mem + insert_mem chain
 *  6. Memory is properly freed via free_valid_rbtree
 *  7. Returns bool from runtime comparisons — survives extraction to C
 *)
fn test_rbtree_insert_search_delete ()
  requires emp
  returns passed: bool
  ensures emp ** pure (passed == true)
{
  // 1. Create empty RB tree
  let tree0 = I.rb_new ();

  // 2. Insert keys: 3, 1, 2
  let tree1 = I.rb_insert_v tree0 3;
  // Postcondition gives: valid_rbtree tree1 (S.insert S.Leaf 3)
  //   + S.mem 3 (S.insert S.Leaf 3) = true
  //   + S.search (S.insert S.Leaf 3) 3 == Some 3

  let tree2 = I.rb_insert_v tree1 1;

  let tree3 = I.rb_insert_v tree2 2;
  // Postcondition gives: valid_rbtree tree3 (S.insert (S.insert (S.insert S.Leaf 3) 1) 2)
  //   + S.mem 2 ... = true
  //   + S.search ... 2 == Some 2

  // 3. Search for existing key 2 — postcondition of rb_insert_v already
  //    established S.search 'ft 2 == Some 2, so rb_search_v directly gives r2 == Some 2.
  //    NO helper lemma or assert_norm needed!
  let r2 = I.rb_search_v tree3 2;
  assert (pure (r2 == Some 2));
  let check1 = opt_int_eq r2 (Some 2);

  // 4. Search for non-existing key 4 — postcondition gives
  //    ~(S.mem 4 'ft) ==> r4 == None; we establish ~(S.mem 4 'ft) via insert_mem chain
  let r4 = I.rb_search_v tree3 4;
  mem_4_not_in_t3 ();
  assert (pure (r4 == None));
  let check2 = opt_int_eq r4 None;

  // 5. Delete key 1 — postcondition gives S.search (S.delete 'ft 1) 1 == None
  let tree4 = I.rb_delete_v tree3 1;

  // 6. Search for deleted key 1 — postcondition of rb_delete_v already
  //    established S.search 'ft 1 == None, so rb_search_v directly gives r1_after == None.
  //    NO helper lemma or assert_norm needed!
  let r1_after = I.rb_search_v tree4 1;
  assert (pure (r1_after == None));
  let check3 = opt_int_eq r1_after None;

  // 7. Search for remaining key 3 — we establish S.mem 3 'ft via
  //    insert_mem + delete_mem chain, then postcondition gives r3_after == Some 3
  let r3_after = I.rb_search_v tree4 3;
  mem_3_after_delete_1 ();
  assert (pure (r3_after == Some 3));
  let check4 = opt_int_eq r3_after (Some 3);

  // 8. Clean up: free all memory
  I.free_valid_rbtree tree4;

  // 9. Return runtime check result (ghost proof guarantees this is true)
  let result = check1 && check2 && check3 && check4;
  result
}
```

#pop-options
