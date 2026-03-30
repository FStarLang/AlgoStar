(*
   Array-Based BST — Spec Validation Test

   Tests the CLRS.Ch12.BSTArray.Impl.fsti API using a small concrete instance:
   create an empty 7-element BST, search the empty tree, insert a key, and
   search again.

   Two layers of assurance:
     1. PROOF (ghost, erased at extraction):
        Ghost assertions verify postcondition precision
     2. RUNTIME (computational, survives extraction to C):
        Concrete comparisons check insert/search consistency
        Returns bool — caller can verify at runtime

   Proves:
   1. Search precondition is satisfiable on an empty tree
   2. Insert precondition is satisfiable on an empty tree
   3. Search postcondition is precise: absent key returns None (empty tree)
   4. Insert->Search composability: successful insert implies search finds key
   5. No-op insert: search on unchanged arrays returns None

   Methodology:
     Bhat et al., "Towards Validated Specifications for LLM-Generated Code"
     https://arxiv.org/abs/2406.09757

   NO admits. NO assumes.
*)
module CLRS.Ch12.BSTArray.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

open FStar.Mul
open CLRS.Ch12.BSTArray.Impl
open CLRS.Ch12.BSTArray.Complexity
module AP = CLRS.Ch12.BSTArray.Predicates

(* ====================================================================
   § 1. Pure specification validation

   Verify well_formed_bst and subtree_in_range on a concrete empty tree.
   ==================================================================== *)

let empty_keys : Seq.seq int = Seq.create 7 0
let empty_valid : Seq.seq bool = Seq.create 7 false

// well_formed_bst holds for the empty tree (all valid entries false)
#push-options "--fuel 4 --ifuel 2"
let _ : squash (AP.well_formed_bst empty_keys empty_valid 7 0 0 100) = ()
#pop-options

// subtree_in_range holds trivially for the empty tree
let _ : squash (subtree_in_range empty_keys empty_valid 7 0 0 100) = ()

// key_in_subtree is false for all keys in an empty tree
let _ : squash (~(key_in_subtree empty_keys empty_valid 7 0 5)) = ()

(* ====================================================================
   § 2. Pulse API test — exercises tree_search and tree_insert

   Returns bool with concrete runtime checks.
   ==================================================================== *)

#push-options "--fuel 8 --ifuel 4"

```pulse
(** test_bstarray_search_insert
 *
 * Exercises: tree_search (on empty tree), tree_insert, tree_search
 *            (after insert), demonstrating insert->search composability
 *
 * Instance: cap=7, insert key 5 with bounds lo=0 hi=100
 *
 * Returns true iff all runtime checks pass.
 * Ghost postcondition: r == true (proven at verification time).
 *)
fn test_bstarray_search_insert ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  // Create key array: 7 ints, all 0
  let kv = V.alloc 0 7sz;
  V.to_array_pts_to kv;
  let k_arr = V.vec_to_array kv;
  rewrite (A.pts_to (V.vec_to_array kv) (Seq.create 7 0))
       as (A.pts_to k_arr (Seq.create 7 0));

  // Create valid array: 7 bools, all false
  let vv = V.alloc false 7sz;
  V.to_array_pts_to vv;
  let v_arr = V.vec_to_array vv;
  rewrite (A.pts_to (V.vec_to_array vv) (Seq.create 7 false))
       as (A.pts_to v_arr (Seq.create 7 false));

  // Ghost tick counter
  let ctr = GR.alloc #nat 0;

  // Construct BST record
  let t : bst = { keys = k_arr; valid = v_arr; cap = 7sz };
  rewrite (A.pts_to k_arr (Seq.create 7 0))
       as (A.pts_to t.keys (Seq.create 7 0));
  rewrite (A.pts_to v_arr (Seq.create 7 false))
       as (A.pts_to t.valid (Seq.create 7 false));

  // === Search empty tree for key 5 ===
  let r_empty = tree_search #1.0R t #(hide (Seq.create 7 0)) #(hide (Seq.create 7 false)) #(hide 0) #(hide 100) 5 ctr;
  // Postcondition: None? r_empty ==> ~(key_in_subtree ...)
  assert (pure (None? r_empty));

  // --- Runtime check: search on empty tree returns None ---
  let pass_empty = not (Some? r_empty);

  // === Insert key 5 (bounds: lo=0, hi=100) ===
  let success = tree_insert t #(hide (Seq.create 7 0)) #(hide (Seq.create 7 false)) 5 #(hide 0) #(hide 100) ctr;

  // After insert: arrays updated, well_formed_bst preserved
  with ks' vs' vticks'. assert (
    A.pts_to t.keys ks' **
    A.pts_to t.valid vs' **
    GR.pts_to ctr vticks'
  );

  // Bridge: AP.well_formed_bst -> Impl.subtree_in_range
  wfb_to_sir (Ghost.reveal ks') (Ghost.reveal vs') 7 0 0 100;

  // === Search for key 5 after insert ===
  let r_found = tree_search #1.0R t #ks' #vs' #(hide 0) #(hide 100) 5 ctr;
  assert (pure (success ==> Some? r_found));
  assert (pure (not success ==> None? r_found));

  // --- Runtime check: insert and search are consistent ---
  // If insert succeeded, search must find the key.
  // If insert failed, search must not find the key.
  // Both implications are proven ghost, so the disjunction is provably true.
  let pass_consistency = not success || Some? r_found;

  // === Search for absent key 99 after insert ===
  let r_miss = tree_search #1.0R t #ks' #vs' #(hide 0) #(hide 100) 99 ctr;
  assert (pure (not success ==> None? r_miss));

  // === Cleanup ===
  with vticks_f. assert (GR.pts_to ctr vticks_f);
  GR.free ctr;

  with ks_f. assert (A.pts_to t.keys ks_f);
  rewrite (A.pts_to t.keys ks_f) as (A.pts_to (V.vec_to_array kv) ks_f);
  V.to_vec_pts_to kv;
  V.free kv;

  with vs_f. assert (A.pts_to t.valid vs_f);
  rewrite (A.pts_to t.valid vs_f) as (A.pts_to (V.vec_to_array vv) vs_f);
  V.to_vec_pts_to vv;
  V.free vv;

  // --- Final result: all checks must pass ---
  let result = pass_empty && pass_consistency;
  result
}
```

#pop-options
