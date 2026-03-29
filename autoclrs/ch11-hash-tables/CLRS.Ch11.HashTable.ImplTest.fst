(*
   Hash Table Spec Validation Tests

   Source: Adapted from the spec validation methodology described in
   https://arxiv.org/abs/2406.09757 and test patterns from
   https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/

   Each test exercises a concrete instance of the Impl.fsti API and proves
   that the postcondition is precise enough to determine the expected output.

   NO admits. NO assumes.
*)

module CLRS.Ch11.HashTable.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch11.HashTable.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ============================================================
// Pure helpers for reasoning about concrete table contents
// ============================================================

// Lemma: In Seq.create n v, every element at a valid index equals v.
// This helps Z3 connect postconditions to concrete sequences.
let lemma_create_index (n: nat) (v: int) (i: nat)
  : Lemma (requires i < n)
          (ensures Seq.index (Seq.create n v) i == v)
  = ()

// Helper: triggers Z3 pattern matching for insert's false-branch contradiction
// on a fresh table. Generates the term hash_probe_nat key 0 size and the fact
// that slot 0 in the probe sequence is -1 (empty).
let trigger_insert_empty (n: nat{n > 0}) (key: int{key >= 0})
  : Lemma (hash_probe_nat key 0 n < n /\
           Seq.index (Seq.create n (-1)) (hash_probe_nat key 0 n) == -1)
  = lemma_hash_probe_nat_in_bounds key 0 n;
    lemma_create_index n (-1) (hash_probe_nat key 0 n)
let lemma_create_no_key (n: nat{n > 0}) (key: int{key >= 0})
  : Lemma (~(key_in_table (Seq.create n (-1)) n key))
  = // For any probe p < n, hash_probe_nat key p n < n,
    // and Seq.index (Seq.create n (-1)) _ == -1 != key (since key >= 0).
    // So no probe finds the key, meaning key_in_table is false.
    introduce forall (probe: nat). probe < n ==> Seq.index (Seq.create n (-1)) (hash_probe_nat key probe n) =!= key
    with introduce _ ==> _ with _. (
      lemma_hash_probe_nat_in_bounds key probe n;
      lemma_create_index n (-1) (hash_probe_nat key probe n)
    )

// ============================================================
// Test 1: Search on empty table returns not-found
// ============================================================
//
// Proves:
// - Precondition of hash_search is satisfiable (valid_ht holds for fresh table)
// - Postcondition is precise: search for absent key returns exactly `size`
//

#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
fn test_search_empty ()
  requires emp
  ensures emp
{
  let tv = hash_table_create 3sz;
  let table = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 3 (-1)))
       as (A.pts_to table (Seq.create 3 (-1)));
  let ctr = GR.alloc #nat 0;

  // Search for key 5 in empty table
  let r = hash_search table 3sz 5 ctr;

  // Postcondition precision: We prove the result is exactly 3 (not found).
  //
  // Reasoning from the postcondition:
  //   - SZ.v r <= 3
  //   - SZ.v r < 3 ==> Seq.index (Seq.create 3 (-1)) (SZ.v r) == 5
  //   - But Seq.index (Seq.create 3 (-1)) i == -1 for any valid i
  //   - So SZ.v r < 3 leads to -1 == 5, a contradiction
  //   - Therefore SZ.v r == 3
  assert (pure (SZ.v r == 3));

  // Cleanup
  GR.free ctr;
  with s. assert (A.pts_to table s);
  rewrite (A.pts_to table s) as (A.pts_to (V.vec_to_array tv) s);
  hash_table_free tv;
}
#pop-options


// ============================================================
// Test 2: Insert then search — key is found
// ============================================================
//
// Proves:
// - Precondition of hash_insert is satisfiable
// - **Insert on empty table MUST succeed** (strengthened spec):
//   The false branch requires all probe positions to be non-empty/non-deleted,
//   but probe 0 hits slot hash_probe_nat(0,0,3) = 0, which is -1 in the
//   fresh table — contradiction. So b == true is forced.
// - After a successful insert, hash_search finds the key (result < size)
// - The slot at the returned index contains the key
//

#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
fn test_insert_then_search ()
  requires emp
  ensures emp
{
  let tv = hash_table_create 3sz;
  let table = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 3 (-1)))
       as (A.pts_to table (Seq.create 3 (-1)));
  let ctr = GR.alloc #nat 0;

  // Insert key 0
  let b = hash_insert table 3sz 0 ctr;

  // ** NEW: Insert on empty table MUST succeed **
  // The false branch of the postcondition asserts:
  //   forall q < 3. Seq.index (Seq.create 3 (-1)) (hash_probe_nat 0 q 3) =!= -1
  // For q = 0: hash_probe_nat 0 0 3 = 0, and Seq.index (Seq.create 3 (-1)) 0 = -1
  // So -1 =!= -1 is false — contradiction. Hence b must be true.
  trigger_insert_empty 3 0;
  assert (pure (b == true));

  // Search for key 0 — must find it
  let r = hash_search table 3sz 0 ctr;

  // Postcondition precision: search must find key 0.
  // From insert: key_in_table s' 3 0
  // From search: SZ.v r == 3 ==> ~(key_in_table s' 3 0)
  // Contrapositive: key_in_table s' 3 0 ==> SZ.v r != 3
  // Combined with SZ.v r <= 3: SZ.v r < 3
  assert (pure (SZ.v r < 3));

  // Cleanup
  GR.free ctr;
  with s. assert (A.pts_to table s);
  rewrite (A.pts_to table s) as (A.pts_to (V.vec_to_array tv) s);
  hash_table_free tv;
}
#pop-options


// ============================================================
// Test 3: Insert then search for absent key — not found
// ============================================================
//
// Proves:
// - Insert on empty table succeeds (strengthened spec)
// - After inserting key 0, searching for key 1 returns not-found
// - The postcondition's seq_modified_at is precise enough to determine
//   that other keys remain absent
//

#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
fn test_insert_search_absent ()
  requires emp
  ensures emp
{
  let tv = hash_table_create 3sz;
  let table = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 3 (-1)))
       as (A.pts_to table (Seq.create 3 (-1)));
  let ctr = GR.alloc #nat 0;

  // Insert key 0 — must succeed on empty table
  let b = hash_insert table 3sz 0 ctr;
  trigger_insert_empty 3 0;
  assert (pure (b == true));

  // Search for key 1 — should NOT find it
  let r = hash_search table 3sz 1 ctr;

  // Postcondition precision: search must return 3 (not found).
  //
  // From search: SZ.v r < 3 ==> Seq.index s' (SZ.v r) == 1
  // From insert: s' has slots that are either 0 (at idx) or -1 (elsewhere)
  // Neither 0 nor -1 equals 1, so SZ.v r < 3 leads to contradiction
  // Therefore SZ.v r == 3
  assert (pure (SZ.v r == 3));

  // Cleanup
  GR.free ctr;
  with s. assert (A.pts_to table s);
  rewrite (A.pts_to table s) as (A.pts_to (V.vec_to_array tv) s);
  hash_table_free tv;
}
#pop-options


// ============================================================
// Test 4: Delete then search — key is absent
// ============================================================
//
// Proves:
// - Insert on empty table succeeds (strengthened spec)
// - **Delete after insert MUST succeed** (strengthened spec):
//   Insert establishes key_in_table. The delete postcondition's false branch
//   now asserts ~(key_in_table s size key), contradicting key_in_table.
//   So b2 == true is forced.
// - After insert + delete, search returns not-found
// - Z3 reasons through the composition of insert and delete postconditions
//

#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
fn test_delete_then_search ()
  requires emp
  ensures emp
{
  let tv = hash_table_create 3sz;
  let table = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 3 (-1)))
       as (A.pts_to table (Seq.create 3 (-1)));
  let ctr = GR.alloc #nat 0;

  // Insert key 0 — must succeed
  let b1 = hash_insert table 3sz 0 ctr;
  trigger_insert_empty 3 0;
  assert (pure (b1 == true));

  // Delete key 0 — must succeed
  // ** NEW: delete on present key MUST succeed **
  // From insert: key_in_table s' 3 0 (key is in the table)
  // Delete's false branch: ~(key_in_table s' 3 0) — contradicts the above
  // So b2 == true is forced.
  let b2 = hash_delete table 3sz 0 ctr;
  assert (pure (b2 == true));

  // Search for key 0 — should NOT find it
  let r = hash_search table 3sz 0 ctr;

  // The slot that had key 0 is now -2.
  // From insert: the key was at exactly one position (seq_modified_at from [-1,-1,-1])
  // From delete: that position is now -2, all others unchanged
  // So no slot contains 0.
  // From search: SZ.v r < 3 ==> Seq.index s'' (SZ.v r) == 0
  // But no slot contains 0, so SZ.v r == 3
  assert (pure (SZ.v r == 3));

  // Cleanup
  GR.free ctr;
  with s. assert (A.pts_to table s);
  rewrite (A.pts_to table s) as (A.pts_to (V.vec_to_array tv) s);
  hash_table_free tv;
}
#pop-options


// ============================================================
// Test 5: Insert-no-dup — existing key leaves table unchanged
// ============================================================
//
// Proves:
// - Insert on empty table succeeds (strengthened spec)
// - hash_insert_no_dup postcondition distinguishes between
//   "key was already present (table unchanged)" and "key was freshly inserted"
// - b2 == true is forced by postcondition contradiction
//

#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
fn test_insert_no_dup_existing ()
  requires emp
  ensures emp
{
  let tv = hash_table_create 3sz;
  let table = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 3 (-1)))
       as (A.pts_to table (Seq.create 3 (-1)));
  let ctr = GR.alloc #nat 0;

  // First insert key 0 (plain insert) — must succeed
  let b1 = hash_insert table 3sz 0 ctr;
  trigger_insert_empty 3 0;
  assert (pure (b1 == true));

  // Now try insert_no_dup with the same key 0
  with s1. assert (A.pts_to table s1);
  let b2 = hash_insert_no_dup table 3sz 0 ctr;

  // insert_no_dup postcondition on success:
  //   key_in_table s' 3 0 /\ key_findable s' 3 0 /\
  //   (s' == s1 \/ (freshly inserted))
  //
  // In the else branch: ~(key_in_table s1 3 0). But we know key_in_table s1 3 0
  // from the insert postcondition. Contradiction! So b2 must be true.
  assert (pure (b2 == true));

  // Verify key 0 is still findable
  let r = hash_search table 3sz 0 ctr;
  assert (pure (SZ.v r < 3));

  // Cleanup
  GR.free ctr;
  with s. assert (A.pts_to table s);
  rewrite (A.pts_to table s) as (A.pts_to (V.vec_to_array tv) s);
  hash_table_free tv;
}
#pop-options


// ============================================================
// Test 6: Insert-no-dup on empty table — fresh insert
// ============================================================
//
// Proves:
// - **hash_insert_no_dup on empty table MUST succeed** (strengthened spec):
//   The false branch requires all probes to be non-empty/non-deleted,
//   which contradicts the fresh table. So b == true is forced.
// - On success, the key was freshly inserted (not already present)
//

#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
fn test_insert_no_dup_fresh ()
  requires emp
  ensures emp
{
  let tv = hash_table_create 3sz;
  let table = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 3 (-1)))
       as (A.pts_to table (Seq.create 3 (-1)));
  let ctr = GR.alloc #nat 0;

  // We first prove that key 0 is absent from the empty table
  lemma_create_no_key 3 0;

  // insert_no_dup key 0 into empty table — must succeed
  let b = hash_insert_no_dup table 3sz 0 ctr;

  // ** NEW: insert_no_dup on empty table MUST succeed **
  // The false branch asserts forall q < 3. probe positions are non-empty/non-deleted.
  // For q = 0: hash_probe_nat(0,0,3) = 0, Seq.index (Seq.create 3 (-1)) 0 = -1
  // And -1 =!= -1 is false — contradiction. So b must be true.
  trigger_insert_empty 3 0;
  assert (pure (b == true));

  // The postcondition distinguishes fresh insert from "was already present"
  // using the ~(key_in_table s size key) clause from the fresh-insert disjunct.
  // We proved ~(key_in_table (Seq.create 3 (-1)) 3 0) above.

  // Verify key 0 is findable
  let r = hash_search table 3sz 0 ctr;
  assert (pure (SZ.v r < 3));

  // Cleanup
  GR.free ctr;
  with s. assert (A.pts_to table s);
  rewrite (A.pts_to table s) as (A.pts_to (V.vec_to_array tv) s);
  hash_table_free tv;
}
#pop-options


// ============================================================
// Test 7: Create and free — basic lifecycle
// ============================================================
//
// Proves:
// - hash_table_create postcondition establishes valid_ht
// - The returned table can immediately be freed
// - Precondition of hash_table_free (V.is_full_vec) is satisfiable
//

fn test_create_free ()
  requires emp
  ensures emp
{
  let tv = hash_table_create 5sz;
  hash_table_free tv;
}
