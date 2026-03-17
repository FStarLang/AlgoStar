(*
   Hash Table with Open Addressing — Public Interface

   CLRS §11.4: Open addressing hash table with linear probing.
   Division-method hash: h(k) = k % m
   Probe sequence: h(k, i) = (h(k) + i) % m

   Provides: hash_table_create, hash_table_free, hash_insert, hash_search, hash_delete
   All operations proven correct with O(n) worst-case complexity.

   NO admits. NO assumes.
*)

module CLRS.Ch11.HashTable.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// Hash table with open addressing using linear probing
// Sentinel values: -1 = empty, -2 = deleted, >= 0 = valid key

// ========== Pure specification predicates ==========

//SNIPPET_START: ht_hash
// Pure version of hash_probe for reasoning
let hash_probe_nat (key: int{key >= 0}) (probe: nat) (size: nat{size > 0}) : nat =
  (key % size + probe) % size
//SNIPPET_END: ht_hash

// Lemma: hash_probe_nat is always in bounds
val lemma_hash_probe_nat_in_bounds (key: int{key >= 0}) (probe: nat) (size: nat{size > 0})
  : Lemma (hash_probe_nat key probe size < size)

//SNIPPET_START: ht_key_in_table
// Abstract specification: key is present somewhere in the probe sequence
let key_in_table (s: Seq.seq int) (size: nat{size > 0}) (key: int{key >= 0}) : prop =
  exists (probe: nat). probe < size /\ probe < Seq.length s /\ 
    hash_probe_nat key probe size < Seq.length s /\
    Seq.index s (hash_probe_nat key probe size) == key
//SNIPPET_END: ht_key_in_table

//SNIPPET_START: ht_key_findable
// Stronger: key is findable by hash_search — it's at some probe position p,
// and no empty slot (-1) appears at any earlier probe position.
// This guarantees hash_search will reach the key.
let key_findable (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: int{key >= 0}) : prop =
  exists (probe: nat). probe < size /\
    hash_probe_nat key probe size < Seq.length s /\
    Seq.index s (hash_probe_nat key probe size) == key /\
    (forall (p: nat). {:pattern (hash_probe_nat key p size)}
      p < probe ==> Seq.index s (hash_probe_nat key p size) =!= -1)
//SNIPPET_END: ht_key_findable

// Helper: all probes up to i did not contain the key
let probes_not_key (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: int{key >= 0}) (i: nat) : prop =
  forall (probe: nat). {:pattern (hash_probe_nat key probe size)} 
    probe < i ==> Seq.index s (hash_probe_nat key probe size) =!= key

// Helper: table only changed at one position
let seq_modified_at (s s': Seq.seq int) (idx: nat{idx < Seq.length s /\ Seq.length s' == Seq.length s}) : prop =
  forall (j: nat). j < Seq.length s /\ j =!= idx ==> Seq.index s j == Seq.index s' j

// Helper: key appears at most once in the table (no duplicates)
let unique_key (s: Seq.seq int) (key: int{key >= 0}) : prop =
  forall (i j: nat). i < Seq.length s /\ j < Seq.length s /\
    Seq.index s i == key /\ Seq.index s j == key ==> i == j

// ========== Table well-formedness invariant ==========

//SNIPPET_START: ht_valid_ht
// CLRS's correctness argument for HASH-SEARCH relies on the fact that no
// operation ever turns a slot into NIL (-1).  INSERT fills NIL/DELETED slots
// with keys; DELETE turns key slots into DELETED (-2).  Therefore, if we
// encounter a NIL slot at probe position j, no key can exist beyond j in
// the probe sequence — it would have been placed at or before j by INSERT.
//
// valid_ht captures this: for EVERY occurrence of a valid key at some probe
// position, no NIL (-1) slot appears at any earlier probe position.
let valid_ht (s: Seq.seq int) (size: nat) : prop =
  size > 0 /\ size == Seq.length s /\
  (forall (k: int) (probe: nat). {:pattern (Seq.index s (hash_probe_nat k probe size))}
    k >= 0 /\ probe < size /\ Seq.index s (hash_probe_nat k probe size) == k ==>
    (forall (p: nat). {:pattern (hash_probe_nat k p size)}
      p < probe ==> Seq.index s (hash_probe_nat k p size) =!= -1))
//SNIPPET_END: ht_valid_ht

// Lemma: under valid_ht, if a key is at some array index, then it is findable
// by hash_search (key_findable holds)
val lemma_valid_ht_key_at_index_findable
  (s: Seq.seq int) (size: nat) (key: int{key >= 0}) (idx: nat)
  : Lemma
    (requires valid_ht s size /\ idx < size /\ Seq.index s idx == key)
    (ensures key_findable s size key)

// ========== Operations ==========

//SNIPPET_START: ht_helpers
// Create a fresh hash table of given size, all slots initialized to -1 (empty)
fn hash_table_create (size: SZ.t)
  requires pure (SZ.v size > 0)
  returns tv: V.vec int
  ensures A.pts_to (V.vec_to_array tv) (Seq.create (SZ.v size) (-1)) **
          pure (V.is_full_vec tv /\ valid_ht (Seq.create (SZ.v size) (-1)) (SZ.v size))

// Free a hash table
fn hash_table_free (tv: V.vec int) (#s: erased (Seq.seq int))
  requires A.pts_to (V.vec_to_array tv) s ** pure (V.is_full_vec tv)
  ensures emp
//SNIPPET_END: ht_helpers

//SNIPPET_START: ht_hash_insert
// Insert a key into the hash table
// Returns true if successful, false if table is full
// Proves both correctness and O(n) complexity
fn hash_insert
  (table: A.array int)
  (#s: erased (Seq.seq int))
  (size: SZ.t)
  (key: int{key >= 0 /\ SZ.fits key})
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to table s **
    GR.pts_to ctr c0 **
    pure (SZ.v size > 0 /\ Seq.length s == SZ.v size /\
          valid_ht s (SZ.v size))
  returns result: bool
  ensures exists* s' cf.
    A.pts_to table s' **
    GR.pts_to ctr cf **
    pure (
      Seq.length s' == SZ.v size /\
      Seq.length s' == Seq.length s /\
      valid_ht s' (SZ.v size) /\
      (if result
       then (key_in_table s' (SZ.v size) key /\
             key_findable s' (SZ.v size) key /\
             (exists (idx: nat). idx < SZ.v size /\
               (Seq.index s idx == -1 \/ Seq.index s idx == -2) /\
               Seq.index s' idx == key /\
               seq_modified_at s s' idx))
       else (s' == s /\
             (forall (q: nat). {:pattern (hash_probe_nat key q (SZ.v size))}
               q < SZ.v size ==>
                 Seq.index s (hash_probe_nat key q (SZ.v size)) =!= -1 /\
                 Seq.index s (hash_probe_nat key q (SZ.v size)) =!= -2))) /\
      cf >= reveal c0 /\ cf - reveal c0 <= SZ.v size
    )
//SNIPPET_END: ht_hash_insert

//SNIPPET_START: ht_hash_insert_no_dup
// Insert a key only if it is not already present (prevents duplicates)
// Returns true if the key is in the table after the call (either already
// present or freshly inserted), false if the table is full and the key
// was not already present.
// Complexity: at most 2 * size probes (one search + one insert)
fn hash_insert_no_dup
  (table: A.array int)
  (#s: erased (Seq.seq int))
  (size: SZ.t)
  (key: int{key >= 0 /\ SZ.fits key})
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to table s **
    GR.pts_to ctr c0 **
    pure (SZ.v size > 0 /\ Seq.length s == SZ.v size /\
          valid_ht s (SZ.v size))
  returns result: bool
  ensures exists* s' cf.
    A.pts_to table s' **
    GR.pts_to ctr cf **
    pure (
      Seq.length s' == SZ.v size /\
      Seq.length s' == Seq.length s /\
      valid_ht s' (SZ.v size) /\
      cf >= reveal c0 /\ cf - reveal c0 <= 2 * SZ.v size /\
      (if result
       then (key_in_table s' (SZ.v size) key /\
             key_findable s' (SZ.v size) key /\
             // No duplicate: either table unchanged (key was already there)
             // or key was freshly inserted at one empty/deleted slot
             (s' == s \/
              (exists (idx: nat). idx < SZ.v size /\
                (Seq.index s idx == -1 \/ Seq.index s idx == -2) /\
                Seq.index s' idx == key /\
                seq_modified_at s s' idx /\
                ~(key_in_table s (SZ.v size) key))))
       else (s' == s /\ ~(key_in_table s (SZ.v size) key) /\
             (forall (q: nat). {:pattern (hash_probe_nat key q (SZ.v size))}
               q < SZ.v size ==>
                 Seq.index s (hash_probe_nat key q (SZ.v size)) =!= -1 /\
                 Seq.index s (hash_probe_nat key q (SZ.v size)) =!= -2)))
    )
//SNIPPET_END: ht_hash_insert_no_dup

//SNIPPET_START: ht_hash_search
// Search for a key in the hash table
// Returns the index if found, or returns size (invalid index) if not found
// Proves both correctness and O(n) complexity
fn hash_search
  (table: A.array int)
  (#s: erased (Seq.seq int))
  (size: SZ.t)
  (key: int{key >= 0 /\ SZ.fits key})
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to table s **
    GR.pts_to ctr c0 **
    pure (SZ.v size > 0 /\ Seq.length s == SZ.v size /\
          valid_ht s (SZ.v size))
  returns result: SZ.t
  ensures exists* cf.
    A.pts_to table s **
    GR.pts_to ctr cf **
    pure (
      SZ.v result <= SZ.v size /\
      SZ.v size > 0 /\
      Seq.length s == SZ.v size /\
      valid_ht s (SZ.v size) /\
      key >= 0 /\
      // Functional correctness: found
      (SZ.v result < SZ.v size ==> (
        SZ.v result < Seq.length s /\
        Seq.index s (SZ.v result) == key
      )) /\
      // Functional correctness: not found — key is absent from the table
      (SZ.v result == SZ.v size ==> ~(key_in_table s (SZ.v size) key)) /\
      // Complexity bound: at most size probes
      cf >= reveal c0 /\ cf - reveal c0 <= SZ.v size
    )
//SNIPPET_END: ht_hash_search

//SNIPPET_START: ht_hash_delete
// Delete a key from the hash table using open addressing
// Returns true if the key was found and deleted (marked with -2), false otherwise
// Proves both correctness and O(n) complexity
fn hash_delete
  (table: A.array int)
  (#s: erased (Seq.seq int))
  (size: SZ.t)
  (key: int{key >= 0 /\ SZ.fits key})
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to table s **
    GR.pts_to ctr c0 **
    pure (SZ.v size > 0 /\ Seq.length s == SZ.v size /\
          valid_ht s (SZ.v size))
  returns result: bool
  ensures exists* s' cf.
    A.pts_to table s' **
    GR.pts_to ctr cf **
    pure (
      Seq.length s' == SZ.v size /\
      Seq.length s' == Seq.length s /\
      valid_ht s' (SZ.v size) /\
      cf >= reveal c0 /\ cf - reveal c0 <= SZ.v size /\
      (if result
       then (exists (idx: nat).
               idx < Seq.length s /\
               Seq.index s idx == key /\
               Seq.index s' idx == -2 /\
               seq_modified_at s s' idx)
       else (Seq.equal s' s /\ ~(key_in_table s (SZ.v size) key)))
    )
//SNIPPET_END: ht_hash_delete
