(*
   Hash Table with Open Addressing — Correctness and Complexity

   CLRS §11.4: Open addressing hash table operations with linear probing.

   Proves both correctness and worst-case complexity:
   - INSERT: key_in_table when successful, unchanged when full; O(n) probes
   - SEARCH: found index contains key; O(n) probes

   Uses GhostReference.ref nat for tick counter — fully erased at runtime.
   Each probe operation (array access + comparison) gets one ghost tick.

   NO admits. NO assumes.
*)

module CLRS.Ch11.HashTable
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// Hash table with open addressing using linear probing
// Sentinel values: -1 = empty, -2 = deleted, >= 0 = valid key

// ========== Ghost tick primitives ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Complexity bound predicates ==========

//SNIPPET_START: ht_complexity_bounds
// Insert complexity: at most n probes
let hash_insert_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= n

// Search complexity: at most n probes
let hash_search_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= n
//SNIPPET_END: ht_complexity_bounds

//SNIPPET_START: ht_hash
// Hash function: h(k) = k % table_size
let hash (k: int{k >= 0 /\ SZ.fits k}) (size: SZ.t{SZ.v size > 0}) : SZ.t =
  SZ.rem (SZ.uint_to_t k) size

// Linear probing: h(k, i) = (h(k) + i) % table_size
let hash_probe (k: int{k >= 0 /\ SZ.fits k}) (i: SZ.t) (size: SZ.t{SZ.v size > 0}) : SZ.t =
  let h = hash k size in
  let sum = SZ.v h + SZ.v i in
  SZ.uint_to_t (sum % SZ.v size)

// Pure version of hash_probe for reasoning
let hash_probe_nat (key: int{key >= 0}) (probe: nat) (size: nat{size > 0}) : nat =
  (key % size + probe) % size
//SNIPPET_END: ht_hash

// Lemma: hash_probe_nat is always in bounds
let lemma_hash_probe_nat_in_bounds (key: int{key >= 0}) (probe: nat) (size: nat{size > 0})
  : Lemma (hash_probe_nat key probe size < size)
  = ()

// Lemma: hash_probe and hash_probe_nat are consistent
let lemma_hash_probe_consistent (key: int{key >= 0 /\ SZ.fits key}) (i: SZ.t) (size: SZ.t{SZ.v size > 0})
  : Lemma (ensures SZ.v (hash_probe key i size) == hash_probe_nat key (SZ.v i) (SZ.v size))
  = ()

// Abstract specification: key is present somewhere in the probe sequence
//SNIPPET_START: ht_key_in_table
let key_in_table (s: Seq.seq int) (size: nat{size > 0}) (key: int{key >= 0}) : prop =
  exists (probe: nat). probe < size /\ probe < Seq.length s /\ 
    hash_probe_nat key probe size < Seq.length s /\
    Seq.index s (hash_probe_nat key probe size) == key
//SNIPPET_END: ht_key_in_table

// Helper: all probes up to i did not contain the key
let probes_not_key (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: int{key >= 0}) (i: nat) : prop =
  forall (probe: nat). {:pattern (hash_probe_nat key probe size)} 
    probe < i ==> Seq.index s (hash_probe_nat key probe size) =!= key

// Instantiation lemma for probes_not_key
let lemma_probes_not_key_inst 
  (s: Seq.seq int) 
  (size: nat{size > 0 /\ size == Seq.length s}) 
  (key: int{key >= 0}) 
  (i: nat) 
  (probe: nat{probe < i})
  : Lemma 
    (requires probes_not_key s size key i)
    (ensures Seq.index s (hash_probe_nat key probe size) =!= key)
  = ()

// Helper: table only changed at one position
let seq_modified_at (s s': Seq.seq int) (idx: nat{idx < Seq.length s /\ Seq.length s' == Seq.length s}) : prop =
  forall (j: nat). j < Seq.length s /\ j =!= idx ==> Seq.index s j == Seq.index s' j

// Returns true if successful, false if table is full
// Proves both correctness and O(n) complexity
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
//SNIPPET_START: ht_hash_insert
fn hash_insert
  (table: A.array int)
  (#s: erased (Seq.seq int))
  (size: SZ.t)
  (key: int)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to table s **
    GR.pts_to ctr c0 **
    pure (SZ.v size > 0 /\ Seq.length s == SZ.v size /\ key >= 0 /\ SZ.fits key)
  returns result: bool
  ensures exists* s' cf.
    A.pts_to table s' **
    GR.pts_to ctr cf **
    pure (
      Seq.length s' == SZ.v size /\
      (if result then key_in_table s' (SZ.v size) key else s' == s) /\
      cf >= reveal c0 /\ cf - reveal c0 <= SZ.v size
    )
//SNIPPET_END: ht_hash_insert
{
  let mut i: SZ.t = 0sz;
  let mut inserted: bool = false;
  let mut done: bool = false;
  
  while (
    let vdone = !done;
    let vi = !i;
    (not vdone && vi <^ size)
  )
  invariant exists* vi vinserted vdone st vc.
    R.pts_to i vi **
    R.pts_to inserted vinserted **
    R.pts_to done vdone **
    A.pts_to table st **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v size /\
      Seq.length st == SZ.v size /\
      // Correctness invariants
      (vinserted == true ==> key_in_table st (SZ.v size) key) /\
      (vinserted == false ==> Seq.equal st s) /\
      // Complexity invariant: exactly vi probes so far
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi
    )
  {
    let vi = !i;
    let idx = hash_probe key vi size;
    
    // Tick: one probe operation (array access + comparisons)
    tick ctr;
    
    let slot = A.op_Array_Access table idx;
    
    // Check if we can insert here (empty or deleted)
    let can_insert = (slot = -1 || slot = -2);
    
    // Compute new value for this slot
    let new_val = (if can_insert then key else slot);
    A.op_Array_Assignment table idx new_val;
    
    assert pure (lemma_hash_probe_consistent key vi size; 
                 SZ.v idx == hash_probe_nat key (SZ.v vi) (SZ.v size));
    
    // Update flags
    let vinserted = !inserted;
    let new_inserted = (if can_insert then true else vinserted);
    inserted := new_inserted;
    
    let vdone_inner = !done;
    let new_done = (if can_insert then true else vdone_inner);
    done := new_done;
    
    i := SZ.add vi 1sz;
  };
  
  !inserted
}
#pop-options

// Search for a key in the hash table
// Returns the index if found, or returns size (invalid index) if not found
// Proves both correctness and O(n) complexity
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
//SNIPPET_START: ht_hash_search
fn hash_search
  (table: A.array int)
  (#s: erased (Seq.seq int))
  (size: SZ.t)
  (key: int)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to table s **
    GR.pts_to ctr c0 **
    pure (SZ.v size > 0 /\ Seq.length s == SZ.v size /\ key >= 0 /\ SZ.fits key)
  returns result: SZ.t
  ensures exists* cf.
    A.pts_to table s **
    GR.pts_to ctr cf **
    pure (
      SZ.v result <= SZ.v size /\
      // Functional correctness
      (SZ.v result < SZ.v size ==> (
        SZ.v result < Seq.length s /\
        Seq.index s (SZ.v result) == key
      )) /\
      // Complexity bound: at most size probes
      cf >= reveal c0 /\ cf - reveal c0 <= SZ.v size
    )
//SNIPPET_END: ht_hash_search
{
  let mut i: SZ.t = 0sz;
  let mut found_idx: SZ.t = size;
  let mut done: bool = false;
  
  while (
    let vdone = !done;
    let vi = !i;
    (not vdone && vi <^ size)
  )
  invariant exists* vi vfound_idx vdone vc.
    R.pts_to i vi **
    R.pts_to found_idx vfound_idx **
    R.pts_to done vdone **
    A.pts_to table s **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v size /\
      SZ.v vfound_idx <= SZ.v size /\
      Seq.length s == SZ.v size /\
      // Functional invariants
      (SZ.v vfound_idx < SZ.v size ==> Seq.index s (SZ.v vfound_idx) == key) /\
      (SZ.v vfound_idx == SZ.v size ==> probes_not_key s (SZ.v size) key (SZ.v vi)) /\
      (vdone /\ SZ.v vfound_idx == SZ.v size ==> 
        (exists (probe: nat). probe < SZ.v vi /\ Seq.index s (hash_probe_nat key probe (SZ.v size)) == -1)) /\
      // Complexity invariant: exactly vi probes so far
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi
    )
  {
    let vi = !i;
    let idx = hash_probe key vi size;
    
    // Tick: one probe operation (array access + comparisons)
    tick ctr;
    
    let slot = A.op_Array_Access table idx;
    
    // Found the key
    let is_found = (slot = key);
    
    // Hit an empty slot, stop searching
    let is_empty = (slot = -1);
    
    // Update found_idx if we found the key
    let vfound_idx_inner = !found_idx;
    let new_found_idx = (if is_found then idx else vfound_idx_inner);
    found_idx := new_found_idx;
    
    // Stop if found or empty
    let vdone_inner = !done;
    let new_done = (if (is_found || is_empty) then true else vdone_inner);
    done := new_done;
    
    i := SZ.add vi 1sz;
  };
  
  !found_idx
}
#pop-options

// ========== Pure complexity lemmas ==========

// Worst-case number of operations for hash table insertion
let hash_insert_worst (n: nat) : nat = n

// Worst-case number of operations for hash table search
let hash_search_worst (n: nat) : nat = n

// Insert is linear in worst case
let hash_insert_linear (n: nat) 
  : Lemma (ensures hash_insert_worst n <= n) 
  = ()

// Search is linear in worst case
let hash_search_linear (n: nat) 
  : Lemma (ensures hash_search_worst n <= n) 
  = ()

// Combined lemma: both operations are O(n)
let hash_operations_linear (n: nat)
  : Lemma (ensures hash_insert_worst n + hash_search_worst n <= op_Multiply 2 n)
  = ()
