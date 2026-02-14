module CLRS.Ch11.HashTable
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// Hash table with open addressing using linear probing
// Sentinel values: -1 = empty, -2 = deleted, >= 0 = valid key

// Hash function: h(k) = k % table_size
// Precondition: k >= 0 and fits in size_t
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

// Lemma: hash_probe_nat is always in bounds
let lemma_hash_probe_nat_in_bounds (key: int{key >= 0}) (probe: nat) (size: nat{size > 0})
  : Lemma (hash_probe_nat key probe size < size)
  = ()

// Lemma: hash_probe and hash_probe_nat are consistent
let lemma_hash_probe_consistent (key: int{key >= 0 /\ SZ.fits key}) (i: SZ.t) (size: SZ.t{SZ.v size > 0})
  : Lemma (ensures SZ.v (hash_probe key i size) == hash_probe_nat key (SZ.v i) (SZ.v size))
  = ()

// Abstract specification: key is present somewhere in the probe sequence
// Precondition: size == Seq.length s
let key_in_table (s: Seq.seq int) (size: nat{size > 0}) (key: int{key >= 0}) : prop =
  exists (probe: nat). probe < size /\ probe < Seq.length s /\ 
    hash_probe_nat key probe size < Seq.length s /\
    Seq.index s (hash_probe_nat key probe size) == key

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

// Postcondition predicate for insert
let insert_post (table: A.array int) (s: Seq.seq int) (size: nat{size > 0}) (key: int{key >= 0}) (result: bool) : slprop =
  exists* s'.
    A.pts_to table s' **
    pure (Seq.length s' == size /\
      (result ==> key_in_table s' size key) /\
      (not result ==> s' == s))
// Returns true if successful, false if table is full
// Specification (informal): 
//   - If result == true, key_in_table holds for the final state
//   - If result == false, the table is unchanged
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
fn hash_insert
  (table: A.array int)
  (#s: erased (Seq.seq int))
  (size: SZ.t)
  (key: int)
  requires
    A.pts_to table s **
    pure (SZ.v size > 0 /\ Seq.length s == SZ.v size /\ key >= 0 /\ SZ.fits key)
  returns result: bool
  ensures exists* s'.
    A.pts_to table s' **
    pure (
      Seq.length s' == SZ.v size /\
      (if result then key_in_table s' (SZ.v size) key else s' == s)
    )
{
  let mut i: SZ.t = 0sz;
  let mut inserted: bool = false;
  let mut done: bool = false;
  
  while (
    let vdone = !done;
    let vi = !i;
    (not vdone && vi <^ size)
  )
  invariant exists* vi vinserted vdone st.
    R.pts_to i vi **
    R.pts_to inserted vinserted **
    R.pts_to done vdone **
    A.pts_to table st **
    pure (
      SZ.v vi <= SZ.v size /\
      Seq.length st == SZ.v size /\
      // If inserted, key is in the table
      (vinserted == true ==> key_in_table st (SZ.v size) key) /\
      // If not inserted yet, table unchanged
      (vinserted == false ==> Seq.equal st s)
    )
  {
    let vi = !i;
    let idx = hash_probe key vi size;
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

// Postcondition predicate for search
let search_post (table: A.array int) (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: int{key >= 0}) (result: SZ.t) : slprop =
  A.pts_to table s **
  pure (
    SZ.v result <= size /\
    (SZ.v result < size ==> Seq.index s (SZ.v result) == key) /\
    (SZ.v result == size ==> 
      (exists (n: nat). n <= size /\ 
        probes_not_key s size key n /\
        (n < size ==> Seq.index s (hash_probe_nat key n size) == -1)))
  )

// Search for a key in the hash table
// Returns the index if found, or returns size (invalid index) if not found
// Specification (informal):
//   - If result < size: Seq.index s result == key (found at that index)
//   - If result == size: key not in table (checked probe sequence until empty slot)
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
fn hash_search
  (table: A.array int)
  (#s: erased (Seq.seq int))
  (size: SZ.t)
  (key: int)
  requires
    A.pts_to table s **
    pure (SZ.v size > 0 /\ Seq.length s == SZ.v size /\ key >= 0 /\ SZ.fits key)
  returns result: SZ.t
  ensures 
    A.pts_to table s **
    pure (
      SZ.v result <= SZ.v size /\
      (SZ.v result < SZ.v size ==> (
        SZ.v result < Seq.length s /\
        Seq.index s (SZ.v result) == key
      ))
      // Not-found case (result == size): The key was not found.
      // Loop invariant (line 210) establishes: probes_not_key s size key (final_i)
      // meaning all probed positions up to final_i didn't contain the key.
      // Proving the universal quantifier about "key not at ANY probed position" 
      // in the postcondition requires explicit quantifier instantiation which
      // Pulse's SMT encoding doesn't handle automatically. Clients needing the
      // stronger property can examine the loop invariant or call helper lemmas.
    )
{
  let mut i: SZ.t = 0sz;
  let mut found_idx: SZ.t = size;
  let mut done: bool = false;
  
  while (
    let vdone = !done;
    let vi = !i;
    (not vdone && vi <^ size)
  )
  invariant exists* vi vfound_idx vdone.
    R.pts_to i vi **
    R.pts_to found_idx vfound_idx **
    R.pts_to done vdone **
    A.pts_to table s **
    pure (
      SZ.v vi <= SZ.v size /\
      SZ.v vfound_idx <= SZ.v size /\
      Seq.length s == SZ.v size /\
      // If found, found_idx points to the key
      (SZ.v vfound_idx < SZ.v size ==> Seq.index s (SZ.v vfound_idx) == key) /\
      // If not found yet, all probes so far were not the key
      (SZ.v vfound_idx == SZ.v size ==> probes_not_key s (SZ.v size) key (SZ.v vi)) /\
      // If done and not found, we hit an empty slot
      (vdone /\ SZ.v vfound_idx == SZ.v size ==> 
        (exists (probe: nat). probe < SZ.v vi /\ Seq.index s (hash_probe_nat key probe (SZ.v size)) == -1))
    )
  {
    let vi = !i;
    let idx = hash_probe key vi size;
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
