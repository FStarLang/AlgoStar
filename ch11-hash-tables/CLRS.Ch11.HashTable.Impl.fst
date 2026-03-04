(*
   Hash Table with Open Addressing — Implementation

   CLRS §11.4: Open addressing hash table operations with linear probing.

   Proves both correctness and worst-case complexity:
   - INSERT: key_in_table when successful, unchanged when full; O(n) probes
   - SEARCH: found index contains key; when not found, key is absent
             from table or empty slot reached; O(n) probes
   - DELETE: slot marked DELETED (-2) when found, table unchanged otherwise; O(n) probes

   Uses GhostReference.ref nat for tick counter — fully erased at runtime.
   Each probe operation (array access + comparison) gets one ghost tick.

   NO admits. NO assumes.
*)

module CLRS.Ch11.HashTable.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Ghost tick primitives ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Internal hash functions ==========

//SNIPPET_START: ht_hash_internal
// Hash function: h(k) = k % table_size
let hash (k: int{k >= 0 /\ SZ.fits k}) (size: SZ.t{SZ.v size > 0}) : SZ.t =
  SZ.rem (SZ.uint_to_t k) size

// Linear probing: h(k, i) = (h(k) + i) % table_size
let hash_probe (k: int{k >= 0 /\ SZ.fits k}) (i: SZ.t) (size: SZ.t{SZ.v size > 0}) : SZ.t =
  let h = hash k size in
  let sum = SZ.v h + SZ.v i in
  SZ.uint_to_t (sum % SZ.v size)
//SNIPPET_END: ht_hash_internal

// ========== Internal lemmas ==========

// Lemma: hash_probe_nat is always in bounds
let lemma_hash_probe_nat_in_bounds (key: int{key >= 0}) (probe: nat) (size: nat{size > 0})
  : Lemma (hash_probe_nat key probe size < size)
  = ()

// Lemma: hash_probe and hash_probe_nat are consistent
let lemma_hash_probe_consistent (key: int{key >= 0 /\ SZ.fits key}) (i: SZ.t) (size: SZ.t{SZ.v size > 0})
  : Lemma (ensures SZ.v (hash_probe key i size) == hash_probe_nat key (SZ.v i) (SZ.v size))
  = ()

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

// When all probes have been checked and none contain the key,
// the key is not in the table
let lemma_probes_not_key_full
  (s: Seq.seq int)
  (size: nat{size > 0 /\ size == Seq.length s})
  (key: int{key >= 0})
  : Lemma
    (requires probes_not_key s size key size)
    (ensures ~(key_in_table s size key))
    [SMTPat (probes_not_key s size key size)]
  = ()

// ========== valid_ht lemmas ==========

// Key lemma: under valid_ht, an empty slot in the probe sequence proves
// the key is absent from the entire table.
let lemma_valid_ht_search_not_found
  (s: Seq.seq int) (size: nat)
  (key: int{key >= 0}) (j: nat)
  : Lemma
    (requires valid_ht s size /\
              j < size /\
              Seq.index s (hash_probe_nat key j size) == -1 /\
              probes_not_key s size key (j + 1))
    (ensures ~(key_in_table s size key))
  = ()

// valid_ht holds for a fresh table (all -1): vacuously true, no key >= 0 present
let lemma_valid_ht_create (size: nat{size > 0})
  : Lemma (valid_ht (Seq.create size (-1)) size)
  = ()

// valid_ht is preserved by delete (replacing a key with -2)
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let lemma_valid_ht_delete
  (s: Seq.seq int) (size: nat)
  (idx: nat{idx < size})
  : Lemma
    (requires valid_ht s size /\ Seq.index s idx >= 0)
    (ensures valid_ht (Seq.upd s idx (-2)) size)
  = let s' = Seq.upd s idx (-2) in
    introduce forall (k: int) (probe: nat).
      k >= 0 /\ probe < size /\ Seq.index s' (hash_probe_nat k probe size) == k ==>
      (forall (p: nat). p < probe ==> Seq.index s' (hash_probe_nat k p size) =!= -1)
    with introduce _ ==> _
    with _. (
      introduce forall (p: nat). p < probe ==> Seq.index s' (hash_probe_nat k p size) =!= -1
      with introduce _ ==> _
      with _. ()
    )
#pop-options

// valid_ht is preserved by insert (replacing -1 or -2 with a key >= 0)
// when the insertion point is the first empty/deleted slot in the probe sequence
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let lemma_valid_ht_insert
  (s: Seq.seq int) (size: nat)
  (key: int{key >= 0}) (probe_i: nat{probe_i < size})
  : Lemma
    (requires valid_ht s size /\
              (Seq.index s (hash_probe_nat key probe_i size) == -1 \/
               Seq.index s (hash_probe_nat key probe_i size) == -2) /\
              (forall (q: nat). {:pattern (hash_probe_nat key q size)}
                q < probe_i ==>
                  Seq.index s (hash_probe_nat key q size) =!= -1 /\
                  Seq.index s (hash_probe_nat key q size) =!= -2))
    (ensures valid_ht (Seq.upd s (hash_probe_nat key probe_i size) key) size)
  = let idx = hash_probe_nat key probe_i size in
    let s' = Seq.upd s idx key in
    introduce forall (k: int) (probe: nat).
      k >= 0 /\ probe < size /\ Seq.index s' (hash_probe_nat k probe size) == k ==>
      (forall (p: nat). p < probe ==> Seq.index s' (hash_probe_nat k p size) =!= -1)
    with introduce _ ==> _
    with _. (
      introduce forall (p: nat). p < probe ==> Seq.index s' (hash_probe_nat k p size) =!= -1
      with introduce _ ==> _
      with _. (
        ()
      )
    )
#pop-options

// ========== Operations ==========

//SNIPPET_START: ht_helpers_impl
fn hash_table_create (size: SZ.t)
  requires pure (SZ.v size > 0)
  returns tv: V.vec int
  ensures A.pts_to (V.vec_to_array tv) (Seq.create (SZ.v size) (-1)) **
          pure (V.is_full_vec tv /\ valid_ht (Seq.create (SZ.v size) (-1)) (SZ.v size))
{
  lemma_valid_ht_create (SZ.v size);
  let tv = V.alloc (-1) size;
  V.to_array_pts_to tv;
  tv
}

fn hash_table_free (tv: V.vec int) (#s: erased (Seq.seq int))
  requires A.pts_to (V.vec_to_array tv) s ** pure (V.is_full_vec tv)
  ensures emp
{
  V.to_vec_pts_to tv;
  V.free tv
}
//SNIPPET_END: ht_helpers_impl

// Returns true if successful, false if table is full
// Proves both correctness and O(n) complexity
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
//SNIPPET_START: ht_hash_insert_impl
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
       else s' == s) /\
      cf >= reveal c0 /\ cf - reveal c0 <= SZ.v size
    )
//SNIPPET_END: ht_hash_insert_impl
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
      valid_ht st (SZ.v size) /\
      // Correctness invariants
      (vinserted == true ==> vdone == true) /\
      (vinserted == true ==>
        key_in_table st (SZ.v size) key /\
        key_findable st (SZ.v size) key /\
        (exists (idx: nat). idx < SZ.v size /\
          (Seq.index s idx == -1 \/ Seq.index s idx == -2) /\
          Seq.index st idx == key /\
          seq_modified_at s st idx)) /\
      (vinserted == false ==> Seq.equal st s) /\
      (vinserted == false ==>
        (forall (q: nat). {:pattern (hash_probe_nat key q (SZ.v size))}
          q < SZ.v vi ==>
            Seq.index s (hash_probe_nat key q (SZ.v size)) =!= -1 /\
            Seq.index s (hash_probe_nat key q (SZ.v size)) =!= -2)) /\
      // Complexity invariant: exactly vi probes so far
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi
    )
  decreases (SZ.v size - SZ.v !i)
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
//SNIPPET_START: ht_hash_search_impl
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
//SNIPPET_END: ht_hash_search_impl
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
      (vdone /\ SZ.v vfound_idx == SZ.v size ==> ~(key_in_table s (SZ.v size) key)) /\
      // Complexity invariant: exactly vi probes so far
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi
    )
  decreases (SZ.v size - SZ.v !i)
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
    
    // When we hit an empty slot with no key found, valid_ht proves key is absent
    assert pure (lemma_hash_probe_consistent key vi size;
                 SZ.v idx == hash_probe_nat key (SZ.v vi) (SZ.v size));
    assert pure (
      if is_empty
      then (lemma_valid_ht_search_not_found s (SZ.v size) key (SZ.v vi); true)
      else true
    );
    
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

// Delete a key from the hash table using open addressing
// Returns true if the key was found and deleted (marked with -2), false otherwise
// Proves both correctness and O(n) complexity
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
//SNIPPET_START: ht_hash_delete_impl
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
       else Seq.equal s' s)
    )
//SNIPPET_END: ht_hash_delete_impl
{
  let mut i: SZ.t = 0sz;
  let mut deleted_at: SZ.t = size;
  let mut done: bool = false;
  
  while (
    let vdone = !done;
    let vi = !i;
    (not vdone && vi <^ size)
  )
  invariant exists* vi vdel vdone st vc.
    R.pts_to i vi **
    R.pts_to deleted_at vdel **
    R.pts_to done vdone **
    A.pts_to table st **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v size /\
      SZ.v vdel <= SZ.v size /\
      Seq.length st == SZ.v size /\
      valid_ht st (SZ.v size) /\
      // Link deletion and done flag: once deleted, done is set
      (SZ.v vdel < SZ.v size ==> vdone == true) /\
      // When key was found and deleted
      (SZ.v vdel < SZ.v size ==> (
        Seq.index s (SZ.v vdel) == key /\
        Seq.index st (SZ.v vdel) == -2 /\
        seq_modified_at s st (SZ.v vdel)
      )) /\
      // When key not yet found
      (SZ.v vdel == SZ.v size ==> Seq.equal st s) /\
      // Complexity invariant: exactly vi probes so far
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi
    )
  decreases (SZ.v size - SZ.v !i)
  {
    let vi = !i;
    let idx = hash_probe key vi size;
    
    // Tick: one probe operation (array access + comparisons)
    tick ctr;
    
    let slot = A.op_Array_Access table idx;
    
    // Found the key — will mark as DELETED (-2)
    let is_found = (slot = key);
    
    // Hit an empty slot — stop searching
    let is_empty = (slot = -1);
    
    // Compute new value: -2 (DELETED) if found, otherwise keep slot unchanged
    let new_val = (if is_found then -2 else slot);
    A.op_Array_Assignment table idx new_val;
    
    // Preserve valid_ht when deleting
    assert pure (
      if is_found
      then (lemma_valid_ht_delete s (SZ.v size) (SZ.v idx); true)
      else true
    );
    
    // Update deleted_at if we found the key
    let vdel = !deleted_at;
    let new_del = (if is_found then idx else vdel);
    deleted_at := new_del;
    
    // Stop if found or empty
    let vdone_inner = !done;
    let new_done = (if (is_found || is_empty) then true else vdone_inner);
    done := new_done;
    
    i := SZ.add vi 1sz;
  };
  
  let result_idx = !deleted_at;
  (result_idx <^ size)
}
#pop-options

// ========== Complexity summary ==========
// hash_insert, hash_search, and hash_delete are each verified to perform at
// most `size` probes in the worst case (linear in table size) via the ghost
// tick counter.  The postconditions `cf - c0 <= SZ.v size` encode this bound
// directly.
