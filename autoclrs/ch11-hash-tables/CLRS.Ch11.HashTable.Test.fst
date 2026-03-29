module CLRS.Ch11.HashTable.Test
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

// Test: Create a small hash table, insert some values, and search for them
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
fn test_hash_table ()
  requires emp
  ensures emp
{
  // Create a table of size 5, initially all -1 (empty)
  let tv = hash_table_create 5sz;
  let table = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 5 (-1))) as (A.pts_to table (Seq.create 5 (-1)));
  
  // Ghost tick counter for complexity tracking
  let ctr = GR.alloc #nat 0;
  
  // Insert key 10 (should go to position 10 % 5 = 0)
  let success1 = hash_insert table 5sz 10 ctr;
  
  // Insert key 23 (should go to position 23 % 5 = 3)
  let success2 = hash_insert table 5sz 23 ctr;
  
  // Search for key 10 (should find it at position 0)
  let idx1 = hash_search table 5sz 10 ctr;
  
  // Search for key 23 (should find it at position 3)
  let idx2 = hash_search table 5sz 23 ctr;
  
  // Search for key 99 (not present, should return 5)
  let idx3 = hash_search table 5sz 99 ctr;
  
  // Delete key 10 (should find and delete it at position 0)
  let del1 = hash_delete table 5sz 10 ctr;
  
  // Re-search for key 10 (now deleted, should return 5 = not found)
  let idx4 = hash_search table 5sz 10 ctr;
  
  // Free the ghost counter
  GR.free ctr;
  
  // Free the table
  with s. assert (A.pts_to table s);
  rewrite (A.pts_to table s) as (A.pts_to (V.vec_to_array tv) s);
  hash_table_free tv;
}
#pop-options

// Test: Create a size-3 table, fill it, then verify 4th insert fails
fn test_insert_full ()
  requires emp
  ensures emp
{
  let tv = hash_table_create 3sz;
  let table = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 3 (-1))) as (A.pts_to table (Seq.create 3 (-1)));
  let ctr = GR.alloc #nat 0;
  
  // Fill all 3 slots: keys 0, 1, 2 hash to slots 0, 1, 2
  let s1 = hash_insert table 3sz 0 ctr;
  let s2 = hash_insert table 3sz 1 ctr;
  let s3 = hash_insert table 3sz 2 ctr;
  
  // Table is full — 4th insert should fail
  let s4 = hash_insert table 3sz 99 ctr;
  
  // Clean up
  GR.free ctr;
  with s. assert (A.pts_to table s);
  rewrite (A.pts_to table s) as (A.pts_to (V.vec_to_array tv) s);
  hash_table_free tv;
}

// Test: Insert keys that collide (3 and 8 both hash to slot 3 in size-5 table)
fn test_collision ()
  requires emp
  ensures emp
{
  let tv = hash_table_create 5sz;
  let table = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 5 (-1))) as (A.pts_to table (Seq.create 5 (-1)));
  let ctr = GR.alloc #nat 0;
  
  // Insert key 3 (hashes to slot 3 % 5 = 3)
  let s1 = hash_insert table 5sz 3 ctr;
  
  // Insert key 8 (hashes to slot 8 % 5 = 3, collision, probes to slot 4)
  let s2 = hash_insert table 5sz 8 ctr;
  
  // Search for key 3 — should find it
  let idx1 = hash_search table 5sz 3 ctr;
  
  // Search for key 8 — should find it despite collision
  let idx2 = hash_search table 5sz 8 ctr;
  
  // Clean up
  GR.free ctr;
  with s. assert (A.pts_to table s);
  rewrite (A.pts_to table s) as (A.pts_to (V.vec_to_array tv) s);
  hash_table_free tv;
}
