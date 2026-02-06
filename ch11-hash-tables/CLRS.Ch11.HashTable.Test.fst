module CLRS.Ch11.HashTable.Test
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch11.HashTable

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

// Test: Create a small hash table, insert some values, and search for them
fn test_hash_table ()
  requires emp
  ensures emp
{
  // Create a table of size 5, initially all -1 (empty)
  let tv = V.alloc (-1) 5sz;
  V.to_array_pts_to tv;
  let table = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 5 (-1))) as (A.pts_to table (Seq.create 5 (-1)));
  
  // Insert key 10 (should go to position 10 % 5 = 0)
  let success1 = hash_insert table 5sz 10;
  
  // Insert key 23 (should go to position 23 % 5 = 3)
  let success2 = hash_insert table 5sz 23;
  
  // Search for key 10 (should find it at position 0)
  let idx1 = hash_search table 5sz 10;
  
  // Search for key 23 (should find it at position 3)
  let idx2 = hash_search table 5sz 23;
  
  // Search for key 99 (not present, should return 5)
  let idx3 = hash_search table 5sz 99;
  
  // Free the table
  with s. assert (A.pts_to table s);
  rewrite (A.pts_to table s) as (A.pts_to (V.vec_to_array tv) s);
  V.to_vec_pts_to tv;
  V.free tv;
}
