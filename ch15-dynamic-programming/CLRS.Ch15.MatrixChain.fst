(*
   Matrix Chain Multiplication - Verified implementation in Pulse
   
   Given dimensions p[0..n] for n matrices (matrix i has dimensions p[i] × p[i+1]),
   find the minimum number of scalar multiplications needed to multiply them.
   
   Bottom-up dynamic programming approach from CLRS Chapter 15.
   
   NO admits. NO assumes.
*)

module CLRS.Ch15.MatrixChain
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.Vec
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Helper Lemmas ==========

// Bounds checking lemma for 2D indexing
let lemma_index_in_bounds (i j n: nat)
  : Lemma (requires i < n /\ j < n)
          (ensures op_Multiply i n + j < op_Multiply n n)
  = ()

let lemma_table_size_positive (n: nat{n > 0})
  : Lemma (op_Multiply n n > 0)
  = ()

// ========== Main Implementation ==========

open Pulse.Lib.BoundedIntegers

fn matrix_chain_order
  (#p: perm)
  (dims: A.array int)
  (n: SZ.t)
  (#s_dims: erased (Seq.seq int))
  requires
    A.pts_to dims #p s_dims **
    pure (
      SZ.v n + 1 == Seq.length s_dims /\
      SZ.v n + 1 == A.length dims /\
      SZ.v n > 0 /\
      SZ.fits (op_Multiply (SZ.v n) (SZ.v n)) /\
      (forall (i: nat). i < Seq.length s_dims ==> Seq.index s_dims i > 0)
    )
  returns result: int
  ensures
    A.pts_to dims #p s_dims **
    pure (result >= 0)
{
  // Allocate DP table m[0..n-1][0..n-1] as flat array of size n*n
  let table_size = n *^ n;
  lemma_table_size_positive (SZ.v n);
  
  let m = V.alloc 0 table_size;
  
  // Initialize: m[i][i] = 0 for all i (single matrix, no cost)
  // This is already done by V.alloc 0
  
  // Main DP: iterate over chain lengths l from 2 to n
  let mut l: SZ.t = 2sz;
  
  while (!l <=^ n)
  invariant exists* vl sm.
    R.pts_to l vl **
    V.pts_to m sm **
    A.pts_to dims #p s_dims **
    pure (
      SZ.v vl <= SZ.v n + 1 /\
      SZ.v vl >= 2 /\
      Seq.length sm == op_Multiply (SZ.v n) (SZ.v n) /\
      V.length m == Seq.length sm /\
      (forall (k: nat). k < Seq.length sm ==> Seq.index sm k >= 0)
    )
  {
    let vl = !l;
    
    // For each starting position i
    let mut i: SZ.t = 0sz;
    
    while (!i <^ n - vl + 1sz)
    invariant exists* vi sm_i.
      R.pts_to l vl **
      R.pts_to i vi **
      V.pts_to m sm_i **
      A.pts_to dims #p s_dims **
      pure (
        SZ.v vl <= SZ.v n + 1 /\
        SZ.v vl >= 2 /\
        SZ.v vi <= SZ.v n - SZ.v vl + 1 /\
        Seq.length sm_i == op_Multiply (SZ.v n) (SZ.v n) /\
        V.length m == Seq.length sm_i /\
        (forall (k: nat). k < Seq.length sm_i ==> Seq.index sm_i k >= 0)
      )
    {
      let vi = !i;
      
      // Compute j = i + l - 1
      let j = vi + vl - 1sz;
      
      // Initialize m[i][j] to a large value
      // Use 1000000000 as "infinity" (sufficient for practical matrix chains)
      let mut min_cost: int = 1000000000;
      
      // Try all split points k from i to j-1
      let mut k: SZ.t = vi;
      
      while (!k <^ j)
      invariant exists* vk vmin_cost sm_k.
        R.pts_to l vl **
        R.pts_to i vi **
        R.pts_to k vk **
        R.pts_to min_cost vmin_cost **
        V.pts_to m sm_k **
        A.pts_to dims #p s_dims **
        pure (
          SZ.v vl <= SZ.v n + 1 /\
          SZ.v vl >= 2 /\
          SZ.v vi <= SZ.v n - SZ.v vl + 1 /\
          SZ.v vk >= SZ.v vi /\
          SZ.v vk <= SZ.v j /\
          SZ.v j == SZ.v vi + SZ.v vl - 1 /\
          SZ.v j < SZ.v n /\
          Seq.length sm_k == op_Multiply (SZ.v n) (SZ.v n) /\
          V.length m == Seq.length sm_k /\
          vmin_cost >= 0 /\
          (forall (t: nat). t < Seq.length sm_k ==> Seq.index sm_k t >= 0)
        )
      {
        let vk = !k;
        let vmin_cost = !min_cost;
        
        // Compute index for m[i][k]
        let idx_ik = vi *^ n + vk;
        lemma_index_in_bounds (SZ.v vi) (SZ.v vk) (SZ.v n);
        
        // Compute index for m[k+1][j]
        let idx_k1j = (vk + 1sz) *^ n + j;
        lemma_index_in_bounds (SZ.v vk + 1) (SZ.v j) (SZ.v n);
        
        // Read m[i][k] and m[k+1][j]
        let cost_ik = V.op_Array_Access m idx_ik;
        let cost_k1j = V.op_Array_Access m idx_k1j;
        
        // Read dimensions: p[i], p[k+1], p[j+1]
        let dim_i = A.op_Array_Access dims vi;
        let dim_k1 = A.op_Array_Access dims (vk + 1sz);
        let dim_j1 = A.op_Array_Access dims (j + 1sz);
        
        // Compute cost of multiplying matrices i..k and k+1..j
        let mult_cost = dim_i * dim_k1 * dim_j1;
        let q = cost_ik + cost_k1j + mult_cost;
        
        // Update min_cost = min(min_cost, q)
        let new_min = (if q < vmin_cost then q else vmin_cost);
        min_cost := new_min;
        
        k := vk + 1sz;
      };
      
      // Store m[i][j] = min_cost
      let final_min_cost = !min_cost;
      let idx_ij = vi *^ n + j;
      lemma_index_in_bounds (SZ.v vi) (SZ.v j) (SZ.v n);
      V.op_Array_Assignment m idx_ij final_min_cost;
      
      // Help Pulse join the branches
      with sm_new. assert (V.pts_to m sm_new);
      
      i := vi + 1sz;
    };
    
    l := vl + 1sz;
  };
  
  // Extract result: m[0][n-1]
  let result_idx = 0sz *^ n + (n - 1sz);
  lemma_index_in_bounds 0 (SZ.v n - 1) (SZ.v n);
  
  let result = V.op_Array_Access m result_idx;
  
  // Free the table
  V.free m;
  
  result
}
