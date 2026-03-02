(*
   Matrix Chain Multiplication - Verified implementation in Pulse
   
   Given dimensions p[0..n] for n matrices (matrix i has dimensions p[i] × p[i+1]),
   find the minimum number of scalar multiplications needed to multiply them.
   
   Bottom-up dynamic programming approach from CLRS Chapter 15.
   
   Proves: result == mc_outer (Seq.create (n*n) 0) s_dims n 2
   i.e., the result equals the pure Floyd-Warshall-style imperative mirror spec.
   
   Complexity: O(n³) — specifically exactly (n³-n)/6 innermost-loop iterations.
   The bound is proven on the pure loop model in MatrixChain.Complexity.fst.
   Unlike RodCutting.fst and LCS.fst, the Pulse implementation does not carry
   a ghost tick counter; the loop structure is identical to the pure model,
   so the O(n³) bound transfers directly.
   
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

#set-options "--z3rlimit 40"

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Pure Specification (imperative mirror) ==========

//SNIPPET_START: mc_spec
// mc_inner_k: process split points k..j-1, accumulating min cost
// Reads from table but doesn't modify it
let rec mc_inner_k (table: Seq.seq int) (dims: Seq.seq int) (n i j k: nat) (min_acc: int)
  : Tot int (decreases (j - k))
  = if k >= j || i >= n || j >= n || Seq.length table <> n * n || Seq.length dims <> n + 1 then min_acc
    else
      let cost_ik = Seq.index table (i * n + k) in
      let cost_k1j = Seq.index table ((k + 1) * n + j) in
      let dim_i = Seq.index dims i in
      let dim_k1 = Seq.index dims (k + 1) in
      let dim_j1 = Seq.index dims (j + 1) in
      let q = cost_ik + cost_k1j + dim_i * dim_k1 * dim_j1 in
      let new_min = if q < min_acc then q else min_acc in
      mc_inner_k table dims n i j (k + 1) new_min

// mc_inner_i: process starting positions i..n-l, updating table for chain length l
let rec mc_inner_i (table: Seq.seq int) (dims: Seq.seq int) (n l i: nat)
  : Tot (Seq.seq int) (decreases (n - l + 1 - i))
  = if l < 2 || i + l > n || Seq.length table <> n * n || Seq.length dims <> n + 1 then table
    else
      let j = i + l - 1 in
      let min_cost = mc_inner_k table dims n i j i 1000000000 in
      let table' = Seq.upd table (i * n + j) min_cost in
      mc_inner_i table' dims n l (i + 1)

// mc_outer: process chain lengths l=l..n
let rec mc_outer (table: Seq.seq int) (dims: Seq.seq int) (n l: nat)
  : Tot (Seq.seq int) (decreases (n + 1 - l))
  = if l > n || Seq.length table <> n * n || Seq.length dims <> n + 1 then table
    else
      let table' = mc_inner_i table dims n l 0 in
      mc_outer table' dims n (l + 1)
//SNIPPET_END: mc_spec

// Length preservation lemmas
let rec lemma_mc_inner_i_len (table: Seq.seq int) (dims: Seq.seq int) (n l i: nat)
  : Lemma (ensures Seq.length (mc_inner_i table dims n l i) == Seq.length table)
          (decreases (n - l + 1 - i))
  = if l < 2 || i + l > n || Seq.length table <> n * n || Seq.length dims <> n + 1 then ()
    else begin
      let j = i + l - 1 in
      let min_cost = mc_inner_k table dims n i j i 1000000000 in
      lemma_mc_inner_i_len (Seq.upd table (i * n + j) min_cost) dims n l (i + 1)
    end

let rec lemma_mc_outer_len (table: Seq.seq int) (dims: Seq.seq int) (n l: nat)
  : Lemma (ensures Seq.length (mc_outer table dims n l) == Seq.length table)
          (decreases (n + 1 - l))
  = if l > n || Seq.length table <> n * n || Seq.length dims <> n + 1 then ()
    else begin
      lemma_mc_inner_i_len table dims n l 0;
      lemma_mc_outer_len (mc_inner_i table dims n l 0) dims n (l + 1)
    end

// The final result (what the postcondition expresses)
let mc_result (dims: Seq.seq int) (n: nat) : int =
  if n = 0 || Seq.length dims <> n + 1 then 0
  else begin
    let table = Seq.create (n * n) 0 in
    let final_table = mc_outer table dims n 2 in
    lemma_mc_outer_len table dims n 2;
    assert (Seq.length final_table == n * n);
    Seq.index final_table (n - 1)
  end

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

//SNIPPET_START: mc_sig
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
    pure (
      result == mc_result s_dims (SZ.v n)
    )
//SNIPPET_END: mc_sig
{
  // Allocate DP table m[0..n-1][0..n-1] as flat array of size n*n
  let table_size = n *^ n;
  lemma_table_size_positive (SZ.v n);
  
  let m = V.alloc 0 table_size;
  
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
      // Remaining work from current state = total work from initial state
      mc_outer sm s_dims (SZ.v n) (SZ.v vl) == 
        mc_outer (Seq.create (SZ.v n * SZ.v n) 0) s_dims (SZ.v n) 2
    )
  decreases (Prims.op_Addition (SZ.v n) 1 `Prims.op_Subtraction` SZ.v !l)
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
        // Remaining i-work then remaining l-work = total
        mc_outer (mc_inner_i sm_i s_dims (SZ.v n) (SZ.v vl) (SZ.v vi)) s_dims (SZ.v n) (SZ.v vl + 1) ==
          mc_outer (Seq.create (SZ.v n * SZ.v n) 0) s_dims (SZ.v n) 2
      )
    decreases (SZ.v n `Prims.op_Subtraction` SZ.v !i)
    {
      let vi = !i;
      
      // Compute j = i + l - 1
      let j = vi + vl - 1sz;
      
      // Initialize m[i][j] to a large value
      let mut min_cost: int = 1000000000;
      
      // Capture the table state at i-loop entry for use after k-loop
      with sm_i_entry. assert (V.pts_to m sm_i_entry);
      
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
          // k-loop doesn't modify table
          sm_k == sm_i_entry /\
          // accumulator tracks remaining k-work
          mc_inner_k sm_k s_dims (SZ.v n) (SZ.v vi) (SZ.v j) (SZ.v vk) vmin_cost ==
            mc_inner_k sm_k s_dims (SZ.v n) (SZ.v vi) (SZ.v j) (SZ.v vi) 1000000000
        )
      decreases (SZ.v j `Prims.op_Subtraction` SZ.v !k)
      {
        let vk = !k;
        let vmin_cost = !min_cost;
        
        // Compute index for m[i][k]
        let idx_ik = vi *^ n + vk;
        lemma_index_in_bounds (SZ.v vi) (SZ.v vk) (SZ.v n);
        
        // Compute index for m[k+1][j]
        lemma_index_in_bounds (SZ.v vk + 1) (SZ.v j) (SZ.v n);
        let idx_k1j = (vk + 1sz) *^ n + j;
        
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
      
      i := vi + 1sz;
    };
    
    l := vl + 1sz;
  };
  
  // Extract result: m[0][n-1]
  let result_idx = 0sz *^ n + (n - 1sz);
  lemma_index_in_bounds 0 (SZ.v n - 1) (SZ.v n);
  
  // Get the ghost sequence for the final table
  with sm_final. assert (V.pts_to m sm_final);
  
  // Help SMT: mc_outer at vl > n is the identity
  lemma_mc_outer_len (Seq.create (SZ.v n * SZ.v n) 0) s_dims (SZ.v n) 2;
  
  let result = V.op_Array_Access m result_idx;
  
  // Free the table
  V.free m;
  
  result
}
