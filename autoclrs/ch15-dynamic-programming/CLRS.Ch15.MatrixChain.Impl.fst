(*
   Matrix Chain Multiplication - Verified implementation in Pulse
   
   Given dimensions p[0..n] for n matrices (matrix i has dimensions p[i] × p[i+1]),
   find the minimum number of scalar multiplications needed to multiply them.
   
   Bottom-up dynamic programming approach from CLRS Chapter 15.
   
   Proves BOTH functional correctness AND O(n³) complexity:
   - Correctness: result == mc_result dims n (the pure imperative mirror spec)
   - Complexity: exactly mc_iterations n innermost-loop iterations,
     where mc_iterations n ≤ n³ (proven in MatrixChain.Complexity)
   
   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   
   NO admits. NO assumes.
*)

module CLRS.Ch15.MatrixChain.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.Vec
open FStar.SizeT
open FStar.Mul

#set-options "--z3rlimit 60 --split_queries always"

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

open CLRS.Ch15.MatrixChain.Spec
open CLRS.Ch15.MatrixChain.Complexity
module MCL = CLRS.Ch15.MatrixChain.Lemmas

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Complexity helpers ==========

// Remaining k-loop iterations for chain length l, starting from position i
let mc_remaining_i (n l i: nat) : nat =
  if l >= 2 && l <= n && i + l <= n + 1 then (n - l + 1 - i) * (l - 1)
  else 0

let mc_remaining_i_step (n l i: nat)
  : Lemma (requires l >= 2 /\ l <= n /\ i + l <= n)
          (ensures mc_remaining_i n l i == (l - 1) + mc_remaining_i n l (i + 1))
  = ()

let mc_remaining_i_end (n l: nat)
  : Lemma (requires l >= 2 /\ l <= n)
          (ensures mc_remaining_i n l (n - l + 1) == 0)
  = ()

let mc_inner_sum_to_remaining (n l: nat)
  : Lemma (requires l >= 2 /\ l <= n)
          (ensures mc_inner_sum n l == mc_remaining_i n l 0 + mc_inner_sum n (l + 1))
  = mc_inner_sum_step n l

// Bridge: when sentinel is large enough, mc_result equals the true recursive optimum
let mc_result_eq_mc_cost (dims: Seq.seq int) (n: nat)
  : Lemma (requires n > 0 /\ Seq.length dims == n + 1 /\
                    MCL.all_costs_bounded dims n n 1000000000)
          (ensures mc_result dims n == MCL.mc_cost dims 0 (n - 1))
  = MCL.mc_spec_equiv dims n

// ========== Main Implementation ==========

open Pulse.Lib.BoundedIntegers

//SNIPPET_START: mc_sig
fn matrix_chain_order
  (#p: perm)
  (dims: A.array int)
  (n: SZ.t)
  (#s_dims: erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to dims #p s_dims **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n + 1 == Seq.length s_dims /\
      SZ.v n + 1 == A.length dims /\
      SZ.v n > 0 /\
      SZ.fits (op_Multiply (SZ.v n) (SZ.v n)) /\
      (forall (i: nat). i < Seq.length s_dims ==> Seq.index s_dims i > 0)
    )
  returns result: int
  ensures exists* (cf: nat).
    A.pts_to dims #p s_dims **
    GR.pts_to ctr cf **
    pure (
      result == mc_result s_dims (SZ.v n) /\
      result >= 0 /\
      mc_complexity_bounded cf (reveal c0) (SZ.v n)
    )
//SNIPPET_END: mc_sig
{
  // Prove non-negativity of the pure spec result
  mc_result_nonneg s_dims (SZ.v n);
  // Allocate DP table m[0..n-1][0..n-1] as flat array of size n*n
  let table_size = n *^ n;
  lemma_table_size_positive (SZ.v n);
  
  let m = V.alloc 0 table_size;
  
  // Main DP: iterate over chain lengths l from 2 to n
  let mut l: SZ.t = 2sz;

  // Establish: mc_inner_sum n 2 == mc_iterations n
  mc_inner_sum_at_start (SZ.v n);
  
  while (!l <=^ n)
  invariant exists* vl sm (vc: nat).
    R.pts_to l vl **
    V.pts_to m sm **
    GR.pts_to ctr vc **
    A.pts_to dims #p s_dims **
    pure (
      SZ.v vl <= SZ.v n + 1 /\
      SZ.v vl >= 2 /\
      Seq.length sm == op_Multiply (SZ.v n) (SZ.v n) /\
      V.length m == Seq.length sm /\
      mc_outer sm s_dims (SZ.v n) (SZ.v vl) == 
        mc_outer (Seq.create (SZ.v n * SZ.v n) 0) s_dims (SZ.v n) 2 /\
      vc >= reveal c0 /\
      vc + mc_inner_sum (SZ.v n) (SZ.v vl) == reveal c0 + mc_iterations (SZ.v n)
    )
  decreases (Prims.op_Addition (SZ.v n) 1 `Prims.op_Subtraction` SZ.v !l)
  {
    let vl = !l;
    
    // For each starting position i
    let mut i: SZ.t = 0sz;

    // Transition: outer invariant -> middle invariant
    mc_inner_sum_to_remaining (SZ.v n) (SZ.v vl);
    
    while (!i <^ n - vl + 1sz)
    invariant exists* vi sm_i (vc_i: nat).
      R.pts_to l vl **
      R.pts_to i vi **
      V.pts_to m sm_i **
      GR.pts_to ctr vc_i **
      A.pts_to dims #p s_dims **
      pure (
        SZ.v vl <= SZ.v n + 1 /\
        SZ.v vl >= 2 /\
        SZ.v vi <= SZ.v n - SZ.v vl + 1 /\
        Seq.length sm_i == op_Multiply (SZ.v n) (SZ.v n) /\
        V.length m == Seq.length sm_i /\
        mc_outer (mc_inner_i sm_i s_dims (SZ.v n) (SZ.v vl) (SZ.v vi)) s_dims (SZ.v n) (SZ.v vl + 1) ==
          mc_outer (Seq.create (SZ.v n * SZ.v n) 0) s_dims (SZ.v n) 2 /\
        vc_i >= reveal c0 /\
        vc_i + mc_remaining_i (SZ.v n) (SZ.v vl) (SZ.v vi) + mc_inner_sum (SZ.v n) (SZ.v vl + 1) == reveal c0 + mc_iterations (SZ.v n)
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

      // Transition: middle invariant -> inner invariant
      mc_remaining_i_step (SZ.v n) (SZ.v vl) (SZ.v vi);
      
      // Try all split points k from i to j-1
      let mut k: SZ.t = vi;
      
      while (!k <^ j)
      invariant exists* vk vmin_cost sm_k (vc_k: nat).
        R.pts_to l vl **
        R.pts_to i vi **
        R.pts_to k vk **
        R.pts_to min_cost vmin_cost **
        V.pts_to m sm_k **
        GR.pts_to ctr vc_k **
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
          sm_k == sm_i_entry /\
          mc_inner_k sm_k s_dims (SZ.v n) (SZ.v vi) (SZ.v j) (SZ.v vk) vmin_cost ==
            mc_inner_k sm_k s_dims (SZ.v n) (SZ.v vi) (SZ.v j) (SZ.v vi) 1000000000 /\
          vc_k >= reveal c0 /\
          vc_k + (SZ.v j - SZ.v vk) + mc_remaining_i (SZ.v n) (SZ.v vl) (SZ.v vi + 1) + mc_inner_sum (SZ.v n) (SZ.v vl + 1) == reveal c0 + mc_iterations (SZ.v n)
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

        // Count the k-iteration — one ghost tick
        tick ctr;
        
        k := vk + 1sz;
      };
      
      // Store m[i][j] = min_cost
      let final_min_cost = !min_cost;
      let idx_ij = vi *^ n + j;
      lemma_index_in_bounds (SZ.v vi) (SZ.v j) (SZ.v n);
      
      V.op_Array_Assignment m idx_ij final_min_cost;
      
      i := vi + 1sz;
    };

    // Transition: middle invariant back to outer invariant
    mc_remaining_i_end (SZ.v n) (SZ.v vl);
    
    l := vl + 1sz;
  };
  
  // After outer loop: l > n, so mc_inner_sum n l == 0, hence vc == c0 + mc_iterations n
  let vl_final = !l;
  mc_inner_sum_zero (SZ.v n) (SZ.v vl_final);
  
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
