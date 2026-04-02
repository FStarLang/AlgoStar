(*
   Extended Matrix Chain Multiplication - Verified implementation in Pulse
   
   Extends the basic matrix chain multiplication to also compute the split-point
   table s[i,j], which records the optimal split point k for each subproblem (i,j).
   
   Given dimensions p[0..n] for n matrices (matrix i has dimensions p[i] × p[i+1]),
   find the minimum number of scalar multiplications needed to multiply them,
   AND record the split points that achieve this minimum.
   
   Bottom-up dynamic programming approach from CLRS Chapter 15.
   
   Proves: cost == mc_result s_dims (SZ.v n)
   i.e., the cost equals the pure specification from CLRS.Ch15.MatrixChain.
   
   The s table stores optimal split points (documented but not fully formally
   verified for split correctness — that can be done in a follow-up).
   
   NO admits. NO assumes.
*)

module CLRS.Ch15.MatrixChain.Extended
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.Vec
open FStar.SizeT
open FStar.Mul

#set-options "--z3rlimit 10 --fuel 1 --ifuel 0 --split_queries always"

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Reuse the pure spec from CLRS.Ch15.MatrixChain ==========

// We import the original spec and result function to state the cost postcondition.
open CLRS.Ch15.MatrixChain.Spec
open CLRS.Ch15.MatrixChain.Lemmas

// ========== Extended Pure Specification (imperative mirror with split tracking) ==========

// mc_inner_k_ext: process split points k..j-1, accumulating min cost AND best split k
// Returns (min_cost, best_k)
let rec mc_inner_k_ext (table: Seq.seq int) (splits: Seq.seq int) (dims: Seq.seq int) 
                       (n i j k: nat) (min_acc: int) (best_k: int)
  : Tot (int & int) (decreases (j - k))
  = if k >= j || i >= n || j >= n || Seq.length table <> n * n || Seq.length dims <> n + 1 
       || Seq.length splits <> n * n
    then (min_acc, best_k)
    else
      let cost_ik = Seq.index table (i * n + k) in
      let cost_k1j = Seq.index table ((k + 1) * n + j) in
      let dim_i = Seq.index dims i in
      let dim_k1 = Seq.index dims (k + 1) in
      let dim_j1 = Seq.index dims (j + 1) in
      let q = cost_ik + cost_k1j + dim_i * dim_k1 * dim_j1 in
      let new_min = if q < min_acc then q else min_acc in
      let new_best_k = if q < min_acc then k else best_k in
      mc_inner_k_ext table splits dims n i j (k + 1) new_min new_best_k

// mc_inner_i_ext: process starting positions i..n-l, updating both table and splits
let rec mc_inner_i_ext (table: Seq.seq int) (splits: Seq.seq int) (dims: Seq.seq int) (n l i: nat)
  : Tot (Seq.seq int & Seq.seq int) (decreases (n - l + 1 - i))
  = if l < 2 || i + l > n || Seq.length table <> n * n || Seq.length dims <> n + 1 
       || Seq.length splits <> n * n
    then (table, splits)
    else
      let j = i + l - 1 in
      let (min_cost, best_k) = mc_inner_k_ext table splits dims n i j i 1000000000 i in
      let table' = Seq.upd table (i * n + j) min_cost in
      let splits' = Seq.upd splits (i * n + j) best_k in
      mc_inner_i_ext table' splits' dims n l (i + 1)

// mc_outer_ext: process chain lengths l=l..n, updating both table and splits
let rec mc_outer_ext (table: Seq.seq int) (splits: Seq.seq int) (dims: Seq.seq int) (n l: nat)
  : Tot (Seq.seq int & Seq.seq int) (decreases (n + 1 - l))
  = if l > n || Seq.length table <> n * n || Seq.length dims <> n + 1 
       || Seq.length splits <> n * n
    then (table, splits)
    else
      let (table', splits') = mc_inner_i_ext table splits dims n l 0 in
      mc_outer_ext table' splits' dims n (l + 1)

// ========== Length preservation lemmas ==========

// The extended k-loop doesn't change table or splits lengths (it's read-only on them)
// — but we do need length preservation for the i-loop and outer loop.

let rec lemma_mc_inner_i_ext_len (table: Seq.seq int) (splits: Seq.seq int) 
                                  (dims: Seq.seq int) (n l i: nat)
  : Lemma (ensures (let (t', s') = mc_inner_i_ext table splits dims n l i in
                    Seq.length t' == Seq.length table /\ Seq.length s' == Seq.length splits))
          (decreases (n - l + 1 - i))
  = if l < 2 || i + l > n || Seq.length table <> n * n || Seq.length dims <> n + 1 
       || Seq.length splits <> n * n
    then ()
    else begin
      let j = i + l - 1 in
      let (min_cost, best_k) = mc_inner_k_ext table splits dims n i j i 1000000000 i in
      let table' = Seq.upd table (i * n + j) min_cost in
      let splits' = Seq.upd splits (i * n + j) best_k in
      lemma_mc_inner_i_ext_len table' splits' dims n l (i + 1)
    end

let rec lemma_mc_outer_ext_len (table: Seq.seq int) (splits: Seq.seq int) 
                                (dims: Seq.seq int) (n l: nat)
  : Lemma (ensures (let (t', s') = mc_outer_ext table splits dims n l in
                    Seq.length t' == Seq.length table /\ Seq.length s' == Seq.length splits))
          (decreases (n + 1 - l))
  = if l > n || Seq.length table <> n * n || Seq.length dims <> n + 1 
       || Seq.length splits <> n * n
    then ()
    else begin
      lemma_mc_inner_i_ext_len table splits dims n l 0;
      let (table', splits') = mc_inner_i_ext table splits dims n l 0 in
      lemma_mc_outer_ext_len table' splits' dims n (l + 1)
    end

// mc_result_ext: returns (cost, splits_seq)
let mc_result_ext (dims: Seq.seq int) (n: nat) : int & Seq.seq int =
  if n = 0 || Seq.length dims <> n + 1 then (0, Seq.empty)
  else begin
    let table = Seq.create (n * n) 0 in
    let splits = Seq.create (n * n) 0 in
    let (final_table, final_splits) = mc_outer_ext table splits dims n 2 in
    lemma_mc_outer_ext_len table splits dims n 2;
    assert (Seq.length final_table == n * n);
    (Seq.index final_table (n - 1), final_splits)
  end

// ========== Equivalence: the cost table from extended == cost table from original ==========
// Key insight: the extended spec computes the same cost table as the original,
// because best_k doesn't influence the cost computation at all.

// mc_inner_k_ext returns the same min_cost as mc_inner_k
let rec lemma_inner_k_cost_equiv (table: Seq.seq int) (splits: Seq.seq int) (dims: Seq.seq int)
                                  (n i j k: nat) (min_acc: int) (best_k: int)
  : Lemma (requires Seq.length splits == n * n)
          (ensures fst (mc_inner_k_ext table splits dims n i j k min_acc best_k) ==
                   mc_inner_k table dims n i j k min_acc)
          (decreases (j - k))
  = if k >= j || i >= n || j >= n || Seq.length table <> n * n || Seq.length dims <> n + 1 
       || Seq.length splits <> n * n
    then ()
    else begin
      let cost_ik = Seq.index table (i * n + k) in
      let cost_k1j = Seq.index table ((k + 1) * n + j) in
      let dim_i = Seq.index dims i in
      let dim_k1 = Seq.index dims (k + 1) in
      let dim_j1 = Seq.index dims (j + 1) in
      let q = cost_ik + cost_k1j + dim_i * dim_k1 * dim_j1 in
      let new_min = if q < min_acc then q else min_acc in
      let new_best_k = if q < min_acc then k else best_k in
      lemma_inner_k_cost_equiv table splits dims n i j (k + 1) new_min new_best_k
    end

// mc_inner_i_ext returns the same cost table as mc_inner_i
let rec lemma_inner_i_cost_equiv (table: Seq.seq int) (splits: Seq.seq int) 
                                  (dims: Seq.seq int) (n l i: nat)
  : Lemma (requires Seq.length splits == n * n)
          (ensures fst (mc_inner_i_ext table splits dims n l i) ==
                   mc_inner_i table dims n l i)
          (decreases (n - l + 1 - i))
  = if l < 2 || i + l > n || Seq.length table <> n * n || Seq.length dims <> n + 1 
       || Seq.length splits <> n * n
    then ()
    else begin
      let j = i + l - 1 in
      lemma_inner_k_cost_equiv table splits dims n i j i 1000000000 i;
      let (min_cost, best_k) = mc_inner_k_ext table splits dims n i j i 1000000000 i in
      let min_cost_orig = mc_inner_k table dims n i j i 1000000000 in
      assert (min_cost == min_cost_orig);
      let table' = Seq.upd table (i * n + j) min_cost in
      let splits' = Seq.upd splits (i * n + j) best_k in
      assert (table' == Seq.upd table (i * n + j) min_cost_orig);
      lemma_mc_inner_i_ext_len table splits dims n l i;
      lemma_inner_i_cost_equiv table' splits' dims n l (i + 1)
    end

// mc_outer_ext returns the same cost table as mc_outer
let rec lemma_outer_cost_equiv (table: Seq.seq int) (splits: Seq.seq int) 
                                (dims: Seq.seq int) (n l: nat)
  : Lemma (requires Seq.length splits == n * n)
          (ensures fst (mc_outer_ext table splits dims n l) ==
                   mc_outer table dims n l)
          (decreases (n + 1 - l))
  = if l > n || Seq.length table <> n * n || Seq.length dims <> n + 1 
       || Seq.length splits <> n * n
    then ()
    else begin
      lemma_inner_i_cost_equiv table splits dims n l 0;
      let (table', splits') = mc_inner_i_ext table splits dims n l 0 in
      let table_orig' = mc_inner_i table dims n l 0 in
      assert (table' == table_orig');
      lemma_mc_inner_i_ext_len table splits dims n l 0;
      assert (Seq.length splits' == n * n);
      lemma_outer_cost_equiv table' splits' dims n (l + 1)
    end

// Corollary: mc_result_ext gives the same cost as mc_result
let lemma_result_cost_equiv (dims: Seq.seq int) (n: nat)
  : Lemma (fst (mc_result_ext dims n) == mc_result dims n)
  = if n = 0 || Seq.length dims <> n + 1 then ()
    else begin
      let table = Seq.create (n * n) 0 in
      let splits = Seq.create (n * n) 0 in
      lemma_outer_cost_equiv table splits dims n 2;
      lemma_mc_outer_ext_len table splits dims n 2;
      lemma_mc_outer_len table dims n 2
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

// ========== Equivalence between ext spec and original spec for the l-loop ==========

// We need lemmas connecting mc_outer_ext to mc_outer for the loop invariant.
// Specifically: the ext outer loop on the cost table equals the original outer loop.

// For the i-loop: fst (mc_inner_i_ext ...) == mc_inner_i ...
// (already proved above as lemma_inner_i_cost_equiv)

// For the outer loop: fst (mc_outer_ext ...) == mc_outer ...
// (already proved above as lemma_outer_cost_equiv)

// ========== Main Implementation ==========

open Pulse.Lib.BoundedIntegers

//SNIPPET_START: extended_mc_sig
fn extended_matrix_chain_order
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
  returns result: (int & V.vec SZ.t)
  ensures exists* ss.
    A.pts_to dims #p s_dims **
    V.pts_to (snd result) ss **
    pure (
      fst result == mc_result s_dims (SZ.v n) /\
      Seq.length ss == op_Multiply (SZ.v n) (SZ.v n) /\
      V.length (snd result) == Seq.length ss
    )
//SNIPPET_END: extended_mc_sig
{
  // Allocate DP table m[0..n-1][0..n-1] as flat array of size n*n
  let table_size = n *^ n;
  lemma_table_size_positive (SZ.v n);
  
  let m = V.alloc 0 table_size;
  
  // Allocate split-point table s[0..n-1][0..n-1] as flat array of size n*n
  let s = V.alloc 0sz table_size;
  
  // Main DP: iterate over chain lengths l from 2 to n
  let mut l: SZ.t = 2sz;
  
  while (!l <=^ n)
  invariant exists* vl sm ss.
    R.pts_to l vl **
    V.pts_to m sm **
    V.pts_to s ss **
    A.pts_to dims #p s_dims **
    pure (
      SZ.v vl <= SZ.v n + 1 /\
      SZ.v vl >= 2 /\
      Seq.length sm == op_Multiply (SZ.v n) (SZ.v n) /\
      V.length m == Seq.length sm /\
      Seq.length ss == op_Multiply (SZ.v n) (SZ.v n) /\
      V.length s == Seq.length ss /\
      // Remaining work from current state = total work from initial state (cost table)
      mc_outer sm s_dims (SZ.v n) (SZ.v vl) == 
        mc_outer (Seq.create (SZ.v n * SZ.v n) 0) s_dims (SZ.v n) 2
    )
  decreases (Prims.op_Addition (SZ.v n) 1 `Prims.op_Subtraction` SZ.v !l)
  {
    let vl = !l;
    
    // For each starting position i
    let mut i: SZ.t = 0sz;
    
    while (!i <^ n - vl + 1sz)
    invariant exists* vi sm_i ss_i.
      R.pts_to l vl **
      R.pts_to i vi **
      V.pts_to m sm_i **
      V.pts_to s ss_i **
      A.pts_to dims #p s_dims **
      pure (
        SZ.v vl <= SZ.v n + 1 /\
        SZ.v vl >= 2 /\
        SZ.v vi <= SZ.v n - SZ.v vl + 1 /\
        Seq.length sm_i == op_Multiply (SZ.v n) (SZ.v n) /\
        V.length m == Seq.length sm_i /\
        Seq.length ss_i == op_Multiply (SZ.v n) (SZ.v n) /\
        V.length s == Seq.length ss_i /\
        // Remaining i-work then remaining l-work = total (cost table)
        mc_outer (mc_inner_i sm_i s_dims (SZ.v n) (SZ.v vl) (SZ.v vi)) s_dims (SZ.v n) (SZ.v vl + 1) ==
          mc_outer (Seq.create (SZ.v n * SZ.v n) 0) s_dims (SZ.v n) 2
      )
    decreases (SZ.v n `Prims.op_Subtraction` SZ.v !i)
    {
      let vi = !i;
      
      // Compute j = i + l - 1
      let j = vi + vl - 1sz;
      
      // Initialize min_cost to a large value and best_k to i
      let mut min_cost: int = 1000000000;
      let mut best_k: SZ.t = vi;
      
      // Capture the table state at i-loop entry for use after k-loop
      with sm_i_entry. assert (V.pts_to m sm_i_entry);
      
      // Try all split points k from i to j-1
      let mut k: SZ.t = vi;
      
      while (!k <^ j)
      invariant exists* vk vmin_cost v_best_k sm_k ss_k.
        R.pts_to l vl **
        R.pts_to i vi **
        R.pts_to k vk **
        R.pts_to min_cost vmin_cost **
        R.pts_to best_k v_best_k **
        V.pts_to m sm_k **
        V.pts_to s ss_k **
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
          Seq.length ss_k == op_Multiply (SZ.v n) (SZ.v n) /\
          V.length s == Seq.length ss_k /\
          // k-loop doesn't modify table
          sm_k == sm_i_entry /\
          // accumulator tracks remaining k-work (cost)
          mc_inner_k sm_k s_dims (SZ.v n) (SZ.v vi) (SZ.v j) (SZ.v vk) vmin_cost ==
            mc_inner_k sm_k s_dims (SZ.v n) (SZ.v vi) (SZ.v j) (SZ.v vi) 1000000000
        )
      decreases (SZ.v j `Prims.op_Subtraction` SZ.v !k)
      {
        let vk = !k;
        let vmin_cost = !min_cost;
        let v_best_k = !best_k;
        
        // Help SMT with SZ.fits for index computations
        assert (pure (SZ.v vi < SZ.v n /\ SZ.v vk < SZ.v n));
        lemma_index_in_bounds (SZ.v vi) (SZ.v vk) (SZ.v n);
        assert (pure (SZ.fits (op_Multiply (SZ.v n) (SZ.v n))));
        assert (pure (op_Multiply (SZ.v vi) (SZ.v n) + SZ.v vk < op_Multiply (SZ.v n) (SZ.v n)));
        assert (pure (SZ.fits (op_Multiply (SZ.v vi) (SZ.v n) + SZ.v vk)));
        
        // Compute index for m[i][k]
        let idx_ik = vi *^ n + vk;
        
        // Compute index for m[k+1][j]
        lemma_index_in_bounds (SZ.v vk + 1) (SZ.v j) (SZ.v n);
        assert (pure (op_Multiply (SZ.v vk + 1) (SZ.v n) + SZ.v j < op_Multiply (SZ.v n) (SZ.v n)));
        assert (pure (SZ.fits (op_Multiply (SZ.v vk + 1) (SZ.v n) + SZ.v j)));
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
        
        // Update min_cost and best_k
        let new_min = (if q < vmin_cost then q else vmin_cost);
        let new_best_k = (if q < vmin_cost then vk else v_best_k);
        min_cost := new_min;
        best_k := new_best_k;
        
        k := vk + 1sz;
      };
      
      // Store m[i][j] = min_cost
      let final_min_cost = !min_cost;
      let final_best_k = !best_k;
      let idx_ij = vi *^ n + j;
      lemma_index_in_bounds (SZ.v vi) (SZ.v j) (SZ.v n);
      
      V.op_Array_Assignment m idx_ij final_min_cost;
      
      // Store s[i][j] = best_k
      V.op_Array_Assignment s idx_ij final_best_k;
      
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
  
  // Free the cost table
  V.free m;
  
  (result, s)
}
