(*
   Longest Common Subsequence - Verified implementation in Pulse
   
   Computes the length of the longest common subsequence of two sequences
   using dynamic programming.
   
   NO admits. NO assumes.
*)

module CLRS.Ch15.LCS
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.Vec
open FStar.SizeT

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Pure Specifications ==========
// IMPORTANT: These MUST come BEFORE `open Pulse.Lib.BoundedIntegers`
// because BoundedIntegers interferes with `decreases` clauses on nat parameters.

// Pure spec: length of LCS of x[0..i-1] and y[0..j-1]
//SNIPPET_START: lcs_spec
let rec lcs_length (x y: Seq.seq int) (i j: nat) : Tot int (decreases i + j) =
  if i = 0 || j = 0 then 0
  else if i <= Seq.length x && j <= Seq.length y && 
          Seq.index x (i - 1) = Seq.index y (j - 1) then
    1 + lcs_length x y (i - 1) (j - 1)
  else
    let l1 = lcs_length x y (i - 1) j in
    let l2 = lcs_length x y i (j - 1) in
    if l1 >= l2 then l1 else l2
//SNIPPET_END: lcs_spec

// Pure spec: build the DP table row by row
let lcs_at (x y: Seq.seq int) (i j: nat) : int =
  if i <= Seq.length x && j <= Seq.length y then lcs_length x y i j else 0

// Pure spec: index into flattened table
let tbl_idx (i j: nat) (n1: nat) : nat = op_Multiply i n1 + j

// Lemma: lcs_length is non-negative
let rec lcs_length_nonneg (x y: Seq.seq int) (i j: nat)
  : Lemma (ensures lcs_length x y i j >= 0)
          (decreases i + j)
  = if i = 0 || j = 0 then ()
    else if i <= Seq.length x && j <= Seq.length y &&
            Seq.index x (i - 1) = Seq.index y (j - 1) then
      lcs_length_nonneg x y (i - 1) (j - 1)
    else begin
      lcs_length_nonneg x y (i - 1) j;
      lcs_length_nonneg x y i (j - 1)
    end

// Lemma: relating DP recurrence to lcs_length  
let lcs_recurrence_correct (x y: Seq.seq int) (i j: nat) 
  (val_diag val_up val_left: int)
  : Lemma 
    (requires 
      i > 0 /\ j > 0 /\
      i <= Seq.length x /\ j <= Seq.length y /\
      val_diag == lcs_length x y (i - 1) (j - 1) /\
      val_up == lcs_length x y (i - 1) j /\
      val_left == lcs_length x y i (j - 1))
    (ensures 
      (if Seq.index x (i - 1) = Seq.index y (j - 1) then val_diag + 1
       else if val_up >= val_left then val_up
       else val_left) == lcs_length x y i j)
  = ()

// DP table correctness predicate:
// All cells (r,c) with r < i, or r == i and c < j, are correct
let lcs_table_correct (x y: Seq.seq int) (tbl: Seq.seq int) (m n: nat) (i j: nat) : prop =
  let n1 = n + 1 in
  Seq.length tbl == op_Multiply (m + 1) n1 /\
  i <= m + 1 /\ j <= n + 1 /\
  (forall (r c: nat). (r < i \/ (r == i /\ c < j)) ==> r <= m ==> c <= n ==>
    Seq.index tbl (op_Multiply r n1 + c) == lcs_length x y r c)

// Lemma: updating table[i*(n+1)+j] with lcs_length value preserves correctness
// and advances to (i, j+1)
#push-options "--z3rlimit 20"
let lcs_table_update_preserves (x y: Seq.seq int) (tbl: Seq.seq int) (m n i j: nat) (v: int)
  : Lemma 
    (requires 
      lcs_table_correct x y tbl m n i j /\
      i <= m /\ j <= n /\
      v == lcs_length x y i j)
    (ensures (
      let idx = op_Multiply i (n + 1) + j in
      let tbl' = Seq.upd tbl idx v in
      lcs_table_correct x y tbl' m n i (j + 1)))
  = let n1 = n + 1 in
    let idx = op_Multiply i n1 + j in
    let tbl' = Seq.upd tbl idx v in
    assert (forall (r c: nat). ((r < i \/ (r == i /\ c < j + 1)) /\ r <= m /\ c <= n) ==>
      (let idx2 = op_Multiply r n1 + c in
       Seq.index tbl' idx2 == lcs_length x y r c))
#pop-options

// Lemma: advancing to next row resets column
let lcs_table_next_row (x y: Seq.seq int) (tbl: Seq.seq int) (m n i: nat)
  : Lemma 
    (requires lcs_table_correct x y tbl m n i (n + 1) /\ i <= m)
    (ensures lcs_table_correct x y tbl m n (i + 1) 0)
  = ()

// Combined lemma for DP value correctness
// This handles both base case (i=0||j=0) and recursive case in one lemma
// to avoid ghost propagation issues in Pulse if/else
let lcs_step_correct (x y: Seq.seq int) (tbl: Seq.seq int) (m n i j: nat) (value: int)
  : Lemma
    (requires
      i <= m /\ j <= n /\
      m == Seq.length x /\ n == Seq.length y /\
      lcs_table_correct x y tbl m n i j /\
      (i = 0 \/ j = 0 ==> value == 0) /\
      (i > 0 /\ j > 0 ==> (
        let n1 = n + 1 in
        let val_diag = Seq.index tbl (op_Multiply (i - 1) n1 + (j - 1)) in
        let val_up = Seq.index tbl (op_Multiply (i - 1) n1 + j) in
        let val_left = Seq.index tbl (op_Multiply i n1 + (j - 1)) in
        let xi = Seq.index x (i - 1) in
        let yj = Seq.index y (j - 1) in
        value == (if xi = yj then val_diag + 1
                  else if val_up >= val_left then val_up
                  else val_left))))
    (ensures value == lcs_length x y i j)
  = if i = 0 || j = 0 then ()
    else ()

open Pulse.Lib.BoundedIntegers

// ========== Helper Lemmas ==========

// Bound checking lemmas
let lemma_index_in_bounds (i j m n: nat)
  : Lemma (requires i <= m /\ j <= n)
          (ensures op_Multiply i (n + 1) + j < op_Multiply (m + 1) (n + 1))
  = ()

let lemma_table_size_positive (m n: nat)
  : Lemma (op_Multiply (m + 1) (n + 1) > 0)
  = ()

// ========== Main Implementation ==========

//SNIPPET_START: lcs_sig
fn lcs 
  (#px #py: perm)
  (x: A.array int) 
  (y: A.array int) 
  (m: SZ.t) 
  (n: SZ.t)
  (#sx #sy: erased (Seq.seq int))
  requires 
    A.pts_to x #px sx ** 
    A.pts_to y #py sy ** 
    pure (
      SZ.v m == Seq.length sx /\ 
      SZ.v m == A.length x /\
      SZ.v n == Seq.length sy /\ 
      SZ.v n == A.length y /\
      SZ.v m > 0 /\ SZ.v n > 0 /\
      SZ.fits (op_Multiply (SZ.v m + 1) (SZ.v n + 1))
    )
  returns result: int
  ensures 
    A.pts_to x #px sx ** 
    A.pts_to y #py sy ** 
    pure (result == lcs_length sx sy (SZ.v m) (SZ.v n))
//SNIPPET_END: lcs_sig
{
  // Allocate DP table: size (m+1) * (n+1)
  let m_plus_1 = m + 1sz;
  let n_plus_1 = n + 1sz;
  let table_size = m_plus_1 *^ n_plus_1;
  lemma_table_size_positive (SZ.v m) (SZ.v n);
  
  let table = V.alloc 0 table_size;
  
  // Outer loop: iterate over rows i from 0 to m
  let mut i: SZ.t = 0sz;
  
  while (!i <=^ m)
  invariant exists* vi stable.
    R.pts_to i vi **
    V.pts_to table stable **
    A.pts_to x #px sx **
    A.pts_to y #py sy **
    pure (
      SZ.v vi <= SZ.v m + 1 /\
      Seq.length stable == op_Multiply (SZ.v m + 1) (SZ.v n + 1) /\
      V.length table == Seq.length stable /\
      lcs_table_correct sx sy stable (SZ.v m) (SZ.v n) (SZ.v vi) 0
    )
  {
    let vi = !i;
    
    // Inner loop: iterate over columns j from 0 to n
    let mut j: SZ.t = 0sz;
    
    while (!j <=^ n)
    invariant exists* vj stable_inner.
      R.pts_to i vi **
      R.pts_to j vj **
      V.pts_to table stable_inner **
      A.pts_to x #px sx **
      A.pts_to y #py sy **
      pure (
        SZ.v vi <= SZ.v m /\
        SZ.v vj <= SZ.v n + 1 /\
        Seq.length stable_inner == op_Multiply (SZ.v m + 1) (SZ.v n + 1) /\
        V.length table == Seq.length stable_inner /\
        lcs_table_correct sx sy stable_inner (SZ.v m) (SZ.v n) (SZ.v vi) (SZ.v vj)
      )
    {
      let vj = !j;
      
      // Bind the table contents from the invariant
      with s_before. assert (V.pts_to table s_before);
      
      // Compute table[i][j] = table[vi *^ (n+1) + vj]
      let idx = vi *^ (n + 1sz) + vj;
      
      // Prove that idx is in bounds
      lemma_index_in_bounds (SZ.v vi) (SZ.v vj) (SZ.v m) (SZ.v n);
      
      // Compute value: for base case (vi=0 or vj=0) use 0
      // For recursive case, read from previously computed cells
      // Use safe indices that are always in bounds
      let safe_vi_m1: SZ.t = (if vi >^ 0sz then vi - 1sz else vi);
      let safe_vj_m1: SZ.t = (if vj >^ 0sz then vj - 1sz else vj);
      
      lemma_index_in_bounds (SZ.v safe_vi_m1) (SZ.v safe_vj_m1) (SZ.v m) (SZ.v n);
      lemma_index_in_bounds (SZ.v safe_vi_m1) (SZ.v vj) (SZ.v m) (SZ.v n);
      lemma_index_in_bounds (SZ.v vi) (SZ.v safe_vj_m1) (SZ.v m) (SZ.v n);
      
      let idx_diag = safe_vi_m1 *^ (n + 1sz) + safe_vj_m1;
      let idx_up = safe_vi_m1 *^ (n + 1sz) + vj;
      let idx_left = vi *^ (n + 1sz) + safe_vj_m1;
      
      // These reads may return garbage for base case, but we won't use the values
      let val_diag = V.op_Array_Access table idx_diag;
      let val_up = V.op_Array_Access table idx_up;
      let val_left = V.op_Array_Access table idx_left;
      
      // Read from input arrays (safe because safe_vi_m1 < m when vi > 0, and vi is always in range)
      // When m=0, vi=0 so we're in base case. When vi>0, safe_vi_m1 = vi-1 < m.
      let xi = A.op_Array_Access x safe_vi_m1;
      let yj = A.op_Array_Access y safe_vj_m1;
      
      // Compute value based on DP recurrence (single expression, no branching for ghost)
      let value_to_store: int = 
        (if vi = 0sz || vj = 0sz then 0
         else if xi = yj then val_diag + 1
         else if val_up >= val_left then val_up
         else val_left);
      
      // Prove value matches lcs_length
      lcs_step_correct sx sy s_before (SZ.v m) (SZ.v n) (SZ.v vi) (SZ.v vj) value_to_store;
      
      // Write the value
      V.op_Array_Assignment table idx value_to_store;
      with s_after. assert (V.pts_to table s_after);
      
      // Prove the update advances table correctness
      lcs_table_update_preserves sx sy s_before (SZ.v m) (SZ.v n) (SZ.v vi) (SZ.v vj) value_to_store;
      assert (pure (Seq.equal s_after (Seq.upd s_before (SZ.v idx) value_to_store)));
      
      j := vj + 1sz;
    };
    
    // Advance to next row
    with s_row_done. assert (V.pts_to table s_row_done);
    lcs_table_next_row sx sy s_row_done (SZ.v m) (SZ.v n) (SZ.v vi);
    
    i := vi + 1sz;
  };
  
  // Extract result: table[m][n] = table[m *^ (n+1) + n]
  let result_idx = m *^ (n + 1sz) + n;
  lemma_index_in_bounds (SZ.v m) (SZ.v n) (SZ.v m) (SZ.v n);
  
  let result = V.op_Array_Access table result_idx;
  
  // Free the table
  V.free table;
  
  result
}
