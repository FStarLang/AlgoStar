(*
   Matrix Multiply — Verified Implementation in Pulse (CLRS §4.2, pp. 75–76)

   Functional correctness: C[i][j] = Σ_{k=0}^{n-1} A[i][k] * B[k][j]
   Complexity: exactly n³ multiply-add operations.

   Uses GhostReference.ref nat for the tick counter -- fully erased at runtime.

   NO admits. NO assumes.
*)

module CLRS.Ch04.MatrixMultiply.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open Pulse.Lib.Reference
open FStar.Classical
open CLRS.Ch04.MatrixMultiply.Spec

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Pulse Implementation ==========

//SNIPPET_START: matrix_multiply_sig
// Matrix multiplication: C = A × B
fn matrix_multiply
  (#pa #pb: perm)
  (a: array int)
  (b: array int)
  (c: array int)
  (#sa: Ghost.erased (Seq.seq int))
  (#sb: Ghost.erased (Seq.seq int))
  (#sc: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to a #pa sa **
    A.pts_to b #pb sb **
    A.pts_to c sc **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length sa == SZ.v n * SZ.v n /\
      Seq.length sb == SZ.v n * SZ.v n /\
      Seq.length sc == SZ.v n * SZ.v n
    )
  ensures exists* sc' (cf: nat).
    A.pts_to a #pa sa **
    A.pts_to b #pb sb **
    A.pts_to c sc' **
    GR.pts_to ctr cf **
    pure (
      mat_mul_correct sa sb sc' (SZ.v n) /\
      complexity_bounded_cubic cf (reveal c0) (SZ.v n)
    )
//SNIPPET_END: matrix_multiply_sig
{
  let mut i: SZ.t = 0sz;
  
  while (!i <^ n)
  invariant exists* vi sc_i (vc : nat).
    R.pts_to i vi **
    A.pts_to a #pa sa **
    A.pts_to b #pb sb **
    A.pts_to c sc_i **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sc_i == SZ.v n * SZ.v n /\
      mat_mul_partial_ij sa sb sc_i (SZ.v n) (SZ.v vi) 0 /\
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi * SZ.v n * SZ.v n
    )
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    
    let mut j: SZ.t = 0sz;
    
    while (!j <^ n)
    invariant exists* vj sc_ij (vc_ij : nat).
      R.pts_to i vi **
      R.pts_to j vj **
      A.pts_to a #pa sa **
      A.pts_to b #pb sb **
      A.pts_to c sc_ij **
      GR.pts_to ctr vc_ij **
      pure (
        SZ.v vi < SZ.v n /\
        SZ.v vj <= SZ.v n /\
        Seq.length sc_ij == SZ.v n * SZ.v n /\
        mat_mul_partial_ij sa sb sc_ij (SZ.v n) (SZ.v vi) (SZ.v vj) /\
        vc_ij >= reveal c0 /\
        vc_ij - reveal c0 == SZ.v vi * SZ.v n * SZ.v n + SZ.v vj * SZ.v n
      )
    decreases (SZ.v n - SZ.v !j)
    {
      let vj = !j;
      
      index_bounds_lemma (SZ.v n) (SZ.v vi) (SZ.v vj) 0;
      
      assert pure (SZ.fits (SZ.v vi * SZ.v n + SZ.v vj));
      let idx_c = vi *^ n +^ vj;
      assert pure (SZ.v idx_c < SZ.v n * SZ.v n);
      
      // Initialize C[i][j] = 0 = dot_product_spec ... 0
      A.op_Array_Assignment c idx_c 0;
      
      let mut k: SZ.t = 0sz;
      
      while (!k <^ n)
      invariant exists* vk sc_ijk (vc_ijk : nat).
        R.pts_to i vi **
        R.pts_to j vj **
        R.pts_to k vk **
        A.pts_to a #pa sa **
        A.pts_to b #pb sb **
        A.pts_to c sc_ijk **
        GR.pts_to ctr vc_ijk **
        pure (
          SZ.v vi < SZ.v n /\
          SZ.v vj < SZ.v n /\
          SZ.v vk <= SZ.v n /\
          Seq.length sc_ijk == SZ.v n * SZ.v n /\
          SZ.v idx_c == flat_index (SZ.v n) (SZ.v vi) (SZ.v vj) /\
          SZ.v idx_c < SZ.v n * SZ.v n /\
          mat_mul_partial_k sa sb sc_ijk (SZ.v n) (SZ.v vi) (SZ.v vj) (SZ.v vk) /\
          mat_mul_partial_ij sa sb sc_ijk (SZ.v n) (SZ.v vi) (SZ.v vj) /\
          vc_ijk >= reveal c0 /\
          vc_ijk - reveal c0 == SZ.v vi * SZ.v n * SZ.v n + SZ.v vj * SZ.v n + SZ.v vk
        )
      decreases (SZ.v n - SZ.v !k)
      {
        let vk = !k;
        
        assert pure (SZ.v vk < SZ.v n);
        
        index_bounds_lemma (SZ.v n) (SZ.v vi) (SZ.v vj) (SZ.v vk);
        
        assert pure (SZ.fits (SZ.v vi * SZ.v n + SZ.v vk));
        let idx_a = vi *^ n +^ vk;
        
        assert pure (SZ.fits (SZ.v vk * SZ.v n + SZ.v vj));
        let idx_b = vk *^ n +^ vj;
        
        let a_val = A.op_Array_Access a idx_a;
        let b_val = A.op_Array_Access b idx_b;
        let c_val = A.op_Array_Access c idx_c;
        
        let new_val = c_val + a_val * b_val;
        
        A.op_Array_Assignment c idx_c new_val;

        // Count the multiply-add — one ghost tick
        tick ctr;
        
        k := vk +^ 1sz;
      };
      
      j := vj +^ 1sz;
    };
    
    i := vi +^ 1sz;
  };
  
  ()
}

#pop-options
