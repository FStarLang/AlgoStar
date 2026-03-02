module CLRS.Ch04.MatrixMultiply
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open Pulse.Lib.Reference
open FStar.Mul
open FStar.Classical

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

(* 
 * Verified implementation of SQUARE-MATRIX-MULTIPLY from CLRS §4.2 (pp. 75–76).
 * 
 * Functional correctness: C[i][j] = Σ_{k=0}^{n-1} A[i][k] * B[k][j]
 * Complexity: exactly n³ multiply-add operations.
 *
 * NO admits. NO assumes.
 *)

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"

// ========== Ghost tick ==========

//SNIPPET_START: ghost_tick
let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}
//SNIPPET_END: ghost_tick

// ========== Pure Specification ==========

//SNIPPET_START: spec
// Flat index for row-major n×n matrix
let flat_index (n i j: nat) : nat = i * n + j

// Arithmetic helper
let index_bounds_lemma (n: nat{n > 0}) (i j k: nat) : Lemma
  (requires i < n /\ j < n /\ k < n)
  (ensures flat_index n i k < n * n /\ flat_index n k j < n * n /\ flat_index n i j < n * n) =
  ()

// Dot product spec: sum of a[i][k] * b[k][j] for k in [0, limit)
let rec dot_product_spec (sa sb: Seq.seq int) (n i j: nat) (limit: nat)
  : Tot int (decreases limit)
  = if limit = 0 || i >= n || j >= n || n = 0 then 0
    else if limit > n then dot_product_spec sa sb n i j n
    else let k = limit - 1 in
         if flat_index n i k >= Seq.length sa || flat_index n k j >= Seq.length sb then 0
         else dot_product_spec sa sb n i j (limit - 1) +
              Seq.index sa (flat_index n i k) * Seq.index sb (flat_index n k j)

// Result correctness: c[i][j] == dot_product_spec for all computed positions
// Note: this dot_product_spec operates on flat (row-major) sequences.
// See also: CLRS.Ch04.Strassen.dot_product which defines the equivalent
// sum over the seq-of-seq matrix representation.
let mat_mul_correct (sa sb sc: Seq.seq int) (n: nat) : prop =
  Seq.length sc == n * n /\
  (forall (i j: nat). i < n /\ j < n ==> 
    Seq.index sc (flat_index n i j) == dot_product_spec sa sb n i j n)

// Partial result: for positions (i',j') < (i,j) in row-major order, result is correct
// For position (i,j), partial dot product up to k is correct
let mat_mul_partial_k (sa sb sc: Seq.seq int) (n i j k: nat) : prop =
  Seq.length sc == n * n /\ i < n /\ j < n /\ k <= n /\
  Seq.index sc (flat_index n i j) == dot_product_spec sa sb n i j k

// All positions in rows < ri, plus positions (ri, col) for col < cj, are correct
let mat_mul_partial_ij (sa sb sc: Seq.seq int) (n ri cj: nat) : prop =
  Seq.length sc == n * n /\
  (forall (i j: nat). (i < ri \/ (i == ri /\ j < cj)) /\ i < n /\ j < n ==> 
    Seq.index sc (flat_index n i j) == dot_product_spec sa sb n i j n)
//SNIPPET_END: spec

// ========== Complexity bound predicate ==========

//SNIPPET_START: complexity_bound
let complexity_bounded_cubic (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n * n * n
//SNIPPET_END: complexity_bound

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
  //SNIPPET_START: outer_loop
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
  //SNIPPET_END: outer_loop
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
      
      //SNIPPET_START: inner_loop
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
          // Partial dot product correctness
          mat_mul_partial_k sa sb sc_ijk (SZ.v n) (SZ.v vi) (SZ.v vj) (SZ.v vk) /\
          // Previous positions unchanged
          mat_mul_partial_ij sa sb sc_ijk (SZ.v n) (SZ.v vi) (SZ.v vj) /\
          // Complexity: vc - c0 == vi*n*n + vj*n + vk
          vc_ijk >= reveal c0 /\
          vc_ijk - reveal c0 == SZ.v vi * SZ.v n * SZ.v n + SZ.v vj * SZ.v n + SZ.v vk
        )
      decreases (SZ.v n - SZ.v !k)
      //SNIPPET_END: inner_loop
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
