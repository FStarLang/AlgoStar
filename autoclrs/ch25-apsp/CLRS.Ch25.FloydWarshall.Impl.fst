module CLRS.Ch25.FloydWarshall.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open CLRS.Ch25.FloydWarshall.Spec

#set-options "--z3rlimit 25 --split_queries always"

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Ghost tick (erased at extraction) ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

open Pulse.Lib.BoundedIntegers

// Helper: row-major index is within n*n (NL arithmetic)
let index_bound_lemma (a b n: nat)
  : Lemma (requires a < n /\ b < n)
          (ensures a * n + b < n * n)
  = FStar.Math.Lemmas.lemma_mult_le_right n a (n - 1);
    FStar.Math.Lemmas.distributivity_sub_left n 1 n

// Helper: (a+1)*n == a*n + n (NL arithmetic)
let succ_mul_lemma (a n: nat)
  : Lemma (ensures (a + 1) * n == a * n + n)
  = FStar.Math.Lemmas.distributivity_add_left a 1 n

// Helper: (a+1)*n*n == a*n*n + n*n (NL arithmetic)
let succ_mul2_lemma (a n: nat)
  : Lemma (ensures (a + 1) * n * n == a * n * n + n * n)
  = FStar.Math.Lemmas.distributivity_add_left a 1 n;
    FStar.Math.Lemmas.distributivity_add_left (a * n) n n

// ========== Floyd-Warshall with correctness + complexity ==========

//SNIPPET_START: floyd_warshall_sig
fn floyd_warshall
  (dist: array int)
  (#contents: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to dist contents **
    GR.pts_to ctr c0 **
    pure (
      Seq.length contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns _:unit
  ensures exists* contents' (cf: nat).
    A.pts_to dist contents' **
    GR.pts_to ctr cf **
    pure (
      Seq.length contents' == SZ.v n * SZ.v n /\
      // Functional correctness: output == pure Floyd-Warshall computation
      contents' == fw_outer contents (SZ.v n) 0 /\
      // Complexity: exactly n³ relaxation operations
      fw_complexity_bounded cf (reveal c0) (SZ.v n)
    )
//SNIPPET_END: floyd_warshall_sig
{
  let mut k : SZ.t = 0sz;

//SNIPPET_START: outer_loop
  while (!k <^ n)
  invariant exists* vk contents_k (vc : nat).
    R.pts_to k vk **
    A.pts_to dist contents_k **
    GR.pts_to ctr vc **
    pure (
      SZ.v vk <= SZ.v n /\
      Seq.length contents_k == SZ.v n * SZ.v n /\
      fw_outer contents_k (SZ.v n) (SZ.v vk) == fw_outer contents (SZ.v n) 0 /\
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vk * SZ.v n * SZ.v n
    )
  decreases (SZ.v n `Prims.op_Subtraction` SZ.v !k)
//SNIPPET_END: outer_loop
  {
    let vk = !k;
    let mut i : SZ.t = 0sz;

//SNIPPET_START: inner_i_loop
    while (!i <^ n)
    invariant exists* vi contents_i (vc_i : nat).
      R.pts_to i vi **
      A.pts_to dist contents_i **
      GR.pts_to ctr vc_i **
      pure (
        SZ.v vi <= SZ.v n /\
        Seq.length contents_i == SZ.v n * SZ.v n /\
        fw_outer (fw_inner_i contents_i (SZ.v n) (SZ.v vk) (SZ.v vi)) (SZ.v n) (SZ.v vk + 1)
          == fw_outer contents (SZ.v n) 0 /\
        vc_i >= reveal c0 /\
        vc_i - reveal c0 == SZ.v vk * SZ.v n * SZ.v n + SZ.v vi * SZ.v n
      )
    decreases (SZ.v n `Prims.op_Subtraction` SZ.v !i)
//SNIPPET_END: inner_i_loop
    {
      let vi = !i;
      let mut j : SZ.t = 0sz;

      // Read d_ik once (cached for entire j-loop, matching pure spec)
      let idx_ik = vi *^ n +^ vk;
      let d_ik = A.op_Array_Access dist idx_ik;

//SNIPPET_START: inner_j_loop
      while (!j <^ n)
      invariant exists* vj contents_j (vc_j : nat).
        R.pts_to j vj **
        A.pts_to dist contents_j **
        GR.pts_to ctr vc_j **
        pure (
          SZ.v vj <= SZ.v n /\
          Seq.length contents_j == SZ.v n * SZ.v n /\
          fw_outer
            (fw_inner_i (fw_inner_j contents_j (SZ.v n) (SZ.v vk) (SZ.v vi) (SZ.v vj) d_ik)
                        (SZ.v n) (SZ.v vk) (SZ.v vi + 1))
            (SZ.v n) (SZ.v vk + 1)
            == fw_outer contents (SZ.v n) 0 /\
          vc_j >= reveal c0 /\
          vc_j - reveal c0 == SZ.v vk * SZ.v n * SZ.v n + SZ.v vi * SZ.v n + SZ.v vj
        )
      decreases (SZ.v n `Prims.op_Subtraction` SZ.v !j)
//SNIPPET_END: inner_j_loop
      {
        let vj = !j;

        // NL arithmetic: row-major index bounds
        index_bound_lemma (SZ.v vi) (SZ.v vj) (SZ.v n);
        index_bound_lemma (SZ.v vk) (SZ.v vj) (SZ.v n);

        // Compute indices
        let idx_ij = vi *^ n +^ vj;
        let idx_kj = vk *^ n +^ vj;

        // Read values
        let d_ij = A.op_Array_Access dist idx_ij;
        let d_kj = A.op_Array_Access dist idx_kj;

        // Compute new value unconditionally (use Prims ops for krml extraction)
        let via_k = Prims.op_Addition d_ik d_kj;
        let new_val = (if Prims.op_LessThan via_k d_ij then via_k else d_ij);

        // Write unconditionally (no conditional writes)
        A.op_Array_Assignment dist idx_ij new_val;

        // Count the relaxation — one ghost tick
        tick ctr;

        j := vj +^ 1sz;
      };

      // NL arithmetic: (vi+1)*n == vi*n + n
      succ_mul_lemma (SZ.v vi) (SZ.v n);
      assert (pure ((SZ.v vi + 1) * SZ.v n == SZ.v vi * SZ.v n + SZ.v n));

      i := vi +^ 1sz;
    };

    // NL arithmetic: (vk+1)*n*n == vk*n*n + n*n
    succ_mul2_lemma (SZ.v vk) (SZ.v n);
    assert (pure ((SZ.v vk + 1) * SZ.v n * SZ.v n == SZ.v vk * SZ.v n * SZ.v n + SZ.v n * SZ.v n));

    k := vk +^ 1sz;
  }
}
