(*
   Rod Cutting — Verified implementation in Pulse

   Given a rod of length n and a price table where prices[i] is the price
   of a piece of length i+1, determine the maximum revenue obtainable by
   cutting up the rod and selling the pieces.

   Bottom-up dynamic programming approach from CLRS Chapter 15.

   Proves BOTH functional correctness AND O(n²) complexity:
   - Correctness: result == optimal_revenue prices n
   - Complexity: exactly n*(n+1)/2 inner-loop iterations

   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.

   NO admits. NO assumes.
*)

module CLRS.Ch15.RodCutting.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.Vec
open FStar.SizeT

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

open CLRS.Ch15.RodCutting.Spec

let lemma_triangle_step (n: nat)
  : Lemma (triangle n + (n + 1) == triangle (n + 1))
  = ()

// ========== Main Implementation ==========

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"

open Pulse.Lib.BoundedIntegers

//SNIPPET_START: rod_cutting_sig
fn rod_cutting
  (#p: perm)
  (prices: A.array nat)
  (n: SZ.t)
  (#s_prices: erased (Seq.seq nat))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to prices #p s_prices **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s_prices /\
      SZ.v n == A.length prices /\
      SZ.fits (SZ.v n + 1)
    )
  returns result: nat
  ensures exists* (cf: nat).
    A.pts_to prices #p s_prices **
    GR.pts_to ctr cf **
    pure (
      result == optimal_revenue s_prices (SZ.v n) /\
      rod_cutting_bounded cf (reveal c0) (SZ.v n)
    )
//SNIPPET_END: rod_cutting_sig
{
  let n_plus_1 = n + 1sz;
  let r = V.alloc (0 <: nat) n_plus_1;
  let mut j: SZ.t = 1sz;

  while (!j <=^ n)
  invariant exists* vj sr (vc : nat).
    R.pts_to j vj **
    V.pts_to r sr **
    GR.pts_to ctr vc **
    A.pts_to prices #p s_prices **
    pure (
      SZ.v vj >= 1 /\
      SZ.v vj <= SZ.v n + 1 /\
      Seq.length sr == SZ.v n + 1 /\
      V.length r == Seq.length sr /\
      dp_correct s_prices sr (SZ.v vj - 1) /\
      vc >= reveal c0 /\
      vc - reveal c0 == triangle (SZ.v vj - 1)
    )
  decreases (Prims.op_Addition (SZ.v n) 1 `Prims.op_Subtraction` SZ.v !j)
  {
    let vj = !j;
    let mut q: nat = 0;
    let mut i: SZ.t = 1sz;

    while (!i <=^ vj)
    invariant exists* vi vq sr_inner (vc_inner : nat).
      R.pts_to j vj **
      R.pts_to i vi **
      R.pts_to q vq **
      V.pts_to r sr_inner **
      GR.pts_to ctr vc_inner **
      A.pts_to prices #p s_prices **
      pure (
        SZ.v vj <= SZ.v n /\
        SZ.v vj >= 1 /\
        SZ.v vi >= 1 /\
        SZ.v vi <= SZ.v vj + 1 /\
        Seq.length sr_inner == SZ.v n + 1 /\
        V.length r == Seq.length sr_inner /\
        dp_correct s_prices sr_inner (SZ.v vj - 1) /\
        vq == accum_max s_prices sr_inner (SZ.v vj) (SZ.v vi - 1) /\
        vc_inner >= reveal c0 /\
        vc_inner - reveal c0 == triangle (SZ.v vj - 1) + (SZ.v vi - 1)
      )
    decreases (Prims.op_Addition (SZ.v vj) 1 `Prims.op_Subtraction` SZ.v !i)
    {
      let vi = !i;
      let vq = !q;

      let idx_price = vi - 1sz;
      let price_i = A.op_Array_Access prices idx_price;
      let r_j_minus_i = V.op_Array_Access r (vj - vi);
      let candidate = price_i + r_j_minus_i;
      let new_q = (if candidate > vq then candidate else vq);
      q := new_q;

      // Count the candidate evaluation — one ghost tick
      tick ctr;

      i := vi + 1sz;
    };

    let final_q = !q;
    with sr_pre. assert (V.pts_to r sr_pre);
    accum_max_dp_correct s_prices sr_pre (SZ.v vj);
    V.op_Array_Assignment r vj final_q;
    with sr_new. assert (V.pts_to r sr_new);

    // After inner loop: vc - c0 == triangle(vj-1) + vj == triangle(vj)
    lemma_triangle_step (SZ.v vj - 1);

    j := vj + 1sz;
  };

  let result = V.op_Array_Access r n;
  V.free r;
  result
}

#pop-options
