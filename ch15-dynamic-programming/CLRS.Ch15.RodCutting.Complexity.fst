(*
   Rod Cutting with Complexity Bound

   Proves O(n²) comparison complexity for the rod cutting DP algorithm.
   Specifically: exactly n*(n+1)/2 inner-loop iterations for a rod of length n.

   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Each inner-loop candidate evaluation gets one ghost tick.

   Also proves functional correctness (result == optimal_revenue prices n).

   NO admits. NO assumes.
*)

module CLRS.Ch15.RodCutting.Complexity
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

// ========== Pure Specification (same as RodCutting.fst) ==========

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"

let rec accum_max (prices: Seq.seq int) (r: Seq.seq int) (j: nat) (limit: nat)
  : Tot int (decreases limit)
  = if limit = 0 || j = 0 then 0
    else if limit > j || limit - 1 >= Seq.length prices || j - limit >= Seq.length r
    then accum_max prices r j (limit - 1)
    else let prev = accum_max prices r j (limit - 1) in
         let candidate = Seq.index prices (limit - 1) + Seq.index r (j - limit) in
         (if candidate >= prev then candidate else prev)

let rec build_opt (prices: Seq.seq int) (len: nat)
  : Tot (s: Seq.seq int{Seq.length s == len + 1 /\ Seq.index s 0 == 0}) (decreases len)
  = if len = 0 then Seq.create 1 0
    else let prev = build_opt prices (len - 1) in
         let opt_len = if len > Seq.length prices then 0
                       else accum_max prices prev len len in
         let result = Seq.snoc prev opt_len in
         assert (Seq.length result == len + 1);
         assert (Seq.index result 0 == Seq.index prev 0);
         result

let optimal_revenue (prices: Seq.seq int) (j: nat) : int =
  Seq.index (build_opt prices j) j

let rec build_opt_prefix (prices: Seq.seq int) (len: nat) (k: nat)
  : Lemma (requires k <= len)
          (ensures Seq.index (build_opt prices len) k == Seq.index (build_opt prices k) k)
          (decreases (len - k))
  = if k = len then ()
    else (
      let prev = build_opt prices (len - 1) in
      let opt_len = if len > Seq.length prices then 0 else accum_max prices prev len len in
      let result = Seq.snoc prev opt_len in
      assert (Seq.length prev == len);
      assert (k < len);
      assert (Seq.index result k == Seq.index prev k);
      build_opt_prefix prices (len - 1) k
    )

let optimal_revenue_consistent (prices: Seq.seq int) (j: nat) (len: nat)
  : Lemma (requires j <= len)
          (ensures Seq.index (build_opt prices len) j == optimal_revenue prices j)
  = build_opt_prefix prices len j

let rec accum_max_ext (prices: Seq.seq int) (r1 r2: Seq.seq int) (j: nat) (limit: nat)
  : Lemma (requires (forall (k:nat). k < j /\ k < Seq.length r1 /\ k < Seq.length r2 ==> Seq.index r1 k == Seq.index r2 k) /\
                     Seq.length r1 >= j /\ Seq.length r2 >= j)
          (ensures accum_max prices r1 j limit == accum_max prices r2 j limit)
          (decreases limit)
  = if limit = 0 || j = 0 then ()
    else if limit > j || limit - 1 >= Seq.length prices then
      accum_max_ext prices r1 r2 j (limit - 1)
    else (
      accum_max_ext prices r1 r2 j (limit - 1);
      assert (j - limit < j);
      assert (j - limit < Seq.length r1);
      assert (j - limit < Seq.length r2);
      assert (Seq.index r1 (j - limit) == Seq.index r2 (j - limit))
    )

let dp_correct (prices: Seq.seq int) (sr: Seq.seq int) (bound: nat) : prop =
  (forall (k: nat). k <= bound /\ k < Seq.length sr ==>
    Seq.index sr k == optimal_revenue prices k)

let accum_max_dp_correct (prices: Seq.seq int) (sr: Seq.seq int) (j: nat)
  : Lemma (requires j > 0 /\ j <= Seq.length prices /\ Seq.length sr > j /\
                     dp_correct prices sr (j - 1))
          (ensures accum_max prices sr j j == optimal_revenue prices j)
  = let prev = build_opt prices (j - 1) in
    assert (Seq.length prev == j);
    let rec aux (k:nat)
      : Lemma (requires k < j)
              (ensures Seq.index sr k == Seq.index prev k)
              (decreases k)
      = optimal_revenue_consistent prices k (j - 1)
    in
    let rec apply_aux (k:nat)
      : Lemma (requires k <= j)
              (ensures forall (i:nat). i < k ==> Seq.index sr i == Seq.index prev i)
              (decreases k)
      = if k = 0 then ()
        else (
          apply_aux (k - 1);
          aux (k - 1)
        )
    in
    apply_aux j;
    accum_max_ext prices sr prev j j

let rec accum_max_nonneg (prices: Seq.seq int) (r: Seq.seq int) (j: nat) (limit: nat)
  : Lemma (requires (forall (k:nat). k < Seq.length prices ==> Seq.index prices k >= 0) /\
                     (forall (k:nat). k < Seq.length r ==> Seq.index r k >= 0))
          (ensures accum_max prices r j limit >= 0)
          (decreases limit)
  = if limit = 0 || j = 0 then ()
    else if limit > j || limit - 1 >= Seq.length prices || j - limit >= Seq.length r
    then accum_max_nonneg prices r j (limit - 1)
    else accum_max_nonneg prices r j (limit - 1)

// ========== Complexity arithmetic ==========

// Triangle number: 1 + 2 + ... + n = n*(n+1)/2
let triangle (n: nat) : nat = op_Multiply n (Prims.op_Addition n 1) / 2

let lemma_triangle_step (n: nat)
  : Lemma (triangle n + (n + 1) == triangle (n + 1))
  = ()

// ========== Complexity bound predicate ==========
let rod_cutting_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == triangle n

// ========== Main Implementation with Complexity ==========

open Pulse.Lib.BoundedIntegers

fn rod_cutting_complexity
  (#p: perm)
  (prices: A.array int)
  (n: SZ.t)
  (#s_prices: erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to prices #p s_prices **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s_prices /\
      SZ.v n == A.length prices /\
      SZ.v n > 0 /\
      SZ.fits (SZ.v n + 1) /\
      (forall (i: nat). i < Seq.length s_prices ==> Seq.index s_prices i >= 0)
    )
  returns result: int
  ensures exists* (cf: nat).
    A.pts_to prices #p s_prices **
    GR.pts_to ctr cf **
    pure (
      result == optimal_revenue s_prices (SZ.v n) /\
      rod_cutting_bounded cf (reveal c0) (SZ.v n)
    )
{
  let n_plus_1 = n + 1sz;
  let r = V.alloc 0 n_plus_1;
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
      (forall (k: nat). k < Seq.length sr ==> Seq.index sr k >= 0) /\
      // Complexity: vc == c0 + triangle(vj - 1)
      vc >= reveal c0 /\
      vc - reveal c0 == triangle (SZ.v vj - 1)
    )
  {
    let vj = !j;
    let mut q: int = 0;
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
        vq >= 0 /\
        dp_correct s_prices sr_inner (SZ.v vj - 1) /\
        (forall (k: nat). k < Seq.length sr_inner ==> Seq.index sr_inner k >= 0) /\
        vq == accum_max s_prices sr_inner (SZ.v vj) (SZ.v vi - 1) /\
        // Complexity: inner ticks track i-1 within this j-iteration
        vc_inner >= reveal c0 /\
        vc_inner - reveal c0 == triangle (SZ.v vj - 1) + (SZ.v vi - 1)
      )
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
