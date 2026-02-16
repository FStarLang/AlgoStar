(*
   Rod Cutting - Verified implementation in Pulse
   
   Given a rod of length n and a price table where prices[i] is the price
   of a piece of length i+1, determine the maximum revenue obtainable by
   cutting up the rod and selling the pieces.
   
   Bottom-up dynamic programming approach from CLRS Chapter 15.
   
   Functional correctness: result == optimal_revenue prices n
   
   NO admits. NO assumes.
*)

module CLRS.Ch15.RodCutting
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

//SNIPPET_START: rod_cutting_spec
// ========== Pure Specification ==========

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"

// Accumulated max: max over i in [1, limit] of (prices[i-1] + r[j-i])
// r is a sequence of subproblem values
let rec accum_max (prices: Seq.seq int) (r: Seq.seq int) (j: nat) (limit: nat)
  : Tot int (decreases limit)
  = if limit = 0 || j = 0 then 0
    else if limit > j || limit - 1 >= Seq.length prices || j - limit >= Seq.length r 
    then accum_max prices r j (limit - 1)
    else let prev = accum_max prices r j (limit - 1) in
         let candidate = Seq.index prices (limit - 1) + Seq.index r (j - limit) in
         (if candidate >= prev then candidate else prev)

// Build the optimal revenue table bottom-up
// build_opt len prices = sequence of length len+1 where s[k] = optimal revenue for rod of length k
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

// Optimal revenue for a rod of length j
let optimal_revenue (prices: Seq.seq int) (j: nat) : int =
  Seq.index (build_opt prices j) j
//SNIPPET_END: rod_cutting_spec

// Lemma: build_opt is prefix-consistent
let rec build_opt_prefix (prices: Seq.seq int) (len: nat) (k: nat)
  : Lemma (requires k <= len)
          (ensures Seq.index (build_opt prices len) k == Seq.index (build_opt prices k) k)
          (decreases (len - k))
  = if k = len then ()
    else (
      let prev = build_opt prices (len - 1) in
      let opt_len = if len > Seq.length prices then 0 else accum_max prices prev len len in
      let result = Seq.snoc prev opt_len in
      // snoc: result = prev ++ [opt_len]
      // For k < Seq.length prev = len, result[k] = prev[k]
      assert (Seq.length prev == len);
      assert (k < len);
      // Seq.snoc s x = Seq.append s (Seq.create 1 x)
      // index (append s t) k = index s k when k < length s
      assert (Seq.index result k == Seq.index prev k);
      build_opt_prefix prices (len - 1) k
    )

// Corollary: optimal_revenue is well-defined (consistent across different build_opt calls)
let optimal_revenue_consistent (prices: Seq.seq int) (j: nat) (len: nat)
  : Lemma (requires j <= len)
          (ensures Seq.index (build_opt prices len) j == optimal_revenue prices j)
  = build_opt_prefix prices len j

// Lemma: accum_max is the same when using sequences that agree on relevant positions
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

// DP table correctness
let dp_correct (prices: Seq.seq int) (sr: Seq.seq int) (bound: nat) : prop =
  (forall (k: nat). k <= bound /\ k < Seq.length sr ==>
    Seq.index sr k == optimal_revenue prices k)

// Lemma: when DP table is correct for k < j, accum_max with DP table == optimal_revenue
let accum_max_dp_correct (prices: Seq.seq int) (sr: Seq.seq int) (j: nat)
  : Lemma (requires j > 0 /\ j <= Seq.length prices /\ Seq.length sr > j /\
                     dp_correct prices sr (j - 1))
          (ensures accum_max prices sr j j == optimal_revenue prices j)
  = let prev = build_opt prices (j - 1) in
    // Need: forall k < j. sr[k] == prev[k]
    // sr[k] == optimal_revenue prices k (from dp_correct)
    // prev[k] == optimal_revenue prices k (from build_opt_prefix, optimal_revenue_consistent)
    assert (Seq.length prev == j);
    let rec aux (k:nat) 
      : Lemma (requires k < j)
              (ensures Seq.index sr k == Seq.index prev k)
              (decreases k)
      = optimal_revenue_consistent prices k (j - 1)
    in
    // Apply to all k < j
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

// Nonneg lemmas
let rec accum_max_nonneg (prices: Seq.seq int) (r: Seq.seq int) (j: nat) (limit: nat)
  : Lemma (requires (forall (k:nat). k < Seq.length prices ==> Seq.index prices k >= 0) /\
                     (forall (k:nat). k < Seq.length r ==> Seq.index r k >= 0))
          (ensures accum_max prices r j limit >= 0)
          (decreases limit)
  = if limit = 0 || j = 0 then ()
    else if limit > j || limit - 1 >= Seq.length prices || j - limit >= Seq.length r 
    then accum_max_nonneg prices r j (limit - 1)
    else accum_max_nonneg prices r j (limit - 1)

// ========== Main Implementation ==========

open Pulse.Lib.BoundedIntegers

//SNIPPET_START: rod_cutting_sig
fn rod_cutting
  (#p: perm)
  (prices: A.array int)
  (n: SZ.t)
  (#s_prices: erased (Seq.seq int))
  requires
    A.pts_to prices #p s_prices **
    pure (
      SZ.v n == Seq.length s_prices /\
      SZ.v n == A.length prices /\
      SZ.v n > 0 /\
      SZ.fits (SZ.v n + 1) /\
      (forall (i: nat). i < Seq.length s_prices ==> Seq.index s_prices i >= 0)
    )
  returns result: int
  ensures
    A.pts_to prices #p s_prices **
    pure (result == optimal_revenue s_prices (SZ.v n))
//SNIPPET_END: rod_cutting_sig
{
  let n_plus_1 = n + 1sz;
  let r = V.alloc 0 n_plus_1;
  
  let mut j: SZ.t = 1sz;
  
  while (!j <=^ n)
  invariant exists* vj sr.
    R.pts_to j vj **
    V.pts_to r sr **
    A.pts_to prices #p s_prices **
    pure (
      SZ.v vj >= 1 /\
      SZ.v vj <= SZ.v n + 1 /\
      Seq.length sr == SZ.v n + 1 /\
      V.length r == Seq.length sr /\
      dp_correct s_prices sr (SZ.v vj - 1) /\
      (forall (k: nat). k < Seq.length sr ==> Seq.index sr k >= 0)
    )
  {
    let vj = !j;
    
    let mut q: int = 0;
    let mut i: SZ.t = 1sz;
    
    while (!i <=^ vj)
    invariant exists* vi vq sr_inner.
      R.pts_to j vj **
      R.pts_to i vi **
      R.pts_to q vq **
      V.pts_to r sr_inner **
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
        vq == accum_max s_prices sr_inner (SZ.v vj) (SZ.v vi - 1)
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
      
      i := vi + 1sz;
    };
    
    // After inner loop: q == accum_max s_prices sr vj vj == optimal_revenue s_prices vj
    let final_q = !q;
    
    with sr_pre. assert (V.pts_to r sr_pre);
    accum_max_dp_correct s_prices sr_pre (SZ.v vj);
    
    V.op_Array_Assignment r vj final_q;
    
    with sr_new. assert (V.pts_to r sr_new);
    
    j := vj + 1sz;
  };
  
  let result = V.op_Array_Access r n;
  
  V.free r;
  
  result
}

#pop-options
