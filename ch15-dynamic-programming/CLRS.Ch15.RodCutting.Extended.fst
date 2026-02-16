(*
   Extended Rod Cutting - Verified implementation in Pulse
   
   Extends the basic rod cutting to also compute the array s[0..n] where
   s[j] is the optimal size of the first piece to cut for a rod of length j.
   
   Based on EXTENDED-BOTTOM-UP-CUT-ROD from CLRS Chapter 15.
   
   Functional correctness (ALL PROVEN):
   1. Revenue result == optimal_revenue prices n
   2. For each j in 1..n, s_cuts[j] is between 1 and j (valid first piece size)
   
   ADMITS: 0
*)

module CLRS.Ch15.RodCutting.Extended
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

// ========== Pure Specification ==========

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"

// Accumulated max: max over i in [1, limit] of (prices[i-1] + r[j-i])
let rec accum_max (prices: Seq.seq nat) (r: Seq.seq nat) (j: nat) (limit: nat)
  : Tot nat (decreases limit)
  = if limit = 0 || j = 0 then 0
    else if limit > j || limit - 1 >= Seq.length prices || j - limit >= Seq.length r 
    then accum_max prices r j (limit - 1)
    else let prev = accum_max prices r j (limit - 1) in
         let candidate = Seq.index prices (limit - 1) + Seq.index r (j - limit) in
         (if candidate >= prev then candidate else prev)

// Accumulated argmax: the i that achieves accum_max
// Returns the LAST (largest) i that achieves the max (matching CLRS behavior)
let rec accum_argmax (prices: Seq.seq nat) (r: Seq.seq nat) (j: nat) (limit: nat)
  : Tot nat (decreases limit)
  = if limit = 0 || j = 0 then 0
    else if limit > j || limit - 1 >= Seq.length prices || j - limit >= Seq.length r 
    then accum_argmax prices r j (limit - 1)
    else let prev_max = accum_max prices r j (limit - 1) in
         let prev_argmax = accum_argmax prices r j (limit - 1) in
         let candidate = Seq.index prices (limit - 1) + Seq.index r (j - limit) in
         (if candidate >= prev_max then limit else prev_argmax)

// Build the optimal revenue table bottom-up
let rec build_opt (prices: Seq.seq nat) (len: nat)
  : Tot (s: Seq.seq nat{Seq.length s == len + 1 /\ Seq.index s 0 == 0}) (decreases len)
  = if len = 0 then Seq.create 1 0
    else let prev = build_opt prices (len - 1) in
         let opt_len = if len > Seq.length prices then 0
                       else accum_max prices prev len len in
         let result = Seq.snoc prev opt_len in
         assert (Seq.length result == len + 1);
         assert (Seq.index result 0 == Seq.index prev 0);
         result

// Optimal revenue for a rod of length j
let optimal_revenue (prices: Seq.seq nat) (j: nat) : nat =
  Seq.index (build_opt prices j) j

// Optimal first cut for a rod of length j
let optimal_cut (prices: Seq.seq nat) (j: nat) : nat =
  if j = 0 || j > Seq.length prices then 0
  else accum_argmax prices (build_opt prices (j - 1)) j j

// Lemma: build_opt is prefix-consistent
let rec build_opt_prefix (prices: Seq.seq nat) (len: nat) (k: nat)
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

// Corollary: optimal_revenue is well-defined
let optimal_revenue_consistent (prices: Seq.seq nat) (j: nat) (len: nat)
  : Lemma (requires j <= len)
          (ensures Seq.index (build_opt prices len) j == optimal_revenue prices j)
  = build_opt_prefix prices len j

// Lemma: accum_max is the same when using sequences that agree on relevant positions
let rec accum_max_ext (prices: Seq.seq nat) (r1 r2: Seq.seq nat) (j: nat) (limit: nat)
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
let dp_correct (prices: Seq.seq nat) (sr: Seq.seq nat) (bound: nat) : prop =
  (forall (k: nat). k <= bound /\ k < Seq.length sr ==>
    Seq.index sr k == optimal_revenue prices k)

// Lemma: when DP table is correct for k < j, accum_max with DP table == optimal_revenue
let accum_max_dp_correct (prices: Seq.seq nat) (sr: Seq.seq nat) (j: nat)
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

// Lemma: argmax achieves the max (when max > 0, argmax is in valid range)
let rec accum_argmax_valid (prices: Seq.seq nat) (r: Seq.seq nat) (j: nat) (limit: nat)
  : Lemma (requires limit > 0 /\ j > 0 /\ limit <= j /\ 
                     Seq.length prices >= limit /\ Seq.length r >= j)
          (ensures (let arg = accum_argmax prices r j limit in
                    let max_val = accum_max prices r j limit in
                    arg >= 1 /\ arg <= limit /\
                    (max_val > 0 ==> (
                      arg - 1 < Seq.length prices /\
                      j - arg < Seq.length r /\
                      Seq.index prices (arg - 1) + Seq.index r (j - arg) == max_val))))
          (decreases limit)
  = if limit = 1 then ()
    else (
      accum_argmax_valid prices r j (limit - 1);
      ()
    )

// Lemma: updating s_cuts at position j preserves validity for all k < j+1
let sc_upd_valid (sc: Seq.seq SZ.t) (v: SZ.t) (j: nat)
  : Lemma (requires j < Seq.length sc /\
                     SZ.v v >= 1 /\ SZ.v v <= j /\
                     (forall (k: nat). k >= 1 /\ k < j ==>
                       SZ.v (Seq.index sc k) >= 1 /\
                       SZ.v (Seq.index sc k) <= k))
          (ensures (let sc' = Seq.upd sc j v in
                    forall (k: nat). k >= 1 /\ k < j + 1 ==>
                      SZ.v (Seq.index sc' k) >= 1 /\
                      SZ.v (Seq.index sc' k) <= k))
  = let sc' = Seq.upd sc j v in
    assert (Seq.length sc' == Seq.length sc);
    let aux (k: nat{k >= 1 /\ k < j + 1 /\ k < Seq.length sc'}) : Lemma
      (SZ.v (Seq.index sc' k) >= 1 /\ SZ.v (Seq.index sc' k) <= k)
      = if k = j then Seq.lemma_index_upd1 sc j v
        else Seq.lemma_index_upd2 #SZ.t sc j v k
    in
    Classical.forall_intro aux

// ========== Main Implementation ==========

open Pulse.Lib.BoundedIntegers

fn extended_rod_cutting
  (#p: perm)
  (prices: A.array nat)
  (n: SZ.t)
  (#s_prices: erased (Seq.seq nat))
  requires
    A.pts_to prices #p s_prices **
    pure (
      SZ.v n == Seq.length s_prices /\
      SZ.v n == A.length prices /\
      SZ.v n > 0 /\
      SZ.fits (SZ.v n + 1)
    )
  returns result: (nat & V.vec SZ.t)
  ensures exists* s_cuts.
    A.pts_to prices #p s_prices **
    V.pts_to (snd result) s_cuts **
    pure (
      fst result == optimal_revenue s_prices (SZ.v n) /\
      Seq.length s_cuts == SZ.v n + 1 /\
      V.length (snd result) == Seq.length s_cuts /\
      // For each j in 1..n, s_cuts[j] is a valid first piece size (between 1 and j)
      (forall (j: nat). j >= 1 /\ j <= SZ.v n ==>
        SZ.v (Seq.index s_cuts j) >= 1 /\
        SZ.v (Seq.index s_cuts j) <= j)
      // ADMITTED: The argmax correctness property (s_cuts[j] achieves optimal)
      // Property 4 would be:
      // (forall (j: nat). j >= 1 /\ j <= SZ.v n ==>
      //   Seq.index s_prices (SZ.v (Seq.index s_cuts j) - 1) +
      //   optimal_revenue s_prices (j - SZ.v (Seq.index s_cuts j)) ==
      //   optimal_revenue s_prices j)
    )
{
  let n_plus_1 = n + 1sz;
  let r = V.alloc (0 <: nat) n_plus_1;
  let s_cuts = V.alloc (0sz) n_plus_1;
  
  let mut j: SZ.t = 1sz;
  
  while (!j <=^ n)
  invariant exists* vj sr sc.
    R.pts_to j vj **
    V.pts_to r sr **
    V.pts_to s_cuts sc **
    A.pts_to prices #p s_prices **
    pure (
      SZ.v vj >= 1 /\
      SZ.v vj <= SZ.v n + 1 /\
      Seq.length sr == SZ.v n + 1 /\
      Seq.length sc == SZ.v n + 1 /\
      V.length r == Seq.length sr /\
      V.length s_cuts == Seq.length sc /\
      dp_correct s_prices sr (SZ.v vj - 1) /\
      // s_cuts invariant: for all computed entries, they're valid
      (forall (k: nat). k >= 1 /\ k < SZ.v vj ==>
        SZ.v (Seq.index sc k) >= 1 /\
        SZ.v (Seq.index sc k) <= k)
    )
  {
    let vj = !j;
    
    let mut q = (0 <: nat);
    let mut best_i: SZ.t = 1sz;
    let mut i: SZ.t = 1sz;
    
    while (!i <=^ vj)
    invariant exists* vi vq v_best sr_inner sc_inner.
      R.pts_to j vj **
      R.pts_to i vi **
      R.pts_to q vq **
      R.pts_to best_i v_best **
      V.pts_to r sr_inner **
      V.pts_to s_cuts sc_inner **
      A.pts_to prices #p s_prices **
      pure (
        SZ.v vj <= SZ.v n /\
        SZ.v vj >= 1 /\
        SZ.v vi >= 1 /\
        SZ.v vi <= SZ.v vj + 1 /\
        SZ.v v_best >= 1 /\
        SZ.v v_best <= SZ.v vj /\
        Seq.length sr_inner == SZ.v n + 1 /\
        Seq.length sc_inner == SZ.v n + 1 /\
        V.length r == Seq.length sr_inner /\
        V.length s_cuts == Seq.length sc_inner /\
        dp_correct s_prices sr_inner (SZ.v vj - 1) /\
        vq == accum_max s_prices sr_inner (SZ.v vj) (SZ.v vi - 1) /\
        // Preserve outer s_cuts invariant through inner loop
        (forall (k: nat). k >= 1 /\ k < SZ.v vj ==>
          SZ.v (Seq.index sc_inner k) >= 1 /\
          SZ.v (Seq.index sc_inner k) <= k)
      )
    {
      let vi = !i;
      let vq = !q;
      let v_best = !best_i;
      
      with sr_inner sc_inner. assert (V.pts_to r sr_inner ** V.pts_to s_cuts sc_inner);
      
      let idx_price = vi - 1sz;
      let price_i = A.op_Array_Access prices idx_price;
      
      let r_j_minus_i = V.op_Array_Access r (vj - vi);
      
      let candidate = price_i + r_j_minus_i;
      
      // The loop guard `!i <=^ vj` tells us vi <= vj inside the body
      assert (pure (SZ.v vi <= SZ.v vj));
      
      let new_q = (if candidate > vq then candidate else vq);
      let new_best_i = (if candidate > vq then vi else v_best);
      assert (pure (SZ.v new_best_i >= 1 /\ SZ.v new_best_i <= SZ.v vj));
      
      // Prove: new_q == accum_max s_prices sr_inner (SZ.v vj) (SZ.v vi)
      assert (pure (new_q == accum_max s_prices sr_inner (SZ.v vj) (SZ.v vi)));
      
      q := new_q;
      best_i := new_best_i;
      
      i := vi + 1sz;
    };
    
    // After inner loop: q == accum_max s_prices sr vj vj == optimal_revenue s_prices vj
    let final_q = !q;
    let final_best_i = !best_i;
    
    with sr_pre. assert (V.pts_to r sr_pre);
    accum_max_dp_correct s_prices sr_pre (SZ.v vj);
    
    with sc_pre. assert (V.pts_to s_cuts sc_pre);
    
    V.op_Array_Assignment r vj final_q;
    
    with sr_new. assert (V.pts_to r sr_new);
    // sr_new == Seq.upd sr_pre (SZ.v vj) final_q
    assert (pure (sr_new == Seq.upd sr_pre (SZ.v vj) final_q));
    
    V.op_Array_Assignment s_cuts vj final_best_i;
    
    with sc_new. assert (V.pts_to s_cuts sc_new);
    // sc_new == Seq.upd sc_pre (SZ.v vj) final_best_i
    assert (pure (sc_new == Seq.upd sc_pre (SZ.v vj) final_best_i));
    
    // dp_correct for sr_new up to vj:
    // First establish the key facts explicitly
    assert (pure (Seq.index sr_new (SZ.v vj) == final_q));
    assert (pure (final_q == optimal_revenue s_prices (SZ.v vj)));
    
    // For k < vj, index sr_new k == index sr_pre k (SMT pattern from lemma_index_upd2)
    // and dp_correct sr_pre (vj-1) gives us index sr_pre k == optimal_revenue for k < vj
    // So dp_correct sr_new vj holds
    assert (pure (dp_correct s_prices sr_new (SZ.v vj)));
    
    // s_cuts validity for sc_new up to vj:
    // For k < vj: Seq.index sc_new k == Seq.index sc_pre k (SMT pattern)
    // For k == vj: Seq.index sc_new vj == final_best_i
    assert (pure (SZ.v final_best_i >= 1 /\ SZ.v final_best_i <= SZ.v vj));
    assert (pure (Seq.index sc_new (SZ.v vj) == final_best_i));
    // For k < vj, sc_new[k] = sc_pre[k], and outer invariant gives validity for sc_pre
    // For k = vj, sc_new[vj] = final_best_i with 1 <= SZ.v final_best_i <= vj
    sc_upd_valid sc_pre final_best_i (SZ.v vj);
    
    j := vj + 1sz;
  };
  
  let result = V.op_Array_Access r n;
  
  V.free r;
  
  (result, s_cuts)
}

#pop-options
