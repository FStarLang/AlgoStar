(*
   Rod Cutting — Shared pure specification (CLRS Chapter 15)

   This module defines the DP recurrence for rod cutting and the key lemmas
   that establish its correctness. These definitions are shared by:
   - CLRS.Ch15.RodCutting (basic Pulse implementation)
   - CLRS.Ch15.RodCutting.Spec (optimality and substructure proofs)
   - CLRS.Ch15.RodCutting.Extended (extended Pulse implementation with cuts array)
*)

module CLRS.Ch15.RodCutting.DPSpec

open FStar.Seq
open FStar.Mul

// Accumulated max: max over i in [1, limit] of (prices[i-1] + r[j-i])
// r is a sequence of subproblem values
let rec accum_max (prices: seq nat) (r: seq nat) (j: nat) (limit: nat)
  : Tot nat (decreases limit)
  = if limit = 0 || j = 0 then 0
    else if limit > j || limit - 1 >= length prices || j - limit >= length r 
    then accum_max prices r j (limit - 1)
    else let prev = accum_max prices r j (limit - 1) in
         let candidate = index prices (limit - 1) + index r (j - limit) in
         (if candidate >= prev then candidate else prev)

// Build the optimal revenue table bottom-up
// build_opt len prices = sequence of length len+1 where s[k] = optimal revenue for rod of length k
let rec build_opt (prices: seq nat) (len: nat)
  : Tot (s: seq nat{length s == len + 1 /\ index s 0 == 0}) (decreases len)
  = if len = 0 then create 1 0
    else let prev = build_opt prices (len - 1) in
         let opt_len = if len > length prices then 0
                       else accum_max prices prev len len in
         let result = snoc prev opt_len in
         assert (length result == len + 1);
         assert (index result 0 == index prev 0);
         result

// Optimal revenue for a rod of length j
let optimal_revenue (prices: seq nat) (j: nat) : nat =
  index (build_opt prices j) j

// Lemma: build_opt is prefix-consistent
let rec build_opt_prefix (prices: seq nat) (len: nat) (k: nat)
  : Lemma (requires k <= len)
          (ensures index (build_opt prices len) k == index (build_opt prices k) k)
          (decreases (len - k))
  = if k = len then ()
    else (
      let prev = build_opt prices (len - 1) in
      let opt_len = if len > length prices then 0 else accum_max prices prev len len in
      let result = snoc prev opt_len in
      assert (length prev == len);
      assert (k < len);
      assert (index result k == index prev k);
      build_opt_prefix prices (len - 1) k
    )

// Corollary: optimal_revenue is well-defined (consistent across different build_opt calls)
let optimal_revenue_consistent (prices: seq nat) (j: nat) (len: nat)
  : Lemma (requires j <= len)
          (ensures index (build_opt prices len) j == optimal_revenue prices j)
  = build_opt_prefix prices len j

// Lemma: accum_max is extensional with respect to sequences that agree on relevant positions
let rec accum_max_ext (prices: seq nat) (r1 r2: seq nat) (j: nat) (limit: nat)
  : Lemma (requires (forall (k:nat). k < j /\ k < length r1 /\ k < length r2 ==> index r1 k == index r2 k) /\
                     length r1 >= j /\ length r2 >= j)
          (ensures accum_max prices r1 j limit == accum_max prices r2 j limit)
          (decreases limit)
  = if limit = 0 || j = 0 then ()
    else if limit > j || limit - 1 >= length prices then 
      accum_max_ext prices r1 r2 j (limit - 1)
    else (
      accum_max_ext prices r1 r2 j (limit - 1);
      assert (j - limit < j);
      assert (j - limit < length r1);
      assert (j - limit < length r2);
      assert (index r1 (j - limit) == index r2 (j - limit))
    )

// DP table correctness
let dp_correct (prices: seq nat) (sr: seq nat) (bound: nat) : prop =
  (forall (k: nat). k <= bound /\ k < length sr ==>
    index sr k == optimal_revenue prices k)

// Lemma: when DP table is correct for k < j, accum_max with DP table == optimal_revenue
let accum_max_dp_correct (prices: seq nat) (sr: seq nat) (j: nat)
  : Lemma (requires j > 0 /\ j <= length prices /\ length sr > j /\
                     dp_correct prices sr (j - 1))
          (ensures accum_max prices sr j j == optimal_revenue prices j)
  = let prev = build_opt prices (j - 1) in
    assert (length prev == j);
    let rec aux (k:nat) 
      : Lemma (requires k < j)
              (ensures index sr k == index prev k)
              (decreases k)
      = optimal_revenue_consistent prices k (j - 1)
    in
    let rec apply_aux (k:nat)
      : Lemma (requires k <= j)
              (ensures forall (i:nat). i < k ==> index sr i == index prev i)
              (decreases k)
      = if k = 0 then ()
        else (
          apply_aux (k - 1);
          aux (k - 1)
        )
    in
    apply_aux j;
    accum_max_ext prices sr prev j j
