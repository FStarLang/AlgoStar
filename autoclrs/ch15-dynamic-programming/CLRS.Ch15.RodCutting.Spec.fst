(*
   Rod Cutting — Shared pure specification (CLRS Chapter 15)

   This module defines the DP recurrence for rod cutting and the key lemmas
   that establish its correctness. These definitions are shared by:
   - CLRS.Ch15.RodCutting (basic Pulse implementation)
   - CLRS.Ch15.RodCutting.Spec (optimality and substructure proofs)
   - CLRS.Ch15.RodCutting.Extended (extended Pulse implementation with cuts array)
*)

module CLRS.Ch15.RodCutting.Spec

open FStar.List.Tot
open FStar.Seq

// ========== Problem Specification ==========

//SNIPPET_START: cutting_defs
/// A cutting is valid if all pieces are positive and sum to n
let rec valid_cutting (n: nat) (cuts: list nat) : prop =
  match cuts with
  | [] -> n = 0
  | piece :: rest -> piece > 0 /\ piece <= n /\ valid_cutting (n - piece) rest

/// Revenue from a cutting: sum of prices for each piece
/// prices[i] = price for a piece of length (i+1)
let rec cutting_revenue (prices: seq nat) (cuts: list nat) : nat =
  match cuts with
  | [] -> 0
  | piece :: rest ->
    if piece > 0 && piece - 1 < length prices
    then index prices (piece - 1) + cutting_revenue prices rest
    else 0 + cutting_revenue prices rest  // out-of-bounds piece has price 0
//SNIPPET_END: cutting_defs

/// The sum of pieces in a cutting
let rec cutting_sum (cuts: list nat) : Tot nat (decreases cuts) =
  match cuts with
  | [] -> 0
  | piece :: rest -> piece + cutting_sum rest

/// Maximum over a range of positive naturals
let rec max_over_range (f: (i:nat{i > 0} -> nat)) (n: nat{n > 0}) : Tot nat (decreases n) =
  if n = 1 then f 1
  else
    let prev = max_over_range f (n - 1) in
    let curr = f n in
    if curr >= prev then curr else prev

/// Revenue from a first cut at position i using a precomputed table
let revenue_with_first_cut (prices: seq nat) (prev_table: seq nat) (j: nat) (i: nat{i > 0 /\ i <= j}) : nat =
  if i - 1 < length prices && j - i < length prev_table
  then index prices (i - 1) + index prev_table (j - i)
  else 0

// ========== DP Recurrence ==========

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

// Explicit one-step unfolding of accum_max for use at fuel 0
let accum_max_step (prices: seq nat) (r: seq nat) (j: nat) (i: nat)
  : Lemma (requires i >= 1 /\ j >= 1 /\ i <= j /\ i - 1 < length prices /\ j - i < length r)
          (ensures accum_max prices r j i ==
                   (let prev = accum_max prices r j (i - 1) in
                    let candidate = index prices (i - 1) + index r (j - i) in
                    if candidate >= prev then candidate else prev))
  = ()

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
