(*
   Rod Cutting - Pure F* Specification (CLRS Chapter 15)
   
   Formalizes:
   1. Valid cuttings: lists of piece lengths that sum to n
   2. Cutting revenue: sum of prices for each piece
   3. Optimal revenue: maximum over all valid cuttings
   4. Optimal substructure (CLRS Eq. 15.2)
   5. DP table computation and correctness proof
   
   NO admits for DP correctness.
*)

module CLRS.Ch15.RodCutting.Lemmas

open FStar.List.Tot
open FStar.Seq
open CLRS.Ch15.RodCutting.Spec

// ========== Properties of Cuttings ==========

/// Every cutting of length n > 0 must start with some piece
let cutting_nonempty (n: nat{n > 0}) (cuts: list nat)
  : Lemma (requires valid_cutting n cuts)
          (ensures Cons? cuts)
  = ()

/// Valid cuttings satisfy bound on piece sizes
let rec cutting_pieces_bounded (n: nat) (cuts: list nat)
  : Lemma (requires valid_cutting n cuts)
          (ensures forall piece. FStar.List.Tot.mem piece cuts ==> piece > 0 /\ piece <= n)
          (decreases cuts)
  = match cuts with
    | [] -> ()
    | piece :: rest -> cutting_pieces_bounded (n - piece) rest

let rec valid_cutting_sum (n: nat) (cuts: list nat)
  : Lemma (requires valid_cutting n cuts)
          (ensures cutting_sum cuts = n)
          (decreases cuts)
  = match cuts with
    | [] -> ()
    | piece :: rest -> valid_cutting_sum (n - piece) rest

// ========== Pure Bottom-Up Computation ==========

/// Correctness: every entry in the table is the optimal revenue
let pure_bottom_up_correct (prices: seq nat) (n: nat) (j: nat)
  : Lemma (requires j <= n)
          (ensures index (pure_bottom_up_cut prices n) j == optimal_revenue prices j)
  = build_opt_prefix prices n j

// ========== DP Correctness Theorem ==========

/// Main theorem: The DP table computed by build_opt is correct
let dp_table_correct (prices: seq nat) (n: nat) (j: nat)
  : Lemma (requires j <= n)
          (ensures index (build_opt prices n) j == optimal_revenue prices j)
  = build_opt_prefix prices n j

/// Corollary: The bottom-up computation correctly solves all subproblems
let dp_solves_all_subproblems (prices: seq nat) (n: nat)
  : Lemma (ensures (let table = build_opt prices n in
                    length table == n + 1 /\
                    (forall (j: nat). j <= n ==> index table j == optimal_revenue prices j)))
  = let aux (j: nat{j <= n})
      : Lemma (index (build_opt prices n) j == optimal_revenue prices j)
      = dp_table_correct prices n j
    in
    FStar.Classical.forall_intro aux

// ========== Optimal Substructure Theorem (CLRS Eq. 15.2) ==========

//SNIPPET_START: optimal_substructure
/// Theorem: Optimal substructure
/// optimal_revenue prices n == max_{1 <= i <= n} (prices[i-1] + optimal_revenue prices (n-i))
/// This follows from the definition of accum_max which considers all first-cut positions  
let optimal_substructure (prices: seq nat) (n: nat{n > 0 /\ n <= length prices}) 
  : Lemma (ensures (let f : (i:nat{i > 0} -> nat) = fun (i:nat{i > 0}) ->
                      if i <= n && i - 1 < length prices
                      then index prices (i - 1) + optimal_revenue prices (n - i)
                      else 0 in
                    optimal_revenue prices n == max_over_range f n))
//SNIPPET_END: optimal_substructure
  = let f : (i:nat{i > 0} -> nat) = fun (i:nat{i > 0}) ->
      if i <= n && i - 1 < length prices
      then index prices (i - 1) + optimal_revenue prices (n - i)
      else 0 in
    let prev = build_opt prices (n - 1) in
    let rec equiv (limit: nat{limit > 0 /\ limit <= n})
      : Lemma (ensures accum_max prices prev n limit == max_over_range f limit)
              (decreases limit)
      = if limit = 1 then (
          build_opt_prefix prices (n - 1) (n - 1)
        )
        else (
          equiv (limit - 1);
          build_opt_prefix prices (n - 1) (n - limit);
          ()
        )
    in
    equiv n

// ========== Part 11: Bridge — DP Recurrence to Enumerative Definition ==========

/// Helper: max_over_range f n >= f k for any k in [1, n]
let rec max_over_range_geq (f: (i:nat{i > 0} -> nat)) (n: nat{n > 0}) (k: nat{k > 0 /\ k <= n})
  : Lemma (ensures max_over_range f n >= f k)
          (decreases n)
  = if n = 1 then ()
    else if k = n then ()
    else max_over_range_geq f (n - 1) k

/// Helper: argmax — computes the index where max_over_range achieves its value
let rec argmax_over_range (f: (i:nat{i > 0} -> nat)) (n: nat{n > 0})
  : Tot (k:nat{k > 0 /\ k <= n}) (decreases n)
  = if n = 1 then 1
    else if f n >= max_over_range f (n - 1) then n
    else argmax_over_range f (n - 1)

/// Helper: argmax_over_range achieves the maximum
let rec argmax_correct (f: (i:nat{i > 0} -> nat)) (n: nat{n > 0})
  : Lemma (ensures max_over_range f n == f (argmax_over_range f n))
          (decreases n)
  = if n = 1 then ()
    else if f n >= max_over_range f (n - 1) then ()
    else argmax_correct f (n - 1)

/// Theorem 1 (Upper Bound):
///   For every valid cutting of a rod of length n (with n <= |prices|),
///   cutting_revenue prices cuts <= optimal_revenue prices n.
let rec cutting_revenue_le_optimal (prices: seq nat) (n: nat) (cuts: list nat)
  : Lemma (requires valid_cutting n cuts /\ n <= length prices)
          (ensures cutting_revenue prices cuts <= optimal_revenue prices n)
          (decreases cuts)
  = match cuts with
    | [] -> ()
    | piece :: rest ->
      cutting_revenue_le_optimal prices (n - piece) rest;
      optimal_substructure prices n;
      let f : (i:nat{i > 0} -> nat) = fun (i:nat{i > 0}) ->
        if i <= n && i - 1 < length prices
        then index prices (i - 1) + optimal_revenue prices (n - i)
        else 0 in
      max_over_range_geq f n piece;
      assert (f piece == index prices (piece - 1) + optimal_revenue prices (n - piece))

/// Theorem 2 (Achievability): construct an optimal cutting witnessing optimal_revenue.
let rec construct_optimal_cutting (prices: seq nat) (n: nat)
  : Pure (list nat)
    (requires n <= length prices)
    (ensures fun cuts -> valid_cutting n cuts /\ cutting_revenue prices cuts == optimal_revenue prices n)
    (decreases n)
  = if n = 0 then []
    else
      let f : (i:nat{i > 0} -> nat) = fun (i:nat{i > 0}) ->
        if i <= n && i - 1 < length prices
        then index prices (i - 1) + optimal_revenue prices (n - i)
        else 0 in
      optimal_substructure prices n;
      let istar = argmax_over_range f n in
      argmax_correct f n;
      assert (optimal_revenue prices n == f istar);
      assert (f istar == index prices (istar - 1) + optimal_revenue prices (n - istar));
      let rest = construct_optimal_cutting prices (n - istar) in
      istar :: rest

/// Corollary: optimal_revenue is achievable (existential statement).
let optimal_revenue_achievable (prices: seq nat) (n: nat)
  : Lemma (requires n <= length prices)
          (ensures exists cuts. valid_cutting n cuts /\ cutting_revenue prices cuts == optimal_revenue prices n)
  = let _w = construct_optimal_cutting prices n in ()
