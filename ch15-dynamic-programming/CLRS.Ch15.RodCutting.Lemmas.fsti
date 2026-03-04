module CLRS.Ch15.RodCutting.Lemmas

open FStar.List.Tot
open FStar.Seq
open CLRS.Ch15.RodCutting.Spec

/// Every cutting of length n > 0 must start with some piece
val cutting_nonempty (n: nat{n > 0}) (cuts: list nat)
  : Lemma (requires valid_cutting n cuts)
          (ensures Cons? cuts)

/// Valid cuttings satisfy bound on piece sizes
val cutting_pieces_bounded (n: nat) (cuts: list nat)
  : Lemma (requires valid_cutting n cuts)
          (ensures forall piece. FStar.List.Tot.mem piece cuts ==> piece > 0 /\ piece <= n)

val valid_cutting_sum (n: nat) (cuts: list nat)
  : Lemma (requires valid_cutting n cuts)
          (ensures cutting_sum cuts = n)

/// Pure function that computes the DP table (alias for build_opt)
let pure_bottom_up_cut (prices: seq nat) (n: nat) : (s:seq nat{length s == n + 1 /\ index s 0 == 0}) =
  build_opt prices n

/// Correctness: every entry in the table is the optimal revenue
val pure_bottom_up_correct (prices: seq nat) (n: nat) (j: nat)
  : Lemma (requires j <= n)
          (ensures index (pure_bottom_up_cut prices n) j == optimal_revenue prices j)

/// Main theorem: The DP table computed by build_opt is correct
val dp_table_correct (prices: seq nat) (n: nat) (j: nat)
  : Lemma (requires j <= n)
          (ensures index (build_opt prices n) j == optimal_revenue prices j)

/// Corollary: The bottom-up computation correctly solves all subproblems
val dp_solves_all_subproblems (prices: seq nat) (n: nat)
  : Lemma (ensures (let table = build_opt prices n in
                    length table == n + 1 /\
                    (forall (j: nat). j <= n ==> index table j == optimal_revenue prices j)))

/// Theorem: Optimal substructure (CLRS Eq. 15.2)
val optimal_substructure (prices: seq nat) (n: nat{n > 0 /\ n <= length prices})
  : Lemma (ensures (let f : (i:nat{i > 0} -> nat) = fun (i:nat{i > 0}) ->
                      if i <= n && i - 1 < length prices
                      then index prices (i - 1) + optimal_revenue prices (n - i)
                      else 0 in
                    optimal_revenue prices n == max_over_range f n))

/// max_over_range f n >= f k for any k in [1, n]
val max_over_range_geq (f: (i:nat{i > 0} -> nat)) (n: nat{n > 0}) (k: nat{k > 0 /\ k <= n})
  : Lemma (ensures max_over_range f n >= f k)

/// Computes the index where max_over_range achieves its value
val argmax_over_range (f: (i:nat{i > 0} -> nat)) (n: nat{n > 0})
  : Tot (k:nat{k > 0 /\ k <= n})

/// argmax_over_range achieves the maximum
val argmax_correct (f: (i:nat{i > 0} -> nat)) (n: nat{n > 0})
  : Lemma (ensures max_over_range f n == f (argmax_over_range f n))

/// Upper bound: cutting_revenue <= optimal_revenue for any valid cutting
val cutting_revenue_le_optimal (prices: seq nat) (n: nat) (cuts: list nat)
  : Lemma (requires valid_cutting n cuts /\ n <= length prices)
          (ensures cutting_revenue prices cuts <= optimal_revenue prices n)

/// Achievability: construct an optimal cutting witnessing optimal_revenue
val construct_optimal_cutting (prices: seq nat) (n: nat)
  : Pure (list nat)
    (requires n <= length prices)
    (ensures fun cuts -> valid_cutting n cuts /\ cutting_revenue prices cuts == optimal_revenue prices n)

/// Corollary: optimal_revenue is achievable (existential statement)
val optimal_revenue_achievable (prices: seq nat) (n: nat)
  : Lemma (requires n <= length prices)
          (ensures exists cuts. valid_cutting n cuts /\ cutting_revenue prices cuts == optimal_revenue prices n)
