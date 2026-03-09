(*
   CLRS Chapter 9: Partial Selection Sort — Complexity Interface

   Comparison count analysis for partial selection sort: O(nk) worst case.
*)
module CLRS.Ch09.PartialSelectionSort.Complexity

open FStar.Mul

/// Exact comparison count: k rounds, each scanning n-1 elements.
val select_comparisons (n k: nat) : nat

/// Upper bound: select_comparisons n k ≤ k * n.
val select_bound (n k: nat)
  : Lemma (requires k <= n)
          (ensures select_comparisons n k <= k * n)

/// Exact closed form: select_comparisons n k == k * (n - 1).
val select_comparisons_exact (n k: nat)
  : Lemma (requires k <= n)
          (ensures select_comparisons n k == k * (n - 1))

/// O(nk) characterization.
val select_complexity_class (n k: nat)
  : Lemma (requires k <= n)
          (ensures select_comparisons n k <= k * n)

/// Tighter model: round i costs (n-1-i) comparisons.
val select_comparisons_tight (n k: nat) : nat

/// Closed form for tight model: 2 * tight(n,k) == k * (2*n - k - 1).
val select_tight_closed_form (n k: nat)
  : Lemma (requires k <= n /\ n > 0)
          (ensures 2 * select_comparisons_tight n k == k * (2 * n - k - 1))

/// Tight model is strictly better when k > 1.
val select_tight_strictly_better (n k: nat)
  : Lemma (requires k > 1 /\ k <= n /\ n > 0)
          (ensures select_comparisons_tight n k < select_comparisons n k)

/// Upper bound for tight model.
val select_tight_bound (n k: nat)
  : Lemma (requires k <= n /\ n > 0)
          (ensures select_comparisons_tight n k <= k * n)
