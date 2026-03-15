module CLRS.Ch15.MatrixChain.Complexity

open FStar.Mul

val mc_inner_sum (n: nat) (l: nat) : Tot nat

val mc_iterations (n: nat) : nat

val term_bound_lemma (n l: nat)
  : Lemma (requires 2 <= l /\ l <= n)
          (ensures (n - l + 1) * (l - 1) <= n * n)

val mc_inner_sum_term_count (n l: nat)
  : Lemma (requires l <= n + 1)
          (ensures mc_inner_sum n l <= (n - l + 1) * (n * n))

/// Main theorem: mc_iterations n ≤ n³
val mc_iterations_bound (n: nat)
  : Lemma (ensures mc_iterations n <= n * n * n)

val mc_is_cubic (n: nat)
  : Lemma (ensures mc_iterations n <= n * n * n)

val mc_iterations_positive (n: nat)
  : Lemma (requires n >= 2)
          (ensures mc_iterations n > 0)

/// mc_inner_sum at start equals mc_iterations
val mc_inner_sum_at_start (n: nat)
  : Lemma (ensures mc_inner_sum n 2 == mc_iterations n)

/// mc_inner_sum unfolds by one step
val mc_inner_sum_step (n l: nat)
  : Lemma (requires l >= 2 /\ l <= n)
          (ensures mc_inner_sum n l == (n - l + 1) * (l - 1) + mc_inner_sum n (l + 1))

/// mc_inner_sum is 0 past the end
val mc_inner_sum_zero (n l: nat)
  : Lemma (requires l > n)
          (ensures mc_inner_sum n l == 0)
