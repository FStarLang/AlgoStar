module NLArith

open FStar.Mul

/// Nonlinear arithmetic helpers for SizeT-based flat matrix indexing.
/// Wraps FStar.Math.Lemmas to provide convenient lemmas.

/// k*n + n <= n*n when k < n, and (k+1)*n == k*n + n
let base_bound (k n: nat)
  : Lemma (requires k < n)
          (ensures k * n + n <= n * n /\ (k + 1) * n == k * n + n)
  = FStar.Math.Lemmas.lemma_mult_le_right n (k + 1) n;
    FStar.Math.Lemmas.distributivity_add_left k 1 n

/// a*n + b < n*n when a < n /\ b < n (flat index within matrix)
let index_bound (a b n: nat)
  : Lemma (requires a < n /\ b < n)
          (ensures a * n + b < n * n)
  = FStar.Math.Lemmas.lemma_mult_le_right n a (n - 1);
    FStar.Math.Lemmas.distributivity_sub_left n 1 n

/// (a+1)*n == a*n + n (incrementing row counter)
let succ_mul (a n: nat)
  : Lemma (ensures (a + 1) * n == a * n + n)
  = FStar.Math.Lemmas.distributivity_add_left a 1 n
