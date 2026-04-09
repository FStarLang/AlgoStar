/*
 * Matrix Chain Multiplication — C implementation with c2pulse verification.
 *
 * Bottom-up dynamic programming approach from CLRS Chapter 15.
 *
 * Given n matrices with dimensions dims[0..n] (matrix i has dimensions
 * dims[i] × dims[i+1]), finds the minimum number of scalar multiplications
 * needed to compute their product.
 *
 * Proves:
 *   1. Non-negativity: all table entries >= 0
 *   2. Result >= 0
 *   3. Functional correctness (admitted):
 *      result == mc_result(dims, n)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(open Pulse.Lib.C.Array)
_include_pulse(open CLRS.Ch15.MatrixChain.Spec)
_include_pulse(open CLRS.Ch15.MatrixChain.C.BridgeLemmas)

/* Helper: compute flat 2D index a*n + b with proven bound a*n + b < n*n.
 * Factored into a separate function so Z3 proves the nonlinear arithmetic
 * (a < n ∧ b < n → a*n + b < n*n) in a small, clean context.
 */
size_t compute_index(size_t a, size_t b, size_t n)
  _requires(a < n)
  _requires(b < n)
  _requires(n >= 1)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _ensures(return < n * n)
{
  return a * n + b;
}

int matrix_chain(_array int *dims, size_t n, _array int *m)
  _preserves(dims._length == n + 1)
  _requires(n >= 1 && n <= 1000)
  /* Table has n*n entries and n*n fits in SizeT */
  _requires((bool) _inline_pulse(
    reveal (length_of $(m)) = SizeT.v $(n) * SizeT.v $(n)))
  _ensures((bool) _inline_pulse(
    reveal (length_of $(m)) = SizeT.v $(n) * SizeT.v $(n)))
  _requires((bool) _inline_pulse(
    SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  /* Dimension values bounded for Int32 overflow safety */
  _requires(_forall(size_t w, w > n || (dims[w] >= 0 && dims[w] <= 200)))
  /* Result bounds */
  _ensures(return >= 0)
  /* Non-negativity of all table entries */
  _ensures(_forall(size_t w,
    (bool) _inline_pulse(SizeT.v var_w >= SizeT.v $(n) * SizeT.v $(n))
    || m[w] >= 0))
  /* Functional correctness: result == mc_result(dims, n) */
  _ensures((_slprop) _inline_pulse(
    with_pure (
      id #int (Int32.v return_1) =
        mc_result
          (to_int_seq (array_value_of $(dims)))
          (SizeT.v $(n)))))
{
  size_t nn = n * n;

  /* Initialize table to all zeros */
  for (size_t idx = 0; idx < nn; idx = idx + 1)
    _invariant(_live(idx))
    _invariant(_live(*m) && _live(*dims))
    _invariant(n >= 1 && n <= 1000)
    _invariant(dims._length == n + 1)
    _invariant((bool) _inline_pulse(
      reveal (length_of $(m)) = SizeT.v $(n) * SizeT.v $(n)))
    _invariant((bool) _inline_pulse(
      SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
    _invariant((bool) _inline_pulse(
      SizeT.v $(idx) <= SizeT.v $(n) * SizeT.v $(n)))
    _invariant(_forall(size_t w, w > n || (dims[w] >= 0 && dims[w] <= 200)))
    _invariant(_forall(size_t w,
      (bool) _inline_pulse(SizeT.v var_w >= SizeT.v $(idx))
      || (m[w] >= 0 && m[w] <= 1000000000)))
  {
    m[idx] = 0;
  }

  /* Main DP: chain lengths l = 2..n */
  for (size_t l = 2; l <= n; l = l + 1)
    _invariant(_live(l))
    _invariant(_live(*m) && _live(*dims))
    _invariant(l >= 2 && l <= n + 1)
    _invariant(n >= 1 && n <= 1000)
    _invariant(dims._length == n + 1)
    _invariant((bool) _inline_pulse(
      reveal (length_of $(m)) = SizeT.v $(n) * SizeT.v $(n)))
    _invariant((bool) _inline_pulse(
      SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
    _invariant(_forall(size_t w, w > n || (dims[w] >= 0 && dims[w] <= 200)))
    _invariant(_forall(size_t w,
      (bool) _inline_pulse(SizeT.v var_w >= SizeT.v $(n) * SizeT.v $(n))
      || (m[w] >= 0 && m[w] <= 1000000000)))
  {
    /* For each starting position i */
    for (size_t i = 0; i + l <= n; i = i + 1)
      _invariant(_live(i) && _live(l))
      _invariant(_live(*m) && _live(*dims))
      _invariant(l >= 2 && l <= n)
      _invariant(n >= 1 && n <= 1000)
      _invariant(dims._length == n + 1)
      _invariant((bool) _inline_pulse(
        reveal (length_of $(m)) = SizeT.v $(n) * SizeT.v $(n)))
      _invariant((bool) _inline_pulse(
        SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
      _invariant(_forall(size_t w, w > n || (dims[w] >= 0 && dims[w] <= 200)))
      _invariant(_forall(size_t w,
        (bool) _inline_pulse(SizeT.v var_w >= SizeT.v $(n) * SizeT.v $(n))
        || (m[w] >= 0 && m[w] <= 1000000000)))
      _invariant((bool) _inline_pulse(
        SizeT.v $(i) + SizeT.v $(l) <= SizeT.v $(n) + 1))
    {
      size_t j = i + l - 1;
      int min_cost = 1000000000;

      /* Try all split points k from i to j-1 */
      for (size_t k = i; k < j; k = k + 1)
        _invariant(_live(k) && _live(min_cost) && _live(i) && _live(l))
        _invariant(_live(*m) && _live(*dims))
        _invariant(l >= 2 && l <= n)
        _invariant(n >= 1 && n <= 1000)
        _invariant(dims._length == n + 1)
        _invariant((bool) _inline_pulse(
          reveal (length_of $(m)) = SizeT.v $(n) * SizeT.v $(n)))
        _invariant((bool) _inline_pulse(
          SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
        _invariant(_forall(size_t w, w > n || (dims[w] >= 0 && dims[w] <= 200)))
        _invariant(_forall(size_t w,
          (bool) _inline_pulse(SizeT.v var_w >= SizeT.v $(n) * SizeT.v $(n))
          || (m[w] >= 0 && m[w] <= 1000000000)))
        _invariant((bool) _inline_pulse(
          SizeT.v $(i) + SizeT.v $(l) <= SizeT.v $(n)))
        _invariant((bool) _inline_pulse(
          SizeT.v $(j) = SizeT.v $(i) + SizeT.v $(l) - 1))
        _invariant((bool) _inline_pulse(
          SizeT.v $(k) >= SizeT.v $(i) && SizeT.v $(k) <= SizeT.v $(j)))
        _invariant(min_cost >= 0 && min_cost <= 1000000000)
      {
        /* Assert linear bounds for compute_index preconditions */
        _assert((bool) _inline_pulse(SizeT.v $(i) < SizeT.v $(n)));
        _assert((bool) _inline_pulse(SizeT.v $(k) < SizeT.v $(n)));
        _assert((bool) _inline_pulse(SizeT.v $(k) + 1 < SizeT.v $(n)));
        _assert((bool) _inline_pulse(SizeT.v $(j) < SizeT.v $(n)));

        /* Compute 2D indices via helper (proves bounds in simpler context) */
        size_t idx_ik = compute_index(i, k, n);
        size_t idx_k1j = compute_index(k + 1, j, n);

        /* Read table values into locals */
        int cost_ik = m[idx_ik];
        int cost_k1j = m[idx_k1j];

        /* Read dimension values */
        int dim_i = dims[i];
        int dim_k1 = dims[k + 1];
        int dim_j1 = dims[j + 1];

        /* Assert bounds for overflow proof */
        _assert(cost_ik >= 0);
        _assert(cost_ik <= 1000000000);
        _assert(cost_k1j >= 0);
        _assert(cost_k1j <= 1000000000);
        _assert(dim_i >= 0);
        _assert(dim_i <= 200);
        _assert(dim_k1 >= 0);
        _assert(dim_k1 <= 200);
        _assert(dim_j1 >= 0);
        _assert(dim_j1 <= 200);

        int mult_cost = dim_i * dim_k1 * dim_j1;
        int sum_cost = cost_ik + cost_k1j;
        int q = sum_cost + mult_cost;

        if (q < min_cost) {
          min_cost = q;
        }
      }

      /* Store m[i][j] = min_cost */
      _assert((bool) _inline_pulse(SizeT.v $(i) < SizeT.v $(n)));
      _assert((bool) _inline_pulse(SizeT.v $(j) < SizeT.v $(n)));
      size_t idx_ij = compute_index(i, j, n);
      m[idx_ij] = min_cost;
    }
  }

  /* Return m[0][n-1] */
  size_t result_idx = n - 1;
  int result = m[result_idx];
  _assert(result >= 0);

  /* admit: functional correctness (to be proven via bridge lemmas) */
  _ghost_stmt(admit());

  return result;
}
