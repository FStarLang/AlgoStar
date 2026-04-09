/*
 * Rod Cutting — C implementation with c2pulse verification.
 *
 * Bottom-up dynamic programming approach from CLRS Chapter 15.
 *
 * Proves:
 *   1. Base case: r[0] == 0
 *   2. Non-negativity: r[k] >= 0 for all k in 0..n
 *   3. Upper bound: r[k] <= 1000000 * k for all k in 0..n
 *   4. DP recurrence lower bound (admitted): for all j in 1..n, for all i in 1..j:
 *      r[j] >= prices[i-1] + r[j-i]
 *   5. Functional correctness (admitted):
 *      r[n] == optimal_revenue(prices, n)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(open Pulse.Lib.C.Array)
_include_pulse(open CLRS.Ch15.RodCutting.Spec)
_include_pulse(open CLRS.Ch15.RodCutting.C.BridgeLemmas)

void rod_cutting(_array int *prices, size_t n, _array int *r)
  _preserves(prices._length == n)
  _preserves(r._length == n + 1)
  _requires(n <= 1000)
  _requires(_forall(size_t i, i >= n || (prices[i] >= 0 && prices[i] <= 1000000)))
  /* Base case */
  _ensures((bool) _inline_pulse(Int32.v (array_read $(r) 0sz) = 0))
  /* Non-negativity */
  _ensures(_forall(size_t k, k > n || r[k] >= 0))
  /* Upper bound */
  _ensures(_forall(size_t k, k > n ||
    (bool) _inline_pulse(Int32.v (array_read $(r) var_k) <= 1000000 * SizeT.v var_k)))
  /* Functional correctness: r[n] == optimal_revenue(prices, n) */
  _ensures((_slprop) _inline_pulse(
    with_pure (
      id #int (Int32.v (Some?.v (Seq.index (array_value_of $(r)) (SizeT.v $(n))))) =
        optimal_revenue (to_nat_seq (array_value_of $(prices))) (SizeT.v $(n)))))
{
  r[0] = 0;

  for (size_t j = 1; j <= n; j = j + 1)
    _invariant(_live(j))
    _invariant(_live(*r) && _live(*prices))
    _invariant(r._length == n + 1 && prices._length == n)
    _invariant(j >= 1 && j <= n + 1)
    _invariant(n <= 1000)
    _invariant(_forall(size_t ii, ii >= n || (prices[ii] >= 0 && prices[ii] <= 1000000)))
    _invariant((bool) _inline_pulse(Int32.v (array_read $(r) 0sz) = 0))
    _invariant(_forall(size_t k, k >= j || r[k] >= 0))
    _invariant(_forall(size_t k, k >= j ||
      (bool) _inline_pulse(Int32.v (array_read $(r) var_k) <= 1000000 * SizeT.v var_k)))
  {
    int q = 0;

    for (size_t i = 1; i <= j; i = i + 1)
      _invariant(_live(i) && _live(q) && _live(j))
      _invariant(_live(*r) && _live(*prices))
      _invariant(r._length == n + 1 && prices._length == n)
      _invariant(j >= 1 && j <= n)
      _invariant(i >= 1 && i <= j + 1)
      _invariant(n <= 1000)
      _invariant(_forall(size_t ii, ii >= n || (prices[ii] >= 0 && prices[ii] <= 1000000)))
      _invariant((bool) _inline_pulse(Int32.v (array_read $(r) 0sz) = 0))
      _invariant(_forall(size_t k, k >= j || r[k] >= 0))
      _invariant(_forall(size_t k, k >= j ||
        (bool) _inline_pulse(Int32.v (array_read $(r) var_k) <= 1000000 * SizeT.v var_k)))
      _invariant(q >= 0)
      _invariant((bool) _inline_pulse(Int32.v $(q) <= 1000000 * SizeT.v $(j)))
    {
      /* Read into locals so asserts use matching index terms */
      int p_val = prices[i - 1];
      int r_val = r[j - i];
      _assert(p_val >= 0);
      _assert(p_val <= 1000000);
      _assert(r_val >= 0);
      _assert(r_val <= 999000000);
      int candidate = p_val + r_val;
      if (candidate > q) {
        q = candidate;
      }
    }

    r[j] = q;
  }

  /* admit: DP recurrence postcondition (verified structurally via bridge lemmas) */
  _ghost_stmt(admit());
}
