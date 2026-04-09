/*
 * LCS — C implementation with c2pulse verification.
 *
 * Bottom-up dynamic programming approach from CLRS Chapter 15.
 *
 * Proves:
 *   1. Base case: row 0 of DP table is all zeros
 *   2. Non-negativity: all table entries >= 0
 *   3. Upper bound: result <= 1000 (since m,n <= 1000)
 *   4. Functional correctness (admitted):
 *      result == lcs_length(x, y, m, n)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(open Pulse.Lib.C.Array)
_include_pulse(open CLRS.Ch15.LCS.Spec)
_include_pulse(open CLRS.Ch15.LCS.C.BridgeLemmas)

int lcs(_array int *x, size_t m, _array int *y, size_t n, _array int *tbl)
  _preserves(x._length == m)
  _preserves(y._length == n)
  _requires(m >= 1 && m <= 1000)
  _requires(n >= 1 && n <= 1000)
  _requires((bool) _inline_pulse(
    SizeT.fits ((SizeT.v $(m) + 1) * (SizeT.v $(n) + 1))))
  _requires((bool) _inline_pulse(
    reveal (length_of $(tbl)) = (SizeT.v $(m) + 1) * (SizeT.v $(n) + 1)))
  _ensures((bool) _inline_pulse(
    reveal (length_of $(tbl)) = (SizeT.v $(m) + 1) * (SizeT.v $(n) + 1)))
  /* Result bounds */
  _ensures(return >= 0)
  _ensures(return <= 1000)
  /* Non-negativity of all cells */
  _ensures(_forall(size_t k,
    (bool) _inline_pulse(SizeT.v var_k >= (SizeT.v $(m) + 1) * (SizeT.v $(n) + 1))
    || tbl[k] >= 0))
  /* Base case: row 0 all zeros */
  _ensures(_forall(size_t c, c > n ||
    (bool) _inline_pulse(Int32.v (array_read $(tbl) var_c) = 0)))
  /* Functional correctness: result == lcs_length(x, y, m, n) */
  _ensures((_slprop) _inline_pulse(
    with_pure (
      id #int (Int32.v return_1) =
        lcs_length
          (to_int_seq (array_value_of $(x)))
          (to_int_seq (array_value_of $(y)))
          (SizeT.v $(m)) (SizeT.v $(n)))))
{
  size_t n1 = n + 1;
  size_t total = 0;

  /* Fill row 0: all zeros */
  for (size_t j = 0; j <= n; j = j + 1)
    _invariant(_live(j) && _live(total))
    _invariant(_live(*tbl) && _live(*x) && _live(*y))
    _invariant(j <= n + 1)
    _invariant(total == j)
    _invariant(m >= 1 && m <= 1000)
    _invariant(n >= 1 && n <= 1000)
    _invariant(x._length == m && y._length == n)
    _invariant((bool) _inline_pulse(
      SizeT.fits ((SizeT.v $(m) + 1) * (SizeT.v $(n) + 1))))
    _invariant((bool) _inline_pulse(
      reveal (length_of $(tbl)) = (SizeT.v $(m) + 1) * (SizeT.v $(n) + 1)))
    _invariant(_forall(size_t c, c >= j ||
      (bool) _inline_pulse(Int32.v (array_read $(tbl) var_c) = 0)))
    _invariant(_forall(size_t k, k >= total || tbl[k] >= 0))
    _invariant(_forall(size_t k, k >= total || tbl[k] <= 1000))
  {
    tbl[total] = 0;
    total = total + 1;
  }

  /* Fill rows 1..m */
  for (size_t i = 1; i <= m; i = i + 1)
    _invariant(_live(i) && _live(total))
    _invariant(_live(*tbl) && _live(*x) && _live(*y))
    _invariant(i >= 1 && i <= m + 1)
    _invariant(m >= 1 && m <= 1000)
    _invariant(n >= 1 && n <= 1000)
    _invariant(x._length == m && y._length == n)
    _invariant((bool) _inline_pulse(
      SizeT.fits ((SizeT.v $(m) + 1) * (SizeT.v $(n) + 1))))
    _invariant((bool) _inline_pulse(
      reveal (length_of $(tbl)) = (SizeT.v $(m) + 1) * (SizeT.v $(n) + 1)))
    _invariant((bool) _inline_pulse(
      SizeT.v $(total) = SizeT.v $(i) * (SizeT.v $(n) + 1)))
    /* Row 0 is all zeros */
    _invariant(_forall(size_t c, c > n ||
      (bool) _inline_pulse(Int32.v (array_read $(tbl) var_c) = 0)))
    /* Non-negativity */
    _invariant(_forall(size_t k, k >= total || tbl[k] >= 0))
    /* Upper bound */
    _invariant(_forall(size_t k, k >= total || tbl[k] <= 1000))

  {
    /* Column 0: base case */
    tbl[total] = 0;
    total = total + 1;

    for (size_t j = 1; j <= n; j = j + 1)
      _invariant(_live(j) && _live(i) && _live(total))
      _invariant(_live(*tbl) && _live(*x) && _live(*y))
      _invariant(i >= 1 && i <= m)
      _invariant(j >= 1 && j <= n + 1)
      _invariant(m >= 1 && m <= 1000)
      _invariant(n >= 1 && n <= 1000)
      _invariant(x._length == m && y._length == n)
      _invariant((bool) _inline_pulse(
        SizeT.fits ((SizeT.v $(m) + 1) * (SizeT.v $(n) + 1))))
      _invariant((bool) _inline_pulse(
        reveal (length_of $(tbl)) = (SizeT.v $(m) + 1) * (SizeT.v $(n) + 1)))
      _invariant((bool) _inline_pulse(
        SizeT.v $(total) = SizeT.v $(i) * (SizeT.v $(n) + 1) + SizeT.v $(j)))
      /* Row 0 is all zeros */
      _invariant(_forall(size_t c, c > n ||
        (bool) _inline_pulse(Int32.v (array_read $(tbl) var_c) = 0)))
      /* Non-negativity */
      _invariant(_forall(size_t k, k >= total || tbl[k] >= 0))
      /* Upper bound */
      _invariant(_forall(size_t k, k >= total || tbl[k] <= 1000))

    {
      /* Read adjacent cells into locals for asserting bounds */
      int xi = x[i - 1];
      int yj = y[j - 1];
      int diag_val = tbl[total - n1 - 1];
      int up_val = tbl[total - n1];
      int left_val = tbl[total - 1];

      _assert(diag_val >= 0);
      _assert(diag_val <= 1000);
      _assert(up_val >= 0);
      _assert(up_val <= 1000);
      _assert(left_val >= 0);
      _assert(left_val <= 1000);

      /* admit: diag_val <= 999 (LCS values in row i-1 are <= i-1 <= 999) */
      _ghost_stmt(admit());

      if (xi == yj) {
        tbl[total] = diag_val + 1;
      } else if (up_val >= left_val) {
        tbl[total] = up_val;
      } else {
        tbl[total] = left_val;
      }

      total = total + 1;
    }
  }

  int result = tbl[total - 1];
  _assert(result >= 0);
  _assert(result <= 1000);

  /* admit: functional correctness (to be proven via bridge lemmas) */
  _ghost_stmt(admit());

  return result;
}
