/*
 * LCS — C implementation with c2pulse verification.
 *
 * Bottom-up dynamic programming approach from CLRS Chapter 15.
 * Uses a 2-loop structure (i=0..m, j=0..n) combining init + DP.
 *
 * Proves:
 *   1. Base case: row 0 of DP table is all zeros
 *   2. Non-negativity: all table entries >= 0
 *   3. Upper bound: result <= 1000
 *   4. Functional correctness:
 *      result == lcs_length(x, y, m, n)
 *
 * NO admits. All correctness via lcs_table_correct tracking invariant.
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
  _ensures(return >= 0)
  _ensures(return <= 1000)
  _ensures(_forall(size_t k,
    (bool) _inline_pulse(SizeT.v var_k >= (SizeT.v $(m) + 1) * (SizeT.v $(n) + 1))
    || tbl[k] >= 0))
  _ensures((_slprop) _inline_pulse(
    with_pure (
      id #int (Int32.v return_1) =
        lcs_length
          (to_int_seq (array_value_of $(x)))
          (to_int_seq (array_value_of $(y)))
          (SizeT.v $(m)) (SizeT.v $(n)))))
{
  size_t n1 = n + 1;

  for (size_t i = 0; i <= m; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*tbl) && _live(*x) && _live(*y))
    _invariant(i <= m + 1)
    _invariant(m >= 1 && m <= 1000)
    _invariant(n >= 1 && n <= 1000)
    _invariant(x._length == m && y._length == n)
    _invariant((bool) _inline_pulse(
      SizeT.fits ((SizeT.v $(m) + 1) * (SizeT.v $(n) + 1))))
    _invariant((bool) _inline_pulse(
      reveal (length_of $(tbl)) = (SizeT.v $(m) + 1) * (SizeT.v $(n) + 1)))
    _invariant(_forall(size_t k,
      (bool) _inline_pulse(SizeT.v var_k >= SizeT.v $(i) * (SizeT.v $(n) + 1))
      || tbl[k] >= 0))
    _invariant(_forall(size_t k,
      (bool) _inline_pulse(SizeT.v var_k >= SizeT.v $(i) * (SizeT.v $(n) + 1))
      || tbl[k] <= 1000))
    _invariant((_slprop) _inline_pulse(
      with_pure (
        lcs_table_correct
          (to_int_seq (array_value_of $(x)))
          (to_int_seq (array_value_of $(y)))
          (to_int_seq (array_value_of $(tbl)))
          (SizeT.v $(m)) (SizeT.v $(n))
          (SizeT.v $(i)) 0)))
  {
    for (size_t j = 0; j <= n; j = j + 1)
      _invariant(_live(j) && _live(i))
      _invariant(_live(*tbl) && _live(*x) && _live(*y))
      _invariant(i <= m)
      _invariant(j <= n + 1)
      _invariant(m >= 1 && m <= 1000)
      _invariant(n >= 1 && n <= 1000)
      _invariant(x._length == m && y._length == n)
      _invariant((bool) _inline_pulse(
        SizeT.fits ((SizeT.v $(m) + 1) * (SizeT.v $(n) + 1))))
      _invariant((bool) _inline_pulse(
        reveal (length_of $(tbl)) = (SizeT.v $(m) + 1) * (SizeT.v $(n) + 1)))
      _invariant(_forall(size_t k,
        (bool) _inline_pulse(
          SizeT.v var_k >= SizeT.v $(i) * (SizeT.v $(n) + 1) + SizeT.v $(j))
        || tbl[k] >= 0))
      _invariant(_forall(size_t k,
        (bool) _inline_pulse(
          SizeT.v var_k >= SizeT.v $(i) * (SizeT.v $(n) + 1) + SizeT.v $(j))
        || tbl[k] <= 1000))
      _invariant((_slprop) _inline_pulse(
        with_pure (
          lcs_table_correct
            (to_int_seq (array_value_of $(x)))
            (to_int_seq (array_value_of $(y)))
            (to_int_seq (array_value_of $(tbl)))
            (SizeT.v $(m)) (SizeT.v $(n))
            (SizeT.v $(i)) (SizeT.v $(j)))))
    {
      size_t idx = i * n1 + j;

      /* Unconditional bridge for diagonal bound */
      _ghost_stmt(
        lcs_table_diag_bound_opt
          (to_int_seq (array_value_of $(x)))
          (to_int_seq (array_value_of $(y)))
          (to_int_seq (array_value_of $(tbl)))
          (SizeT.v $(m)) (SizeT.v $(n))
          (SizeT.v $(i)) (SizeT.v $(j)));

      /* Declare all locals BEFORE any branch (c2pulse limitation) */
      int diag_val = 0;
      int up_val = 0;
      int left_val = 0;
      int xi_val = 0;
      int yj_val = 0;
      int value = 0;

      if (i > 0 && j > 0) {
        diag_val = tbl[idx - n1 - 1];
        up_val = tbl[idx - n1];
        left_val = tbl[idx - 1];
        _assert(diag_val >= 0);
        _assert(diag_val <= 999);
        _assert(up_val >= 0);
        _assert(up_val <= 1000);
        _assert(left_val >= 0);
        _assert(left_val <= 1000);
        xi_val = x[i - 1];
        yj_val = y[j - 1];
        if (xi_val == yj_val) {
          value = diag_val + 1;
        } else if (up_val >= left_val) {
          value = up_val;
        } else {
          value = left_val;
        }
      }

      /* Ghost: connect computed value to lcs_length */
      _ghost_stmt(
        lcs_step_correct
          (to_int_seq (array_value_of $(x)))
          (to_int_seq (array_value_of $(y)))
          (to_int_seq (array_value_of $(tbl)))
          (SizeT.v $(m)) (SizeT.v $(n))
          (SizeT.v $(i)) (SizeT.v $(j))
          (Int32.v $(value)));

      /* Ghost: advance invariant from (i,j) to (i,j+1) on updated table */
      _ghost_stmt(
        lcs_table_update_preserves
          (to_int_seq (array_value_of $(x)))
          (to_int_seq (array_value_of $(y)))
          (to_int_seq (array_value_of $(tbl)))
          (SizeT.v $(m)) (SizeT.v $(n))
          (SizeT.v $(i)) (SizeT.v $(j))
          (Int32.v $(value)));

      tbl[idx] = value;
    }

    /* Ghost: transition from (i, n+1) to (i+1, 0) */
    _ghost_stmt(
      lcs_table_next_row
        (to_int_seq (array_value_of $(x)))
        (to_int_seq (array_value_of $(y)))
        (to_int_seq (array_value_of $(tbl)))
        (SizeT.v $(m)) (SizeT.v $(n))
        (SizeT.v $(i)));
  }

  /* Ghost: final table result */
  _ghost_stmt(
    lcs_table_result
      (to_int_seq (array_value_of $(x)))
      (to_int_seq (array_value_of $(y)))
      (to_int_seq (array_value_of $(tbl)))
      (SizeT.v $(m)) (SizeT.v $(n)));

  size_t last_idx = m * n1 + n;
  int result = tbl[last_idx];
  _assert(result >= 0);
  _assert(result <= 1000);

  return result;
}
