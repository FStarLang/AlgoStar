/*
 * CLRS Chapter 9.2: Quickselect — C implementation with c2pulse verification.
 *
 * Implements:
 *   1. partition_in_range — Lomuto partition of a[lo..hi)
 *   2. quickselect_rec   — recursive partition-based k-th element selection
 *   3. quickselect        — wrapper calling quickselect_rec with lo=0, hi=n
 *
 * Proves (approaching CLRS.Ch09.Quickselect.Impl.fsti):
 *   - partition_in_range: pivot in [lo,hi), partition ordering,
 *     unchanged_outside, bounds, no-fabrication
 *   - quickselect_rec: result == a[k], full ordering (all a[i<k] <= result
 *     <= a[i>k] within [lo,hi)), unchanged_outside, bounds
 *   - quickselect: result == a[k], no-fabrication, full ordering
 *
 * Uses bounds (lb, rb) threaded through the recursion, following
 * the same approach as ch07 quicksort.
 *
 * Complexity tracking omitted (no ghost counters in c2pulse).
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Lomuto partition of a[lo..hi).
 * Pivot = a[hi-1]. Elements <= pivot go to the left partition.
 *
 * Returns pivot_pos in [lo, hi) such that:
 *   - a[j] <= a[pivot_pos] for all j in [lo, pivot_pos)
 *   - a[j] >= a[pivot_pos] for all j in (pivot_pos, hi)
 *   - elements outside [lo, hi) are unchanged
 *   - all elements in [lo, hi) stay in [lb, rb]
 *   - no-fabrication: each output element in [lo,hi) existed in the input
 */
size_t partition_in_range(_array int *a, size_t len, size_t lo, size_t hi, int lb, int rb)
  _requires(a._length == len && lo < hi && hi <= len)
  _requires(lb <= rb)
  _requires(_forall(size_t idx, lo <= idx && idx < hi ==> lb <= a[idx] && a[idx] <= rb))
  _preserves(a._length == len)
  _ensures(lo <= return && return < hi)
  _ensures(_forall(size_t idx, lo <= idx && idx < return ==> a[idx] <= a[return]))
  _ensures(_forall(size_t idx, return < idx && idx < hi ==> a[idx] >= a[return]))
  _ensures(lb <= a[return] && a[return] <= rb)
  _ensures(_forall(size_t idx, lo <= idx && idx < hi ==> lb <= a[idx] && a[idx] <= rb))
  _ensures(_forall(size_t idx, idx < len && (idx < lo || idx >= hi) ==> a[idx] == _old(a[idx])))
  _ensures(_forall(size_t idx, lo <= idx && idx < hi ==>
      _exists(size_t m, lo <= m && m < hi && a[idx] == _old(a[m]))))
{
  size_t hi_m1 = hi - 1;
  int pivot = a[hi_m1];

  size_t i = lo;
  for (size_t j = lo; j < hi_m1; j = j + 1)
    _invariant(_live(j) && _live(i) && _live(pivot) && _live(*a))
    _invariant(a._length == len)
    _invariant(lo <= i && i <= j && j <= hi_m1)
    _invariant(hi <= len)
    _invariant(lb <= rb)
    _invariant(a[hi_m1] == pivot)
    _invariant(lb <= pivot && pivot <= rb)
    _invariant(_forall(size_t idx, lo <= idx && idx < i ==> a[idx] <= pivot))
    _invariant(_forall(size_t idx, i <= idx && idx < j ==> a[idx] > pivot))
    _invariant(_forall(size_t idx, lo <= idx && idx < hi ==> lb <= a[idx] && a[idx] <= rb))
    _invariant(_forall(size_t idx, idx < len && (idx < lo || idx >= hi) ==> a[idx] == _old(a[idx])))
    _invariant(_forall(size_t idx, lo <= idx && idx < hi ==>
        _exists(size_t m, lo <= m && m < hi && a[idx] == _old(a[m]))))
  {
    int val_i = a[i];
    int val_j = a[j];
    if (a[j] <= pivot) {
      if (i != j) {
        a[i] = val_j;
        a[j] = val_i;
      }
      i = i + 1;
    }
  }

  /* Place pivot in its final position by swapping a[i] and a[hi_m1] */
  int val_i = a[i];
  if (i != hi_m1) {
    a[i] = pivot;
    a[hi_m1] = val_i;
  }

  return i;
}

/*
 * Recursive quickselect: find the k-th smallest element (0-indexed)
 * within the range [lo, hi).
 *
 * Tracks bounds (lb, rb) through the recursion to prove full ordering.
 *
 * Proves:
 *   - result == a[k]
 *   - Full ordering within [lo, hi): a[i<k] <= result, a[i>k] >= result
 *   - Bounds: all elements in [lo, hi) stay in [lb, rb]
 *   - Elements outside [lo, hi) are unchanged
 *   - No-fabrication: every output element in [lo,hi) existed in the input
 */
_rec int quickselect_rec(_array int *a, size_t n, size_t k, size_t lo, size_t hi, int lb, int rb)
  _requires(a._length == n && lo <= k && k < hi && hi <= n)
  _requires(lb <= rb)
  _requires(_forall(size_t idx, lo <= idx && idx < hi ==> lb <= a[idx] && a[idx] <= rb))
  _preserves(a._length == n)
  _ensures(return == a[k])
  _ensures(lb <= return && return <= rb)
  _ensures(_forall(size_t idx, lo <= idx && idx < k ==> a[idx] <= return))
  _ensures(_forall(size_t idx, k < idx && idx < hi ==> a[idx] >= return))
  _ensures(_forall(size_t idx, lo <= idx && idx < hi ==> lb <= a[idx] && a[idx] <= rb))
  _ensures(_forall(size_t idx, idx < n && (idx < lo || idx >= hi) ==> a[idx] == _old(a[idx])))
  _ensures(_forall(size_t idx, lo <= idx && idx < hi ==>
      _exists(size_t m, lo <= m && m < hi && a[idx] == _old(a[m]))))
  _decreases(hi - lo)
{
  if (hi - lo <= 1) {
    return a[k];
  }

  size_t p = partition_in_range(a, n, lo, hi, lb, rb);
  int piv = a[p];

  if (k < p) {
    return quickselect_rec(a, n, k, lo, p, lb, piv);
  } else if (p < k) {
    return quickselect_rec(a, n, k, p + 1, hi, piv, rb);
  } else {
    return a[k];
  }
}

/*
 * Quickselect: find the k-th smallest element (0-indexed).
 *
 * Wrapper that computes bounds (min, max of the array) then calls
 * the recursive implementation.
 *
 * Proves:
 *   - result == a[k]
 *   - Full ordering: a[i<k] <= result <= a[i>k]
 *   - No-fabrication: every output element existed in the input
 */
int quickselect(_array int *a, size_t n, size_t k)
  _requires(a._length == n && n > 0 && k < n)
  _preserves(a._length == n)
  _ensures(return == a[k])
  _ensures(_forall(size_t idx, idx < k ==> a[idx] <= return))
  _ensures(_forall(size_t idx, k < idx && idx < n ==> a[idx] >= return))
  _ensures(_forall(size_t p, p < n ==> _exists(size_t m, m < n && a[p] == _old(a[m]))))
{
  /* Compute min/max bounds */
  int lb = a[0];
  int rb = a[0];
  for (size_t i = 1; i < n; i = i + 1)
    _invariant(_live(i) && _live(lb) && _live(rb) && _live(*a))
    _invariant(a._length == n)
    _invariant(1 <= i && i <= n)
    _invariant(lb <= rb)
    _invariant(_forall(size_t idx, idx < i ==> lb <= a[idx] && a[idx] <= rb))
    _invariant(_forall(size_t idx, idx < n ==> a[idx] == _old(a[idx])))
  {
    if (a[i] < lb) lb = a[i];
    if (a[i] > rb) rb = a[i];
  }

  return quickselect_rec(a, n, k, 0, n, lb, rb);
}
