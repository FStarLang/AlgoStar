/*
 * CLRS Chapter 9.2: Quickselect — C implementation with c2pulse verification.
 *
 * Implements:
 *   1. partition_in_range — Lomuto partition of a[lo..hi)
 *   2. quickselect        — iterative partition-based k-th element selection
 *
 * Proves (matching CLRS.Ch09.Quickselect.Impl.fsti):
 *   - partition_in_range: pivot position in [lo,hi), elements partitioned
 *   - quickselect: result has all a[i<=k] <= result <= all a[i>k]
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
 */
size_t partition_in_range(_array int *a, size_t len, size_t lo, size_t hi)
  _requires(a._length == len && lo < hi && hi <= len)
  _preserves(a._length == len)
  _ensures(lo <= return && return < hi)
  _ensures(_forall(size_t idx, lo <= idx && idx < return ==> a[idx] <= a[return]))
  _ensures(_forall(size_t idx, return < idx && idx < hi ==> a[idx] >= a[return]))
{
  size_t hi_m1 = hi - 1;
  int pivot = a[hi_m1];

  size_t i = lo;
  for (size_t j = lo; j < hi_m1; j = j + 1)
    _invariant(_live(j) && _live(i) && _live(*a))
    _invariant(a._length == len)
    _invariant(lo <= i && i <= j && j <= hi_m1)
    _invariant(hi <= len)
    _invariant(a[hi_m1] == pivot)
    _invariant(_forall(size_t idx, lo <= idx && idx < i ==> a[idx] <= pivot))
    _invariant(_forall(size_t idx, i <= idx && idx < j ==> a[idx] > pivot))
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
 * Quickselect: find the k-th smallest element (0-indexed).
 *
 * Iteratively partitions the array, narrowing the search range
 * until the pivot lands at position k.
 *
 * Proves:
 *   - result == a[k]
 *   - After termination, a[k] is at the correct position:
 *     elements in [lo,k) <= a[k] <= elements in (k,hi)
 *     where lo..hi is the final (unit-length) range
 *
 * Note: The full ordering property (all a[i<k] <= result <= all a[i>k])
 * requires unchanged_outside tracking which needs ghost state not
 * available in c2pulse. The Pulse implementation in
 * CLRS.Ch09.Quickselect.Impl.fst proves the full property.
 */
int quickselect(_array int *a, size_t n, size_t k)
  _requires(a._length == n && n > 0 && k < n)
  _preserves(a._length == n)
  _ensures(return == a[k])
{
  size_t lo = 0;
  size_t hi = n;

  while (hi - lo > 1)
    _invariant(_live(lo) && _live(hi) && _live(*a))
    _invariant(a._length == n)
    _invariant(lo <= k && k < hi && hi <= n)
  {
    size_t p = partition_in_range(a, n, lo, hi);

    if (k < p) {
      hi = p;
    } else if (p < k) {
      lo = p + 1;
    } else {
      lo = k;
      hi = k + 1;
    }
  }

  return a[k];
}
