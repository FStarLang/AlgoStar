/*
 * CLRS Chapter 9.2: Quickselect — C implementation with c2pulse verification.
 *
 * Implements:
 *   1. partition_in_range — Lomuto partition of a[lo..hi)
 *   2. quickselect_rec   — recursive partition-based k-th element selection
 *   3. quickselect        — wrapper calling quickselect_rec with lo=0, hi=n
 *
 * Proves (approaching CLRS.Ch09.Quickselect.Impl.fsti):
 *   - partition_in_range: pivot in [lo,hi), partition ordering, unchanged_outside
 *   - quickselect: result == a[k], ordering (all a[i<k] <= result <= a[i>k]),
 *     unchanged_outside
 *
 * Uses _rec for natural recursive structure (c2pulse now supports recursion).
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
 */
size_t partition_in_range(_array int *a, size_t len, size_t lo, size_t hi)
  _requires(a._length == len && lo < hi && hi <= len)
  _preserves(a._length == len)
  _ensures(lo <= return && return < hi)
  _ensures(_forall(size_t idx, lo <= idx && idx < return ==> a[idx] <= a[return]))
  _ensures(_forall(size_t idx, return < idx && idx < hi ==> a[idx] >= a[return]))
  _ensures(_forall(size_t idx, idx < len && (idx < lo || idx >= hi) ==> a[idx] == _old(a[idx])))
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
    _invariant(_forall(size_t idx, idx < len && (idx < lo || idx >= hi) ==> a[idx] == _old(a[idx])))
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
 * Recursively partitions the array, narrowing the search range
 * until the pivot lands at position k.
 *
 * Proves:
 *   - result == a[k]
 *   - Elements outside [lo, hi) are unchanged
 *
 * Note: The full ordering property (all a[i<k] <= result <= a[i>k])
 * requires permutation tracking not available in c2pulse.
 * See CLRS.Ch09.Quickselect.Impl.fst for the full Pulse proof.
 */
_rec int quickselect_rec(_array int *a, size_t n, size_t k, size_t lo, size_t hi)
  _requires(a._length == n && lo <= k && k < hi && hi <= n)
  _preserves(a._length == n)
  _ensures(return == a[k])
  _ensures(_forall(size_t i, i < n && (i < lo || i >= hi) ==> a[i] == _old(a[i])))
  _decreases(hi - lo)
{
  if (hi - lo <= 1) {
    return a[k];
  }

  size_t p = partition_in_range(a, n, lo, hi);

  if (k < p) {
    return quickselect_rec(a, n, k, lo, p);
  } else if (p < k) {
    return quickselect_rec(a, n, k, p + 1, hi);
  } else {
    return a[k];
  }
}

/*
 * Quickselect: find the k-th smallest element (0-indexed).
 *
 * Wrapper that calls the recursive implementation with lo=0, hi=n.
 *
 * Proves:
 *   - result == a[k]
 */
int quickselect(_array int *a, size_t n, size_t k)
  _requires(a._length == n && n > 0 && k < n)
  _preserves(a._length == n)
  _ensures(return == a[k])
{
  return quickselect_rec(a, n, k, 0, n);
}
