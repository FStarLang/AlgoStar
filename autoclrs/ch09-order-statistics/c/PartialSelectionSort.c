/*
 * CLRS Chapter 9: Partial Selection Sort — C with c2pulse verification.
 *
 * Implements:
 *   1. find_min_index_from — find index of minimum in a[start..len)
 *   2. select             — k-th order statistic via partial selection sort
 *
 * Proves (matching CLRS.Ch09.PartialSelectionSort.Impl.fsti):
 *   - find_min_index_from: returned index is in range and holds the minimum
 *   - select: output has sorted prefix, prefix <= suffix, result == a[k-1]
 *
 * Complexity tracking omitted (no ghost counters in c2pulse).
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Find the index of the minimum element in a[start..len).
 * Array is not modified.
 */
size_t find_min_index_from(_array int *a, size_t start, size_t len)
  _requires(a._length == len && start < len)
  _preserves(a._length == len)
  _ensures(start <= return && return < len)
  _ensures(_forall(size_t j, start <= j && j < len ==> a[return] <= a[j]))
{
  size_t min_idx = start;

  for (size_t i = start + 1; i < len; i = i + 1)
    _invariant(_live(i) && _live(min_idx) && _live(*a))
    _invariant(a._length == len)
    _invariant(i > start && i <= len)
    _invariant(start <= min_idx && min_idx < i)
    _invariant(_forall(size_t j, start <= j && j < i ==> a[min_idx] <= a[j]))
  {
    if (a[i] < a[min_idx]) {
      min_idx = i;
    }
  }

  return min_idx;
}

/*
 * Select the k-th smallest element (1-indexed: k in [1..n]).
 *
 * Runs k rounds of selection sort: each round finds the minimum in
 * a[round..n) and swaps it into position a[round].
 *
 * Proves:
 *   - return == a[k-1]
 *   - a[k-1] <= all elements in a[k..n) (prefix_leq_suffix boundary)
 */
int select(_array int *a, size_t n, size_t k)
  _requires(a._length == n && n > 0 && k >= 1 && k <= n)
  _preserves(a._length == n)
  _ensures(return == a[k - 1])
  _ensures(k < n ==> _forall(size_t j, k <= j && j < n ==> return <= a[j]))
{
  for (size_t round = 0; round < k; round = round + 1)
    _invariant(_live(round) && _live(*a))
    _invariant(a._length == n)
    _invariant(round <= k)
    _invariant(round > 0 && round < n ==>
      _forall(size_t j, round <= j && j < n ==> a[round - 1] <= a[j]))
  {
    size_t min_idx = find_min_index_from(a, round, n);
    int val_round = a[round];
    int val_min = a[min_idx];
    if (min_idx != round) {
      a[round] = val_min;
      a[min_idx] = val_round;
    }
  }

  return a[k - 1];
}
