/*
 * CLRS Chapter 9: Partial Selection Sort — C with c2pulse verification.
 *
 * Implements:
 *   1. find_min_index_from — find index of minimum in a[start..len)
 *   2. pss_select          — k-th order statistic via partial selection sort
 *
 * Proves (matching CLRS.Ch09.PartialSelectionSort.Impl.fsti):
 *   - find_min_index_from: returned index is in range and holds the minimum
 *   - pss_select: sorted_prefix, prefix <= suffix boundary, result == a[k-1],
 *     no-fabrication (every output element existed in the input)
 *
 * The no-fabrication property (forward surjection) connects to full
 * Seq.Properties.permutation via bridge lemmas.
 *
 * Complexity tracking omitted (no ghost counters in c2pulse).
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Find the index of the minimum element in a[start..len).
 * Array is not modified.
 *
 * Forwards caller's sorted_prefix and boundary properties,
 * and proves array-unchanged so the caller can re-derive
 * no-fabrication after the call.
 */
size_t find_min_index_from(_array int *a, size_t start, size_t len)
  _requires(a._length == len && start < len)
  _requires(_forall(size_t j, j > 0 && j < start ==> a[j - 1] <= a[j]))
  _requires(start > 0 && start < len ==>
    _forall(size_t j, start <= j && j < len ==> a[start - 1] <= a[j]))
  _preserves(a._length == len)
  _ensures(start <= return && return < len)
  _ensures(_forall(size_t j, start <= j && j < len ==> a[return] <= a[j]))
  _ensures(_forall(size_t j, j > 0 && j < start ==> a[j - 1] <= a[j]))
  _ensures(start > 0 && start < len ==>
    _forall(size_t j, start <= j && j < len ==> a[start - 1] <= a[j]))
  _ensures(_forall(size_t idx, idx < len ==> a[idx] == _old(a[idx])))
{
  size_t min_idx = start;

  for (size_t i = start + 1; i < len; i = i + 1)
    _invariant(_live(i) && _live(min_idx) && _live(*a))
    _invariant(a._length == len)
    _invariant(i > start && i <= len)
    _invariant(start <= min_idx && min_idx < i)
    _invariant(_forall(size_t j, start <= j && j < i ==> a[min_idx] <= a[j]))
    _invariant(_forall(size_t j, j > 0 && j < start ==> a[j - 1] <= a[j]))
    _invariant(start > 0 && start < len ==>
      _forall(size_t j, start <= j && j < len ==> a[start - 1] <= a[j]))
    _invariant(_forall(size_t idx, idx < len ==> a[idx] == _old(a[idx])))
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
 *   - sorted_prefix: a[j-1] <= a[j] for 0 < j < k
 *   - prefix <= suffix boundary: a[k-1] <= a[j] for k <= j < n
 *   - no-fabrication: every output element existed in the input
 */
int pss_select(_array int *a, size_t n, size_t k)
  _requires(a._length == n && n > 0 && k >= 1 && k <= n)
  _preserves(a._length == n)
  _ensures(return == a[k - 1])
  _ensures(k < n ==> _forall(size_t j, k <= j && j < n ==> return <= a[j]))
  _ensures(_forall(size_t j, j > 0 && j < k ==> a[j - 1] <= a[j]))
  _ensures(_forall(size_t p, p < n ==> _exists(size_t m, m < n && a[p] == _old(a[m]))))
{
  for (size_t round = 0; round < k; round = round + 1)
    _invariant(_live(round) && _live(*a))
    _invariant(a._length == n)
    _invariant(round <= k)
    _invariant(_forall(size_t j, j > 0 && j < round ==> a[j - 1] <= a[j]))
    _invariant(round > 0 && round < n ==>
      _forall(size_t j, round <= j && j < n ==> a[round - 1] <= a[j]))
    _invariant(_forall(size_t p, p < n ==> _exists(size_t m, m < n && a[p] == _old(a[m]))))
  {
    size_t min_idx = find_min_index_from(a, round, n);
    int val_round = a[round];
    int val_min = a[min_idx];
    a[round] = val_min;
    a[min_idx] = val_round;
  }

  return a[k - 1];
}
