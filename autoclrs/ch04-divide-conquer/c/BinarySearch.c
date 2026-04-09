/*
 * Binary Search — Recursive C implementation with c2pulse verification.
 *
 * Proves:
 *   1. If key is found, returns an index where a[result] == key.
 *   2. If key is not found, returns len.
 *   3. Correctness relies on the precondition that the array is sorted.
 *
 * Uses c2pulse's _rec support for natural recursive formulation.
 * Equivalent to CLRS.Ch04.BinarySearch.Impl.fsti (minus complexity bound).
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Recursive binary search helper on a sorted array a[lo..hi).
 *
 * Precondition: a is sorted in non-decreasing order.
 *               key is not in a[0..lo) or a[hi..len).
 * Returns: index of key if found, or len if not found.
 */
_rec size_t binary_search_rec(_array int *a, size_t len, int key,
                              size_t lo, size_t hi)
  _preserves(a._length == len)
  _requires(lo <= hi && hi <= len)
  _requires(_forall(size_t i, _forall(size_t j,
    i < j && j < len ==> a[i] <= a[j])))
  /* key is not outside [lo, hi) */
  _requires(_forall(size_t k, k < lo ==> a[k] != key))
  _requires(_forall(size_t k, k >= hi && k < len ==> a[k] != key))
  _ensures(return <= len)
  _ensures(return < len ==> a[return] == key)
  _ensures(return == len ==> _forall(size_t i, i < len ==> a[i] != key))
  _decreases(hi - lo)
{
  if (lo >= hi) {
    return len;
  }

  size_t mid = lo + (hi - lo) / 2;

  if (a[mid] == key) {
    return mid;
  } else if (a[mid] < key) {
    _assert(_forall(size_t k, k <= mid && k < len ==> a[k] <= a[mid]));
    return binary_search_rec(a, len, key, mid + 1, hi);
  } else {
    _assert(_forall(size_t k, k >= mid && k < len ==> a[k] >= a[mid]));
    return binary_search_rec(a, len, key, lo, mid);
  }
}

/*
 * Binary search entry point — delegates to the recursive helper.
 */
size_t binary_search(_array int *a, size_t len, int key)
  _preserves(a._length == len)
  _requires(_forall(size_t i, _forall(size_t j,
    i < j && j < len ==> a[i] <= a[j])))
  _ensures(return <= len)
  _ensures(return < len ==> a[return] == key)
  _ensures(return == len ==> _forall(size_t i, i < len ==> a[i] != key))
{
  return binary_search_rec(a, len, key, 0, len);
}
