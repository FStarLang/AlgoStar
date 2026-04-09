/*
 * Binary Search — C implementation with c2pulse verification.
 *
 * Proves:
 *   1. If key is found, returns an index where a[result] == key.
 *   2. If key is not found, returns len.
 *   3. Correctness relies on the precondition that the array is sorted.
 *
 * Equivalent to CLRS.Ch04.BinarySearch.Impl.fsti (minus complexity bound).
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Binary search on a sorted array.
 *
 * Precondition: a is sorted in non-decreasing order (all-pairs formulation).
 * Returns: index of key if found, or len if not found.
 *
 * Invariant: if key exists in a[0..len), its index is in [lo, hi).
 */
size_t binary_search(_array int *a, size_t len, int key)
  _preserves(a._length == len)
  _requires(_forall(size_t i, _forall(size_t j,
    i < j && j < len ==> a[i] <= a[j])))
  _ensures(return <= len)
  _ensures(return < len ==> a[return] == key)
  _ensures(return == len ==> _forall(size_t i, i < len ==> a[i] != key))
{
  if (len == 0) return len;

  size_t lo = 0;
  size_t hi = len;

  while (lo < hi)
    _invariant(_live(lo) && _live(hi))
    _invariant(_live(*a))
    _invariant(a._length == len)
    _invariant(lo <= hi && hi <= len)
    /* sorted property (preserved — array not modified) */
    _invariant(_forall(size_t i, _forall(size_t j,
      i < j && j < len ==> a[i] <= a[j])))
    /* key not in [0, lo) */
    _invariant(_forall(size_t k, k < lo ==> a[k] != key))
    /* key not in [hi, len) */
    _invariant(_forall(size_t k, k >= hi && k < len ==> a[k] != key))
  {
    size_t mid = lo + (hi - lo) / 2;
    if (a[mid] == key) {
      return mid;
    } else if (a[mid] < key) {
      /* From sortedness: all a[k] for k <= mid satisfy a[k] <= a[mid] < key */
      _assert(_forall(size_t k, k <= mid && k < len ==> a[k] <= a[mid]));
      lo = mid + 1;
    } else {
      /* From sortedness: all a[k] for k >= mid satisfy a[k] >= a[mid] > key */
      _assert(_forall(size_t k, k >= mid && k < len ==> a[k] >= a[mid]));
      hi = mid;
    }
  }
  return len;
}
