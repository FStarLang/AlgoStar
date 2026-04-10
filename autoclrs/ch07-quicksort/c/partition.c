/*
 * CLRS Chapter 7: Lomuto Partition — C implementation with c2pulse verification.
 *
 * Proves:
 *   1. The returned pivot index is within [lo, hi).
 *   2. All elements in [lo, return) are <= a[return] (the pivot).
 *   3. All elements in (return, hi) are > a[return] (strictly_larger_than).
 *   4. Elements outside [lo, hi) are unchanged (frame preservation).
 *   5. No-fabrication: every output element existed in the input range.
 *
 * Matches the specification in CLRS.Ch07.Partition.Impl.fsti
 * (minus complexity counting and full permutation, which use ghost refs).
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Lomuto partition scheme (CLRS §7.1).
 *
 * Chooses a[hi-1] as the pivot. Scans left-to-right, swapping elements
 * <= pivot into the front partition. Finally swaps the pivot into place.
 */
size_t partition(_array int *a, size_t len, size_t lo, size_t hi)
  _requires(a._length == len && lo < hi && hi <= len)
  _ensures(a._length == len && lo <= return && return < hi)
  _ensures(_forall(size_t k, lo <= k && k < return ==> a[k] <= a[return]))
  _ensures(_forall(size_t k, return < k && k < hi ==> a[return] < a[k]))
  _ensures(_forall(size_t k, k < len && (k < lo || hi <= k) ==> a[k] == _old(a[k])))
  /* No-fabrication: every output element in [lo,hi) existed in the input */
  _ensures(_forall(size_t k, lo <= k && k < hi ==>
      _exists(size_t j, lo <= j && j < hi && a[k] == _old(a[j]))))
{
  int pivot = a[hi - 1];
  size_t i = lo;
  int tmp = 0;

  for (size_t j = lo; j < hi - 1; j = j + 1)
    _invariant(_live(j) && _live(i) && _live(pivot) && _live(tmp))
    _invariant(_live(*a))
    _invariant(a._length == len)
    _invariant(lo <= i && i <= j && j < hi)
    _invariant(a[hi - 1] == pivot)
    _invariant(_forall(size_t k, lo <= k && k < i ==> a[k] <= pivot))
    _invariant(_forall(size_t k, i <= k && k < j ==> a[k] > pivot))
    _invariant(_forall(size_t k, k < len && (k < lo || hi <= k) ==> a[k] == _old(a[k])))
    /* No-fabrication: loop invariant */
    _invariant(_forall(size_t k, lo <= k && k < hi ==>
        _exists(size_t m, lo <= m && m < hi && a[k] == _old(a[m]))))
  {
    if (a[j] <= pivot) {
      tmp = a[i];
      a[i] = a[j];
      a[j] = tmp;
      i = i + 1;
    }
  }

  /* Place pivot at position i */
  tmp = a[i];
  a[i] = a[hi - 1];
  a[hi - 1] = tmp;

  return i;
}
