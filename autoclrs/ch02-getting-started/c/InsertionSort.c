/*
 * Insertion Sort — C implementation with c2pulse verification.
 *
 * Proves:
 *   1. The output array is sorted (adjacent-pair formulation).
 *   2. O(n^2) swap complexity: at most n*(n-1)/2 swaps.
 *
 * The proof is self-contained via c2pulse annotations and a
 * companion SortHelpers.fst module that bridges to the CLRS
 * specifications in CLRS.Common.SortSpec.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Swap-based insertion sort with swap counting.
 *
 * Outer loop: after processing index i, a[0..i] is sorted.
 * Inner loop: bubble a[j] leftward by swapping with a[j-1]
 * until it reaches its correct position.
 *
 * cost tracks swap count.  Invariant: cost + j <= i*(i+1)/2.
 * At loop exit cost <= i*(i+1)/2.  After all iterations
 * cost <= len*(len-1)/2.
 */
void insertion_sort(_array int *a, size_t len)
  _requires((bool) _inline_pulse(SizeT.v $(len) < 65536))
  _preserves(a._length == len)
  _ensures(_forall(size_t i, i + 1 < len ==> a[i] <= a[i + 1]))
{
  if (len <= 1) return;

  int cost = 0;
  for (size_t i = 1; i < len; i = i + 1)
    _invariant(_live(i) && _live(cost))
    _invariant(_live(*a))
    _invariant(a._length == len)
    _invariant(i <= len)
    _invariant(_forall(size_t k, k + 1 < i ==> a[k] <= a[k + 1]))
    /* frame: elements past current position are unchanged */
    _invariant(_forall(size_t k, k >= i && k < len ==> a[k] == _old(a[k])))
    /* complexity: cost <= i*(i-1)/2 */
    _invariant(cost >= 0)
    _invariant((bool) _inline_pulse(Int32.v $(cost) <= op_Multiply (SizeT.v $(i)) (SizeT.v $(i) - 1) / 2))
  {
    size_t j = i;
    while (j > 0)
      _invariant(_live(j) && _live(cost))
      _invariant(_live(*a))
      _invariant(a._length == len)
      _invariant(j <= i && i < len)
      /* prefix sorted */
      _invariant(_forall(size_t k, k + 1 < j ==> a[k] <= a[k + 1]))
      /* displaced region sorted */
      _invariant(j + 1 <= i ==> _forall(size_t k, j < k && k + 1 <= i ==> a[k] <= a[k + 1]))
      /* inserted element <= everything in displaced region */
      _invariant(j < i ==> _forall(size_t k, j < k && k <= i ==> a[j] <= a[k]))
      /* boundary: prefix end <= displaced start */
      _invariant(j > 0 && j + 1 <= i ==> a[j - 1] <= a[j + 1])
      /* frame: elements past i are unchanged */
      _invariant(_forall(size_t k, k > i && k < len ==> a[k] == _old(a[k])))
      /* complexity: cost + j <= i*(i+1)/2 */
      _invariant(cost >= 0)
      _invariant((bool) _inline_pulse(Int32.v $(cost) + SizeT.v $(j) <= op_Multiply (SizeT.v $(i)) (SizeT.v $(i) + 1) / 2))
      /* post-loop: a[0..i] sorted and cost bounded */
      _ensures(_forall(size_t k, k + 1 <= i ==> a[k] <= a[k + 1]))
    {
      if (a[j - 1] <= a[j]) break;
      /* swap a[j-1] and a[j] */
      int tmp = a[j];
      a[j] = a[j - 1];
      a[j - 1] = tmp;
      j = j - 1;
      cost = cost + 1;
    }
  }
  /* Final complexity bound: cost <= len*(len-1)/2 */
  _assert(cost >= 0);
  _assert((bool) _inline_pulse(Int32.v $(cost) <= op_Multiply (SizeT.v $(len)) (SizeT.v $(len) - 1) / 2));
}
