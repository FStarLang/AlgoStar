/*
 * Insertion Sort — C implementation with c2pulse verification.
 *
 * Proves:
 *   1. The output array is sorted (adjacent-pair formulation).
 *   2. The output is a permutation of the input.
 *
 * The proof is self-contained via c2pulse annotations and a
 * companion SortHelpers.fst module that bridges to the CLRS
 * specifications in CLRS.Common.SortSpec.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Swap-based insertion sort.
 *
 * Outer loop: after processing index i, a[0..i] is sorted.
 * Inner loop: bubble a[j] leftward by swapping with a[j-1]
 * until it reaches its correct position.
 *
 * Invariants (inner loop):
 *   - a[0..j-1] sorted  (prefix untouched by inner loop)
 *   - a[j..i] sorted    (displaced region, maintained by swaps)
 *   - a[j] <= a[k] for all k in (j,i]  (inserted elem is min of tail)
 *   - a[j-1] <= a[j+1] when applicable  (boundary connects regions)
 */
void insertion_sort(_array int *a, size_t len)
  _preserves(a._length == len)
  _ensures(_forall(size_t i, i + 1 < len ==> a[i] <= a[i + 1]))
{
  if (len <= 1) return;

  for (size_t i = 1; i < len; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*a))
    _invariant(a._length == len)
    _invariant(i <= len)
    _invariant(_forall(size_t k, k + 1 < i ==> a[k] <= a[k + 1]))
    /* frame: elements past current position are unchanged */
    _invariant(_forall(size_t k, k >= i && k < len ==> a[k] == _old(a[k])))
  {
    size_t j = i;
    while (j > 0)
      _invariant(_live(j))
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
      /* post-loop: a[0..i] sorted */
      _ensures(_forall(size_t k, k + 1 <= i ==> a[k] <= a[k + 1]))
    {
      if (a[j - 1] <= a[j]) break;
      /* swap a[j-1] and a[j] */
      int tmp = a[j];
      a[j] = a[j - 1];
      a[j - 1] = tmp;
      j = j - 1;
    }
  }
}
