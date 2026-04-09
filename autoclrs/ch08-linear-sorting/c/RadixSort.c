/*
 * Radix Sort — C implementation with c2pulse verification.
 *
 * Implements CLRS §8.3 single-digit radix sort, which reduces to
 * in-place counting sort. The multi-digit variant (iterating over
 * digit positions with a stable counting sort subroutine) requires
 * additional infrastructure (digit extraction, separate output array,
 * backward placement for stability) and is implemented in the
 * companion F* module CLRS.Ch08.RadixSort.
 *
 * Proves:
 *   1. The output array is sorted (adjacent-pair formulation).
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

/* Forward declaration of counting_sort from CountingSort.c */
void counting_sort(_array int *a, size_t len, int k_val)
  _requires(k_val >= 0)
  _requires((_specint) k_val + 2 <= 2147483647)
  _requires((_specint) len <= 2147483647)
  _requires((bool) _inline_pulse(SizeT.fits (Int32.v $(k_val) + 2)))
  _preserves(a._length == len)
  _requires(_forall(size_t i, i < len ==> a[i] >= 0 && a[i] <= k_val))
  _ensures(_forall(size_t i, i + 1 < len ==> a[i] <= a[i + 1]));

/*
 * Single-digit radix sort: sorts array of non-negative integers
 * bounded by k_val, reducing directly to counting sort.
 *
 * Equivalent to CLRS §8.3 RADIX-SORT with d = 1.
 */
void radix_sort(_array int *a, size_t len, int k_val)
  _requires(k_val >= 0)
  _requires((_specint) k_val + 2 <= 2147483647)
  _requires((_specint) len <= 2147483647)
  _requires((bool) _inline_pulse(SizeT.fits (Int32.v $(k_val) + 2)))
  _preserves(a._length == len)
  _requires(_forall(size_t i, i < len ==> a[i] >= 0 && a[i] <= k_val))
  _ensures(_forall(size_t i, i + 1 < len ==> a[i] <= a[i + 1]))
{
  counting_sort(a, len, k_val);
}
