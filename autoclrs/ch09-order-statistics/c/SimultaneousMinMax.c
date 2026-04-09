/*
 * CLRS Chapter 9.1: Simultaneous Min and Max — C with c2pulse verification.
 *
 * Two implementations:
 *   1. find_minmax      — simple linear scan, 2 comparisons per element
 *   2. find_minmax_pairs — pair processing, ~3n/2 comparisons
 *
 * Both prove:
 *   - The min value exists in the array and is <= all elements
 *   - The max value exists in the array and is >= all elements
 *
 * Equivalent to CLRS.Ch09.SimultaneousMinMax.Impl.fsti (functional correctness;
 * complexity tracking omitted).
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Simple linear scan: check each element against both min and max.
 * Returns min/max via out parameters.
 */
void find_minmax(_array int *a, size_t len, _out int *min_val, _out int *max_val)
  _requires(a._length == len && len >= 1)
  _preserves(a._length == len)
  _ensures(_exists(size_t k, k < len && a[k] == *min_val))
  _ensures(_forall(size_t k, k < len ==> *min_val <= a[k]))
  _ensures(_exists(size_t k, k < len && a[k] == *max_val))
  _ensures(_forall(size_t k, k < len ==> *max_val >= a[k]))
{
  size_t lo_idx = 0;
  size_t hi_idx = 0;

  for (size_t i = 1; i < len; i = i + 1)
    _invariant(_live(i) && _live(lo_idx) && _live(hi_idx) && _live(*a))
    _invariant(a._length == len)
    _invariant(i >= 1 && i <= len)
    _invariant(lo_idx < i && hi_idx < i)
    _invariant(_forall(size_t k, k < i ==> a[lo_idx] <= a[k]))
    _invariant(_forall(size_t k, k < i ==> a[hi_idx] >= a[k]))
  {
    if (a[i] < a[lo_idx]) lo_idx = i;
    if (a[i] > a[hi_idx]) hi_idx = i;
  }

  *min_val = a[lo_idx];
  *max_val = a[hi_idx];
}

/*
 * CLRS pair processing: compare pairs of elements first, then update
 * min/max with the smaller/larger of the pair.
 * Uses ~3n/2 comparisons vs 2(n-1) for the simple scan.
 */
void find_minmax_pairs(_array int *a, size_t len, _out int *min_val, _out int *max_val)
  _requires(a._length == len && len >= 1)
  _preserves(a._length == len)
  _ensures(_exists(size_t k, k < len && a[k] == *min_val))
  _ensures(_forall(size_t k, k < len ==> *min_val <= a[k]))
  _ensures(_exists(size_t k, k < len && a[k] == *max_val))
  _ensures(_forall(size_t k, k < len ==> *max_val >= a[k]))
{
  size_t lo_idx = 0;
  size_t hi_idx = 0;
  size_t i = 1;

  /* Initialize with first pair if len >= 2 */
  if (len >= 2) {
    if (a[0] <= a[1]) {
      hi_idx = 1;
    } else {
      lo_idx = 1;
    }
    i = 2;
  }

  /* Process elements in pairs */
  size_t len_m1 = len - 1;
  while (i < len_m1)
    _invariant(_live(i) && _live(lo_idx) && _live(hi_idx) && _live(*a))
    _invariant(a._length == len)
    _invariant(i >= 1 && i <= len)
    _invariant(lo_idx < i && hi_idx < i)
    _invariant((bool) _inline_pulse(SizeT.v $(len_m1) + 1 = SizeT.v $(len)))
    _invariant(_forall(size_t k, k < i ==> a[lo_idx] <= a[k]))
    _invariant(_forall(size_t k, k < i ==> a[hi_idx] >= a[k]))
  {
    if (a[i] <= a[i + 1]) {
      if (a[i] < a[lo_idx]) lo_idx = i;
      if (a[i + 1] > a[hi_idx]) hi_idx = i + 1;
    } else {
      if (a[i + 1] < a[lo_idx]) lo_idx = i + 1;
      if (a[i] > a[hi_idx]) hi_idx = i;
    }
    i = i + 2;
  }

  /* Handle odd trailing element */
  if (i < len) {
    if (a[i] < a[lo_idx]) lo_idx = i;
    if (a[i] > a[hi_idx]) hi_idx = i;
  }

  *min_val = a[lo_idx];
  *max_val = a[hi_idx];
}
