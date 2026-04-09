/*
 * CLRS Chapter 9.1: MINIMUM / MAXIMUM — C implementation with c2pulse verification.
 *
 * Proves:
 *   1. The returned value exists in the array (existential witness)
 *   2. The returned value is the minimum/maximum (universal bound)
 *
 * Equivalent to the functional-correctness properties in
 * CLRS.Ch09.MinMax.Impl.fsti (complexity tracking omitted as c2pulse
 * does not have ghost counters).
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Find the minimum element of a non-empty array.
 *
 * Tracks the index of the current minimum so the existential
 * witness is always available to the SMT solver.
 */
int find_minimum(_array int *a, size_t len)
  _requires(a._length == len && len > 0)
  _preserves(a._length == len)
  _ensures(_exists(size_t k, k < len && a[k] == return))
  _ensures(_forall(size_t k, k < len ==> return <= a[k]))
{
  size_t min_idx = 0;

  for (size_t i = 1; i < len; i = i + 1)
    _invariant(_live(i) && _live(min_idx) && _live(*a))
    _invariant(a._length == len)
    _invariant(i >= 1 && i <= len)
    _invariant(min_idx < i)
    _invariant(_forall(size_t k, k < i ==> a[min_idx] <= a[k]))
  {
    if (a[i] < a[min_idx]) {
      min_idx = i;
    }
  }

  return a[min_idx];
}

/*
 * Find the maximum element of a non-empty array.
 */
int find_maximum(_array int *a, size_t len)
  _requires(a._length == len && len > 0)
  _preserves(a._length == len)
  _ensures(_exists(size_t k, k < len && a[k] == return))
  _ensures(_forall(size_t k, k < len ==> return >= a[k]))
{
  size_t max_idx = 0;

  for (size_t i = 1; i < len; i = i + 1)
    _invariant(_live(i) && _live(max_idx) && _live(*a))
    _invariant(a._length == len)
    _invariant(i >= 1 && i <= len)
    _invariant(max_idx < i)
    _invariant(_forall(size_t k, k < i ==> a[max_idx] >= a[k]))
  {
    if (a[i] > a[max_idx]) {
      max_idx = i;
    }
  }

  return a[max_idx];
}
