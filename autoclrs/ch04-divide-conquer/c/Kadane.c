/*
 * Kadane's Maximum Subarray — C implementation with c2pulse verification.
 *
 * Proves:
 *   1. The result equals max_subarray_spec (the mathematically optimal
 *      maximum contiguous subarray sum), via bridge lemmas connecting
 *      c2pulse's array model to CLRS.Ch04.MaxSubarray.Spec.
 *   2. The result is >= every element in the array.
 *   3. current_sum tracks max(a[i], current_sum + a[i]) — the maximum
 *      suffix sum ending at position i.
 *   4. best_sum tracks the global maximum over all suffix sums.
 *
 * Equivalent to CLRS.Ch04.MaxSubarray.Kadane.fsti (minus complexity bound).
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(
  open CLRS.Ch04.Kadane.C.BridgeLemmas
  open CLRS.Ch04.MaxSubarray.Spec
)

/*
 * Maximum subarray sum using Kadane's algorithm.
 *
 * At each step:
 *   current_sum = max(a[i], current_sum + a[i])
 *   best_sum    = max(best_sum, current_sum)
 *
 * After the loop, best_sum is the maximum sum over all non-empty
 * contiguous subarrays.
 */
int kadane(_array int *a, size_t len)
  _requires(a._length == len && len > 0)
  /* a[0] bound needed directly for initialization */
  _requires(a[0] >= -1000000 && a[0] <= 1000000)
  /* Bound all elements to prevent overflow in partial sums */
  _requires(_forall(size_t i, i < len ==> a[i] >= -1000000 && a[i] <= 1000000))
  _requires((_specint) len <= 2000)
  _preserves_value(a._length)
  /* result >= every single element */
  _ensures(_forall(size_t i, i < len ==> return >= a[i]))
  /* result == max_subarray_spec (functional correctness) */
  _ensures((bool) _inline_pulse(Int32.v $(return) >= max_subarray_spec_c (array_value_of $(a)) /\ Int32.v $(return) <= max_subarray_spec_c (array_value_of $(a))))
{
  int best_sum = a[0];
  int current_sum = a[0];

  for (size_t i = 1; i < len; i = i + 1)
    _invariant(_live(i) && _live(best_sum) && _live(current_sum))
    _invariant(_live(*a))
    _invariant(a._length == len)
    _invariant(i >= 1 && i <= len)
    _invariant((_specint) len <= 2000)
    /* Element bounds preserved */
    _invariant(_forall(size_t k, k < len ==> a[k] >= -1000000 && a[k] <= 1000000))
    /* best_sum >= every element seen so far */
    _invariant(_forall(size_t k, k < i ==> best_sum >= a[k]))
    /* best_sum >= current_sum */
    _invariant(best_sum >= current_sum)
    /* current_sum >= a[i-1] */
    _invariant(current_sum >= a[i - 1])
    /* Overflow bounds: depend on i */
    _invariant(current_sum >= -1000000)
    _invariant((_specint) current_sum <= (_specint) i * 1000000)
    _invariant(best_sum >= -1000000)
    _invariant((_specint) best_sum <= (_specint) i * 1000000)
    /* Functional correctness: kadane_spec_c partial computation */
    _invariant((bool) _inline_pulse(
      kadane_spec_c (array_value_of $(a)) (SizeT.v $(i))
        (Int32.v $(current_sum)) (Int32.v $(best_sum))
        = max_subarray_spec_c (array_value_of $(a))))
  {
    int sum_with_current = current_sum + a[i];
    if (a[i] > sum_with_current) {
      current_sum = a[i];
    } else {
      current_sum = sum_with_current;
    }

    if (current_sum > best_sum) {
      best_sum = current_sum;
    }
  }

  return best_sum;
}
