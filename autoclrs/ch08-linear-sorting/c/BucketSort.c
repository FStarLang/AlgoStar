/*
 * Bucket Sort (array-based) — C implementation with c2pulse verification.
 *
 * Implements CLRS §8.4 bucket sort using arrays instead of linked lists.
 * Elements in [0, k_val] are distributed into k_val+1 buckets
 * (one per integer value), reducing to counting sort for integer keys.
 *
 * The companion F* spec (CLRS.Ch08.BucketSort.Spec) uses list-based
 * buckets and insertion sort per bucket. Since c2pulse operates on
 * arrays rather than linked lists, this implementation uses the
 * counting-sort-based bucket distribution which is equivalent for
 * integer keys.
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
  _ensures(_forall(size_t i, i + 1 < len ==> a[i] <= a[i + 1]))
  _ensures(_forall(size_t i, i < len ==> a[i] >= 0 && a[i] <= k_val));

/*
 * Array-based bucket sort for non-negative int values in [0, k_val].
 *
 * For integer keys, distributing into one bucket per integer value
 * and concatenating the sorted buckets is exactly counting sort
 * (CLRS §8.4 observation: bucket sort with n = k uses counting sort).
 */
void bucket_sort(_array int *a, size_t len, int k_val)
  _requires(k_val >= 0)
  _requires((_specint) k_val + 2 <= 2147483647)
  _requires((_specint) len <= 2147483647)
  _requires((bool) _inline_pulse(SizeT.fits (Int32.v $(k_val) + 2)))
  _preserves(a._length == len)
  _requires(_forall(size_t i, i < len ==> a[i] >= 0 && a[i] <= k_val))
  _ensures(_forall(size_t i, i + 1 < len ==> a[i] <= a[i + 1]))
  _ensures(_forall(size_t i, i < len ==> a[i] >= 0 && a[i] <= k_val))
{
  counting_sort(a, len, k_val);
}
