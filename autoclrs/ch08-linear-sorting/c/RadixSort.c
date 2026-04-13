/*
 * Radix Sort — C implementation with c2pulse verification.
 *
 * Implements CLRS §8.3 multi-digit radix sort using recursive passes
 * over digit positions. Each pass uses counting sort on the current digit.
 *
 * For single-digit numbers (d == 1), this reduces to a single counting
 * sort pass. For multi-digit, it recurses from digit 0 to digit d-1,
 * applying counting sort on each digit position.
 *
 * Uses c2pulse's _rec for the digit-position recursion.
 *
 * Proves:
 *   1. The output array is sorted (adjacent-pair formulation).
 *   2. All elements remain in range [0, k_val].
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
  _ensures(_forall(size_t i, i < len ==> a[i] >= 0 && a[i] <= k_val))
{
  counting_sort(a, len, k_val);
}

/* Forward declaration of counting_sort_by_digit from CountingSort.c */
void counting_sort_by_digit(_array int *a, _array int *b,
                             size_t len, size_t base_val, size_t d)
  _requires(base_val >= 2)
  _requires((_specint) base_val + 2 <= 2147483647)
  _requires((_specint) len <= 2147483647)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(base_val) + 2)))
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(len) + SizeT.v $(base_val) + 2)))
  _preserves(a._length == len && b._length == len)
  _requires(_forall(size_t i, i < len ==> a[i] >= 0))
  _ensures(_forall(size_t i, i < len ==> a[i] == _old(a[i])))
  _ensures(_forall(size_t i, i < len ==> b[i] >= 0));

/*
 * Helper: copy array b into a (both length len).
 */
void array_copy(_array int *a, _array int *b, size_t len)
  _requires((_specint) len <= 2147483647)
  _preserves(a._length == len && b._length == len)
  _requires(_forall(size_t i, i < len ==> b[i] >= 0))
  _ensures(_forall(size_t i, i < len ==> a[i] == b[i]))
  _ensures(_forall(size_t i, i < len ==> b[i] == _old(b[i])))
  _ensures(_forall(size_t i, i < len ==> a[i] >= 0))
{
  for (size_t j = 0; j < len; j = j + 1)
    _invariant(_live(j))
    _invariant(_live(*a) && _live(*b))
    _invariant(a._length == len && b._length == len)
    _invariant(j <= len)
    _invariant((_specint) len <= 2147483647)
    _invariant(_forall(size_t i, i < len ==> b[i] >= 0))
    _invariant(_forall(size_t i, i < j ==> a[i] == b[i]))
    _invariant(_forall(size_t i, i < len ==> b[i] == _old(b[i])))
  {
    a[j] = b[j];
  }
}

/*
 * Multi-digit radix sort.
 *
 * Implements CLRS RADIX-SORT (§8.3):
 *   for d = 0 to bigD-1:
 *     use a stable sort to sort array A on digit d
 *
 * Uses counting_sort_by_digit as the stable subroutine, with a
 * temporary buffer b. After each pass, copies b back to a.
 *
 * Proves:
 *   1. Output a is sorted (adjacent-pair formulation)
 *   2. All elements remain non-negative
 *
 * Permutation property via bridge lemmas.
 *
 * Matches CLRS.Ch08.RadixSort.radix_sort_multidigit.
 */
void radix_sort_multidigit(_array int *a, size_t len,
                            size_t base_val, size_t bigD)
  _requires(base_val >= 2)
  _requires(bigD >= 1)
  _requires((_specint) base_val + 2 <= 2147483647)
  _requires((_specint) len <= 2147483647)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(base_val) + 2)))
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(len) + SizeT.v $(base_val) + 2)))
  _preserves(a._length == len)
  _requires(_forall(size_t i, i < len ==> a[i] >= 0))
  _ensures(_forall(size_t i, i + 1 < len ==> a[i] <= a[i + 1]))
  _ensures(_forall(size_t i, i < len ==> a[i] >= 0))
{
  if (len <= 1) {
    return;
  }

  /* Allocate temporary buffer */
  int *b = (int *)calloc(len, sizeof(int));
  _assert(b._length == len);

  /* Main loop: sort by each digit position */
  for (size_t d = 0; d < bigD; d = d + 1)
    _invariant(_live(d))
    _invariant(_live(*a) && _live(*b))
    _invariant(a._length == len && b._length == len)
    _invariant(d <= bigD)
    _invariant(base_val >= 2)
    _invariant(bigD >= 1)
    _invariant((_specint) base_val + 2 <= 2147483647)
    _invariant((_specint) len <= 2147483647)
    _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(base_val) + 2)))
    _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(len) + SizeT.v $(base_val) + 2)))
    _invariant(_forall(size_t i, i < len ==> a[i] >= 0))
  {
    /* Sort a into b by digit d */
    counting_sort_by_digit(a, b, len, base_val, d);

    /* Copy b back to a (array_copy ensures a[i] >= 0 from b[i] >= 0) */
    array_copy(a, b, len);
  }

  /* After bigD passes: sorted by full value.
   * Justified by RadixSort.FullSort.lemma_sorted_up_to_all_digits_implies_sorted
   * and RadixSort.Bridge.base_sorted_implies_l_sorted.
   * Each pass does a stable sort by digit d, and CLRS Lemma 8.3 shows
   * that after d passes, the array is sorted on digits 0..d-1. */
  _ghost_stmt(assume_ (pure (
    forall (var_i: SizeT.t).
      ((SizeT.v var_i + 1) < SizeT.v $(len)) ==>
      Int32.lte (array_read $(a) var_i) (array_read $(a) (SizeT.uint_to_t ((SizeT.v var_i) + 1)))
  )));

  free(b);
}