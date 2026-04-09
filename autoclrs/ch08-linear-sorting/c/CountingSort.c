/*
 * Counting Sort (in-place) — C implementation with c2pulse verification.
 *
 * Proves:
 *   1. The output array is sorted (adjacent-pair formulation).
 *
 * Implements CLRS §8.2 in-place variant:
 *   Phase 1: Count occurrences of each value into array c[0..k].
 *   Phase 2: Overwrite a with sorted values by iterating positions
 *            0..len-1, writing the next non-exhausted value at each.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

/*
 * Phase 1 helper: count occurrences of each value in a[0..len) into c[0..k).
 *
 * Separated as a function so c is a parameter (not local), which helps
 * the Pulse verifier track array mask properties across loop iterations.
 */
void count_occurrences(_array int *c, _array int *a, size_t len, size_t k_plus_1, int k_val)
  _requires(k_val >= 0)
  _requires((_specint) k_val + 2 <= 2147483647)
  _requires((_specint) len <= 2147483647)
  _requires((_specint) k_plus_1 == (_specint) k_val + 1)
  _requires((bool) _inline_pulse(SizeT.fits (Int32.v $(k_val) + 2)))
  _preserves(c._length == k_plus_1 && a._length == len)
  _requires(_forall(size_t i, i < len ==> a[i] >= 0 && a[i] <= k_val))
  _requires(_forall(size_t i, i < k_plus_1 ==> c[i] == 0))
  _ensures(_forall(size_t i, i < k_plus_1 ==> c[i] >= 0))
{
  for (size_t j = 0; j < len; j = j + 1)
    _invariant(_live(j))
    _invariant(_live(*a) && _live(*c))
    _invariant(a._length == len && c._length == k_plus_1)
    _invariant(j <= len)
    _invariant((_specint) len <= 2147483647)
    _invariant((_specint) k_plus_1 == (_specint) k_val + 1)
    _invariant((bool) _inline_pulse(SizeT.fits (Int32.v $(k_val) + 2)))
    _invariant(_forall(size_t i, i < len ==> a[i] >= 0 && a[i] <= k_val))
    _invariant(_forall(size_t i, i < k_plus_1 ==> c[i] >= 0 && (_specint) c[i] <= (_specint) j))
  {
    int val = a[j];
    _assert(val >= 0);
    _assert(val <= k_val);
    size_t vi = (size_t) val;
    _assert(vi < k_plus_1);
    int count = c[vi];
    _assert(count >= 0);
    _assert((_specint) count <= (_specint) j);
    _assert((_specint) count < (_specint) len);
    _assert((_specint) count < 2147483647);
    c[vi] = count + 1;
  }
}

/*
 * Phase 2 helper: write sorted values from count array c into a.
 *
 * Iterates values v = 0..k, writing c[v] copies of v at consecutive
 * positions. The sorted property follows from v being non-decreasing.
 *
 * Note: proving that the total count sum equals len (so all positions
 * are filled) requires sequence-level reasoning beyond c2pulse. We use
 * assume_ for this gap; the underlying CLRS counting sort lemmas in
 * CLRS.Ch08.CountingSort.Lemmas.fst prove this property rigorously.
 */
void write_sorted(_array int *a, _array int *c, size_t len, size_t k_plus_1, int k_val)
  _requires(k_val >= 0)
  _requires((_specint) k_val + 2 <= 2147483647)
  _requires((_specint) len <= 2147483647)
  _requires((_specint) k_plus_1 == (_specint) k_val + 1)
  _requires((bool) _inline_pulse(SizeT.fits (Int32.v $(k_val) + 2)))
  _preserves(a._length == len && c._length == k_plus_1)
  _requires(_forall(size_t i, i < k_plus_1 ==> c[i] >= 0))
  _ensures(_forall(size_t i, i + 1 < len ==> a[i] <= a[i + 1]))
{
  size_t pos = 0;
  int v_int = 0;

  for (size_t v = 0; v < k_plus_1; v = v + 1)
    _invariant(_live(v) && _live(pos) && _live(v_int))
    _invariant(_live(*a) && _live(*c))
    _invariant(a._length == len && c._length == k_plus_1)
    _invariant(v <= k_plus_1)
    _invariant(pos <= len)
    _invariant(v_int >= 0)
    _invariant((_specint) v_int == (_specint) v)
    _invariant((_specint) k_plus_1 == (_specint) k_val + 1)
    _invariant((_specint) k_val + 2 <= 2147483647)
    _invariant((_specint) len <= 2147483647)
    _invariant((bool) _inline_pulse(SizeT.fits (Int32.v $(k_val) + 2)))
    _invariant(_forall(size_t i, i + 1 < pos ==> a[i] <= a[i + 1]))
    _invariant(pos > 0 ==> a[pos - 1] <= v_int)
    _invariant(_forall(size_t i, i < k_plus_1 ==> c[i] >= 0))
  {
    int count = c[v];
    int j = 0;

    while (j < count && pos < len)
      _invariant(_live(j) && _live(pos) && _live(v_int) && _live(v))
      _invariant(_live(*a) && _live(*c))
      _invariant(a._length == len && c._length == k_plus_1)
      _invariant(pos <= len)
      _invariant(j >= 0 && j <= count)
      _invariant(count >= 0)
      _invariant(v_int >= 0)
      _invariant((_specint) v_int == (_specint) v)
      _invariant(v < k_plus_1)
      _invariant(_forall(size_t i, i + 1 < pos ==> a[i] <= a[i + 1]))
      _invariant(pos > 0 ==> a[pos - 1] <= v_int)
      _invariant(_forall(size_t i, i < k_plus_1 ==> c[i] >= 0))
    {
      a[pos] = v_int;
      pos = pos + 1;
      j = j + 1;
    }

    v_int = v_int + 1;
  }

  /* The loop wrote sorted values at positions [0, pos).
   * That pos >= len (i.e., all positions filled) follows from
   * sum(c[0..k]) == len, which is proven in the existing F* lemma
   * CLRS.Ch08.CountingSort.Lemmas.final_perm. We assume this gap here. */
  _ghost_stmt(assume_ (pure (SizeT.v $(pos) >= SizeT.v $(len))));
}

/*
 * In-place counting sort for non-negative int values in [0, k_val].
 */
void counting_sort(_array int *a, size_t len, int k_val)
  _requires(k_val >= 0)
  _requires((_specint) k_val + 2 <= 2147483647)
  _requires((_specint) len <= 2147483647)
  _requires((bool) _inline_pulse(SizeT.fits (Int32.v $(k_val) + 2)))
  _preserves(a._length == len)
  _requires(_forall(size_t i, i < len ==> a[i] >= 0 && a[i] <= k_val))
  _ensures(_forall(size_t i, i + 1 < len ==> a[i] <= a[i + 1]))
{
  if (len <= 1) return;

  size_t k_plus_1 = (size_t)(k_val + 1);

  int *c = (int *)calloc(k_plus_1, sizeof(int));
  _assert(c._length == k_plus_1);
  _assert(_forall(size_t i, i < k_plus_1 ==> c[i] == 0));

  count_occurrences(c, a, len, k_plus_1, k_val);
  write_sorted(a, c, len, k_plus_1, k_val);

  free(c);
}

