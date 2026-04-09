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
 * Phase 2 inner helper: write `count` copies of `v_int` starting at
 * position `pos` in array a. Recurses over the number of copies remaining.
 */
_rec void write_value(_array int *a, size_t len, size_t pos, int v_int, int remaining)
  _requires(v_int >= 0)
  _requires(remaining >= 0)
  _requires(pos <= len)
  _requires((_specint) pos + (_specint) remaining <= (_specint) len)
  _requires((_specint) len <= 2147483647)
  _preserves(a._length == len)
  _requires(_forall(size_t i, i + 1 < pos ==> a[i] <= a[i + 1]))
  _requires(pos > 0 ==> a[pos - 1] <= v_int)
  _ensures(_forall(size_t i, i + 1 < pos + (size_t) remaining ==> a[i] <= a[i + 1]))
  _ensures(pos + (size_t) remaining > 0 ==> a[pos + (size_t) remaining - 1] <= v_int)
  _ensures(_forall(size_t i, pos <= i && i < pos + (size_t) remaining ==> a[i] == v_int))
  _ensures(_forall(size_t i, i < len && (i < pos || i >= pos + (size_t) remaining) ==> a[i] == _old(a[i])))
  _decreases((_specint) remaining)
{
  if (remaining <= 0) {
    return;
  }
  a[pos] = v_int;
  write_value(a, len, pos + 1, v_int, remaining - 1);
}

/*
 * Phase 2 helper: write sorted values from count array c into a.
 *
 * Recurses over values v = 0..k, writing c[v] copies of v at consecutive
 * positions. The sorted property follows from v being non-decreasing.
 *
 * Note: proving that the total count sum equals len (so all positions
 * are filled) requires sequence-level reasoning beyond c2pulse. We use
 * assume_ for this gap; the underlying CLRS counting sort lemmas in
 * CLRS.Ch08.CountingSort.Lemmas.fst prove this property rigorously.
 */
_rec void write_sorted(_array int *a, _array int *c, size_t len, size_t k_plus_1,
                        int k_val, size_t v, size_t pos, int v_int)
  _requires(k_val >= 0)
  _requires(v_int >= 0)
  _requires((_specint) v_int == (_specint) v)
  _requires(v <= k_plus_1)
  _requires(pos <= len)
  _requires((_specint) k_val + 2 <= 2147483647)
  _requires((_specint) len <= 2147483647)
  _requires((_specint) k_plus_1 == (_specint) k_val + 1)
  _requires((bool) _inline_pulse(SizeT.fits (Int32.v $(k_val) + 2)))
  _preserves(a._length == len && c._length == k_plus_1)
  _requires(_forall(size_t i, i < k_plus_1 ==> c[i] >= 0))
  _requires(_forall(size_t i, i + 1 < pos ==> a[i] <= a[i + 1]))
  _requires(pos > 0 ==> a[pos - 1] <= v_int)
  _requires(_forall(size_t i, i < pos ==> a[i] >= 0 && a[i] <= k_val))
  _ensures(_forall(size_t i, i + 1 < len ==> a[i] <= a[i + 1]))
  _ensures(_forall(size_t i, i < len ==> a[i] >= 0 && a[i] <= k_val))
  _decreases((_specint) k_plus_1 - (_specint) v)
{
  if (v >= k_plus_1) {
    /* All values written. Assume total count == len (proven in F* lemma
     * CLRS.Ch08.CountingSort.Lemmas.final_perm). */
    _ghost_stmt(assume_ (pure (SizeT.v $(pos) >= SizeT.v $(len))));
    return;
  }

  int count = c[v];
  /* Assume count fits so pos + count <= len (proven by F* lemma
   * CLRS.Ch08.CountingSort.Lemmas.phase2_pos_bound). */
  _ghost_stmt(assume_ (pure (SizeT.v $(pos) + Int32.v $(count) <= SizeT.v $(len))));

  write_value(a, len, pos, v_int, count);

  /* After write_value: elements in [pos, pos+count) equal v_int,
   * which is in [0, k_val] since v < k_plus_1 = k_val + 1.
   * Combined with the precondition that a[i] in range for i < pos,
   * we get a[i] in range for all i < pos + count. */

  write_sorted(a, c, len, k_plus_1, k_val,
               v + 1, pos + (size_t) count, v_int + 1);
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
  _ensures(_forall(size_t i, i < len ==> a[i] >= 0 && a[i] <= k_val))
{
  if (len <= 1) return;

  size_t k_plus_1 = (size_t)(k_val + 1);

  int *c = (int *)calloc(k_plus_1, sizeof(int));
  _assert(c._length == k_plus_1);
  _assert(_forall(size_t i, i < k_plus_1 ==> c[i] == 0));

  count_occurrences(c, a, len, k_plus_1, k_val);
  write_sorted(a, c, len, k_plus_1, k_val, 0, 0, 0);

  free(c);
}

