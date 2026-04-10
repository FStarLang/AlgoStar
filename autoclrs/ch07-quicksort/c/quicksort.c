/*
 * CLRS Chapter 7: Quicksort — C implementation with c2pulse verification.
 *
 * Uses recursive quicksort via c2pulse's _rec support.
 *
 * Proved mechanically (via c2pulse annotations):
 *   - Partition: left ≤ pivot, right > pivot, bounds + frame preserved,
 *     no-fabrication (each output element existed in the input)
 *   - Quicksort: sorted postcondition, bounds preservation, frame
 *   - Termination via _decreases(hi - lo)
 *
 * The proof strategy uses concrete int bounds (lb, rb) threaded through
 * the recursion.  Partition preserves bounds; after recursive sorts,
 * left elements ≤ pivot ≤ right elements, so the combined range is sorted.
 *
 * This matches the approach in CLRS.Ch07.Quicksort.Impl.fst which uses
 * ghost bounds (lb, rb : erased int) and between_bounds / lemma_sorted_append.
 *
 * No-fabrication property: every element in the output range was present
 * somewhere in the input range.  Combined with the bridge lemmas in
 * CLRS.Ch07.Quicksort.C.BridgeLemmas, this connects to the full
 * SortSpec.permutation proved in the Pulse implementation.
 *
 * Complexity tracking (ghost tick counters) is Pulse-specific and omitted
 * here; the full complexity proof is in CLRS.Ch07.Quicksort.Impl.fst.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Lomuto partition with bounds, frame, and no-fabrication tracking.
 *
 * Chooses a[hi-1] as pivot.  Scans left-to-right, swapping elements
 * ≤ pivot into the front partition.  Finally swaps pivot into place.
 *
 * Postconditions match CLRS.Ch07.Partition.Impl.fsti:
 *   - Partition property: left ≤ pivot, right > pivot (strictly_larger_than)
 *   - Bounds preserved: all elements in [lo,hi) stay in [lb,rb] (between_bounds)
 *   - Frame: elements outside [lo,hi) unchanged
 *   - No-fabrication: every output element existed in the input range
 *
 * The full SortSpec.permutation is proved in the Pulse Impl via ghost
 * sequences; the no-fabrication _exists here is a weaker but still
 * useful guarantee that connects to permutation via bridge lemmas.
 */
size_t partition(_array int *a, size_t len, size_t lo, size_t hi, int lb, int rb)
  _requires(a._length == len && lo < hi && hi <= len)
  _requires(lb <= rb)
  _requires(_forall(size_t k, lo <= k && k < hi ==> lb <= a[k] && a[k] <= rb))
  _ensures(a._length == len && lo <= return && return < hi)
  _ensures(_forall(size_t k, lo <= k && k < return ==> a[k] <= a[return]))
  _ensures(_forall(size_t k, return < k && k < hi ==> a[return] < a[k]))
  _ensures(lb <= a[return] && a[return] <= rb)
  _ensures(_forall(size_t k, lo <= k && k < hi ==> lb <= a[k] && a[k] <= rb))
  _ensures(_forall(size_t k, k < len && (k < lo || hi <= k) ==> a[k] == _old(a[k])))
  /* No-fabrication: every output element in [lo,hi) existed in the input */
  _ensures(_forall(size_t k, lo <= k && k < hi ==>
      _exists(size_t j, lo <= j && j < hi && a[k] == _old(a[j]))))
{
  int pivot = a[hi - 1];
  size_t i = lo;
  int tmp = 0;

  for (size_t j = lo; j < hi - 1; j = j + 1)
    _invariant(_live(j) && _live(i) && _live(pivot) && _live(tmp))
    _invariant(_live(*a))
    _invariant(a._length == len)
    _invariant(lo <= i && i <= j && j < hi)
    _invariant(a[hi - 1] == pivot)
    _invariant(lb <= pivot && pivot <= rb)
    _invariant(_forall(size_t k, lo <= k && k < i ==> a[k] <= pivot))
    _invariant(_forall(size_t k, i <= k && k < j ==> a[k] > pivot))
    _invariant(_forall(size_t k, lo <= k && k < hi ==> lb <= a[k] && a[k] <= rb))
    _invariant(_forall(size_t k, k < len && (k < lo || hi <= k) ==> a[k] == _old(a[k])))
    /* No-fabrication: loop invariant */
    _invariant(_forall(size_t k, lo <= k && k < hi ==>
        _exists(size_t m, lo <= m && m < hi && a[k] == _old(a[m]))))
  {
    if (a[j] <= pivot) {
      tmp = a[i];
      a[i] = a[j];
      a[j] = tmp;
      i = i + 1;
    }
  }

  tmp = a[i];
  a[i] = a[hi - 1];
  a[hi - 1] = tmp;

  return i;
}

/*
 * Recursive quicksort with bounds tracking.
 *
 * lb, rb: all elements in a[lo..hi) are between lb and rb.
 * After sorting, the range is sorted and elements remain in [lb, rb].
 *
 * Termination: hi - lo strictly decreases at each recursive call.
 */
_rec void quicksort_rec(_array int *a, size_t len, size_t lo, size_t hi, int lb, int rb)
  _requires(a._length == len && lo <= hi && hi <= len)
  _requires(lb <= rb)
  _requires(_forall(size_t k, lo <= k && k < hi ==> lb <= a[k] && a[k] <= rb))
  _preserves_value(a._length)
  _ensures(_forall(size_t k, lo <= k && k + 1 < hi ==> a[k] <= a[k + 1]))
  _ensures(_forall(size_t k, lo <= k && k < hi ==> lb <= a[k] && a[k] <= rb))
  _ensures(_forall(size_t k, k < len && (k < lo || hi <= k) ==> a[k] == _old(a[k])))
  _decreases(hi - lo)
{
  if (hi - lo < 2) return;

  size_t p = partition(a, len, lo, hi, lb, rb);
  int pivot = a[p];

  /* Sort left: elements in [lo, p) are all <= pivot and >= lb */
  quicksort_rec(a, len, lo, p, lb, pivot);

  /* Sort right: elements in [p+1, hi) are all >= pivot and <= rb */
  quicksort_rec(a, len, p + 1, hi, pivot, rb);
}

/*
 * Top-level quicksort.
 *
 * Computes the array min and max to supply initial bounds, then
 * delegates to quicksort_rec.  This mirrors the F* implementation
 * which uses seq_min / seq_max as ghost bounds.
 */
void quicksort(_array int *a, size_t len)
  _preserves(a._length == len)
  _ensures(_forall(size_t i, i + 1 < len ==> a[i] <= a[i + 1]))
{
  if (len <= 1) return;

  /* Compute min/max bounds */
  int lb = a[0];
  int rb = a[0];
  for (size_t i = 1; i < len; i = i + 1)
    _invariant(_live(i) && _live(lb) && _live(rb) && _live(*a))
    _invariant(a._length == len)
    _invariant(1 <= i && i <= len)
    _invariant(lb <= rb)
    _invariant(_forall(size_t k, k < i ==> lb <= a[k] && a[k] <= rb))
  {
    if (a[i] < lb) lb = a[i];
    if (a[i] > rb) rb = a[i];
  }

  quicksort_rec(a, len, 0, len, lb, rb);
}
