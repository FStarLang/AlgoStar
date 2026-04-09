/*
 * Activity Selection — C implementation with c2pulse verification.
 *
 * Implements the greedy activity selection algorithm (CLRS §16.1,
 * GREEDY-ACTIVITY-SELECTOR) for finding the maximum-cardinality
 * set of mutually compatible (non-overlapping) activities.
 *
 * Proves:
 *   1. count bounds: 0 <= count <= n; count >= 1 when n > 0
 *   2. First selected activity is index 0
 *   3. Selected indices are valid (< n) and strictly increasing
 *   4. Pairwise compatibility: finish[out[j]] <= start[out[j+1]]
 *   5. Earliest compatible: every skipped activity is incompatible
 *      with the last selected before it
 *
 * The earliest_compatible property (5) is the key greedy invariant
 * that enables the optimality proof (CLRS Theorem 16.1) via
 * bridge lemmas in CLRS.Ch16.ActivitySelection.C.BridgeLemmas.
 *
 * Preconditions:
 *   - finish times are sorted in non-decreasing order
 *   - each activity has start < finish (positive duration)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * Greedy activity selection.
 *
 * Input:
 *   start_times[0..n)   — start times of activities
 *   finish_times[0..n)  — finish times, sorted non-decreasingly
 *   out[0..n)           — output buffer for selected activity indices
 *   n                   — number of activities
 *
 * Output:
 *   Returns count (number of selected activities).
 *   out[0..count) contains the selected activity indices.
 *
 * Algorithm:
 *   Always select activity 0 (earliest finish).
 *   Scan remaining activities; select the next one whose start time
 *   is >= the finish time of the last selected activity.
 */
size_t activity_selection(
    _array int *start_times,
    _array int *finish_times,
    _array size_t *out,
    size_t n)
  _requires(start_times._length == n)
  _requires(finish_times._length == n)
  _requires(out._length == n)
  _requires(_forall(size_t i, i + 1 < n ==> finish_times[i] <= finish_times[i + 1]))
  _requires(_forall(size_t i, i < n ==> start_times[i] < finish_times[i]))
  _ensures(start_times._length == n)
  _ensures(finish_times._length == n)
  _ensures(out._length == n)
  _ensures(return <= n)
  _ensures(n == 0 ==> return == 0)
  _ensures(n > 0 ==> return >= 1)
  _ensures(n > 0 ==> out[0] == 0)
  _ensures(_forall(size_t j, j < return ==> out[j] < n))
  _ensures(_forall(size_t j, j + 1 < return ==> out[j] < out[j + 1]))
  _ensures(_forall(size_t j, j + 1 < return ==> finish_times[out[j]] <= start_times[out[j + 1]]))
  /* earliest_compatible: between consecutive selected */
  _ensures(n > 0 ==> _forall(size_t j, j + 1 < return ==>
    _forall(size_t z, out[j] < z && z < out[j + 1] && z < n ==>
      start_times[z] < finish_times[out[j]])))
{
  if (n == 0) return 0;

  out[0] = 0;
  size_t count = 1;
  int last_finish = finish_times[0];

  for (size_t i = 1; i < n; i = i + 1)
    _invariant(_live(i) && _live(count) && _live(last_finish))
    _invariant(_live(*start_times) && _live(*finish_times) && _live(*out))
    _invariant(start_times._length == n && finish_times._length == n && out._length == n)
    _invariant(i >= 1 && i <= n)
    _invariant(count >= 1 && count <= i)
    _invariant(out[0] == 0)
    _invariant(_forall(size_t j, j < count ==> out[j] < n))
    _invariant(_forall(size_t j, j < count ==> out[j] < i))
    _invariant(_forall(size_t j, j + 1 < count ==> out[j] < out[j + 1]))
    _invariant(_forall(size_t j, j + 1 < count ==> finish_times[out[j]] <= start_times[out[j + 1]]))
    _invariant(last_finish == finish_times[out[count - 1]])
    /* earliest_compatible: skipped activities after last selection are incompatible */
    _invariant(_forall(size_t z, out[count - 1] < z && z < i && z < n ==>
      start_times[z] < finish_times[out[count - 1]]))
    /* earliest_compatible: between consecutive selected activities */
    _invariant(_forall(size_t j, j + 1 < count ==>
      _forall(size_t z, out[j] < z && z < out[j + 1] && z < n ==>
        start_times[z] < finish_times[out[j]])))
    _ensures(count >= 1 && count <= n)
    _ensures(out[0] == 0)
    _ensures(_forall(size_t j, j < count ==> out[j] < n))
    _ensures(_forall(size_t j, j + 1 < count ==> out[j] < out[j + 1]))
    _ensures(_forall(size_t j, j + 1 < count ==> finish_times[out[j]] <= start_times[out[j + 1]]))
    _ensures(_forall(size_t j, j + 1 < count ==>
      _forall(size_t z, out[j] < z && z < out[j + 1] && z < n ==>
        start_times[z] < finish_times[out[j]])))
  {
    if (start_times[i] >= last_finish) {
      out[count] = i;
      count = count + 1;
      last_finish = finish_times[i];
    }
  }

  return count;
}
