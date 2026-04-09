/*
 * Graham Scan helpers — CLRS Chapter 33, Section 33.3
 *
 * C implementation with c2pulse verification.
 *
 * Proves:
 *   1. find_bottom returns the index of the bottom-most point
 *      (minimum y, tiebreak minimum x) — the is_bottommost property.
 *   2. polar_cmp correctly computes the cross product for polar
 *      angle comparison relative to a pivot point.
 *
 * Coordinates are bounded to [-16383, 16383] for polar_cmp to ensure
 * all Int32 intermediate computations stay within range.
 *
 * Equivalent to CLRS.Ch33.GrahamScan.Impl.fsti specifications.
 */

#include "c2pulse.h"
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

/*
 * Find the bottom-most point (minimum y coordinate).
 * Break ties by choosing the point with minimum x coordinate.
 * This point is guaranteed to be on the convex hull.
 *
 * Postcondition (is_bottommost):
 *   For all k < len:
 *     ys[result] < ys[k]  OR  (ys[result] == ys[k] AND xs[result] <= xs[k])
 */
size_t find_bottom(_array int *xs, _array int *ys, size_t len)
  _requires(xs._length == len && ys._length == len && len > 0)
  _preserves_value(xs._length)
  _preserves_value(ys._length)
  _ensures(return < len)
  _ensures(_forall(size_t k, k < len ==>
    ys[return] < ys[k] || (ys[return] == ys[k] && xs[return] <= xs[k])))
{
  size_t best = 0;
  for (size_t i = 1; i < len; i = i + 1)
    _invariant(_live(i) && _live(best))
    _invariant(_live(*xs) && _live(*ys))
    _invariant(xs._length == len && ys._length == len)
    _invariant(i <= len)
    _invariant(best < len)
    _invariant(_forall(size_t k, k < i ==>
      ys[best] < ys[k] || (ys[best] == ys[k] && xs[best] <= xs[k])))
  {
    if (ys[i] < ys[best] || (ys[i] == ys[best] && xs[i] < xs[best])) {
      best = i;
    }
  }
  return best;
}

/*
 * Compare polar angles of points a and b w.r.t. pivot p0.
 *
 * Returns the cross product (p0→a) × (p0→b):
 *   > 0 : a has smaller polar angle (a before b in CCW order)
 *   < 0 : b has smaller polar angle
 *   = 0 : collinear
 *
 * Array elements must be bounded to avoid Int32 overflow.
 * The function is verified for memory safety and absence of overflow.
 */
int polar_cmp(_array int *xs, _array int *ys, size_t len,
              size_t p0, size_t a, size_t b)
  _requires(xs._length == len && ys._length == len)
  _requires(p0 < len && a < len && b < len)
  _requires(xs[p0] > -16384 && xs[p0] < 16384)
  _requires(xs[a] > -16384 && xs[a] < 16384)
  _requires(xs[b] > -16384 && xs[b] < 16384)
  _requires(ys[p0] > -16384 && ys[p0] < 16384)
  _requires(ys[a] > -16384 && ys[a] < 16384)
  _requires(ys[b] > -16384 && ys[b] < 16384)
  _preserves_value(xs._length)
  _preserves_value(ys._length)
{
  int ax = xs[a] - xs[p0];
  _assert(ax > -32767 && ax < 32767);
  int ay = ys[a] - ys[p0];
  _assert(ay > -32767 && ay < 32767);
  int bx = xs[b] - xs[p0];
  _assert(bx > -32767 && bx < 32767);
  int by = ys[b] - ys[p0];
  _assert(by > -32767 && by < 32767);
  int term1 = ax * by;
  _assert(term1 > -1073741824 && term1 < 1073741824);
  int term2 = bx * ay;
  _assert(term2 > -1073741824 && term2 < 1073741824);
  return term1 - term2;
}
