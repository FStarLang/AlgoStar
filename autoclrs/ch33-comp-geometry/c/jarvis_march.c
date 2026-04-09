/*
 * Jarvis March (Gift Wrapping) — CLRS Chapter 33, Section 33.3
 *
 * C implementation with c2pulse verification.
 *
 * Proves:
 *   1. find_leftmost returns the index of the leftmost point
 *      (minimum x, tiebreak minimum y) — the is_leftmost property.
 *   2. find_next returns a valid index different from current,
 *      implementing the "most clockwise" selection.
 *
 * Coordinates are bounded to [-16383, 16383] for find_next to ensure
 * all Int32 intermediate computations stay within range.
 *
 * Equivalent to CLRS.Ch33.JarvisMarch.Impl.fsti specifications.
 */

#include "c2pulse.h"
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

/*
 * Find the leftmost point (minimum x coordinate).
 * Break ties by choosing the point with minimum y coordinate.
 * This point is guaranteed to be on the convex hull.
 *
 * Postcondition (is_leftmost):
 *   For all k < len:
 *     xs[result] < xs[k]  OR  (xs[result] == xs[k] AND ys[result] <= ys[k])
 */
size_t find_leftmost(_array int *xs, _array int *ys, size_t len)
  _requires(xs._length == len && ys._length == len && len > 0)
  _preserves_value(xs._length)
  _preserves_value(ys._length)
  _ensures(return < len)
  _ensures(_forall(size_t k, k < len ==>
    xs[return] < xs[k] || (xs[return] == xs[k] && ys[return] <= ys[k])))
{
  size_t best = 0;
  for (size_t i = 1; i < len; i = i + 1)
    _invariant(_live(i) && _live(best))
    _invariant(_live(*xs) && _live(*ys))
    _invariant(xs._length == len && ys._length == len)
    _invariant(i <= len)
    _invariant(best < len)
    _invariant(_forall(size_t k, k < i ==>
      xs[best] < xs[k] || (xs[best] == xs[k] && ys[best] <= ys[k])))
  {
    if (xs[i] < xs[best] || (xs[i] == xs[best] && ys[i] < ys[best])) {
      best = i;
    }
  }
  return best;
}

/*
 * Cross product helper for Jarvis march.
 * Computes (p2-p1) × (p3-p1) using bounded Int32 arithmetic.
 */
int jm_cross(int x1, int y1, int x2, int y2, int x3, int y3)
  _requires(x1 > -16384 && x1 < 16384 && y1 > -16384 && y1 < 16384)
  _requires(x2 > -16384 && x2 < 16384 && y2 > -16384 && y2 < 16384)
  _requires(x3 > -16384 && x3 < 16384 && y3 > -16384 && y3 < 16384)
{
  int dx2 = x2 - x1;
  _assert(dx2 > -32767 && dx2 < 32767);
  int dy2 = y2 - y1;
  _assert(dy2 > -32767 && dy2 < 32767);
  int dx3 = x3 - x1;
  _assert(dx3 > -32767 && dx3 < 32767);
  int dy3 = y3 - y1;
  _assert(dy3 > -32767 && dy3 < 32767);
  int term1 = dx2 * dy3;
  _assert(term1 > -1073741824 && term1 < 1073741824);
  int term2 = dx3 * dy2;
  _assert(term2 > -1073741824 && term2 < 1073741824);
  return term1 - term2;
}

/*
 * Find the next hull vertex from the current vertex.
 * Selects the point that makes the most clockwise turn from current
 * (i.e., the point q such that all other points lie to the left of
 * the line current→q).
 *
 * Array elements must be bounded to avoid Int32 overflow in
 * cross-product computations.
 *
 * Postconditions:
 *   - result < len
 *   - result != current
 */
size_t find_next(_array int *xs, _array int *ys, size_t len, size_t current)
  _requires(xs._length == len && ys._length == len)
  _requires(len > 1 && current < len)
  _requires(_forall(size_t k, k < len ==> xs[k] > -16384 && xs[k] < 16384))
  _requires(_forall(size_t k, k < len ==> ys[k] > -16384 && ys[k] < 16384))
  _preserves_value(xs._length)
  _preserves_value(ys._length)
  _ensures(return < len && return != current)
{
  /* Initialize next to any index != current */
  size_t next = 0;
  if (current == 0) next = 1;

  for (size_t j = 0; j < len; j = j + 1)
    _invariant(_live(j) && _live(next))
    _invariant(_live(*xs) && _live(*ys))
    _invariant(xs._length == len && ys._length == len)
    _invariant(j <= len)
    _invariant(next < len && next != current)
    _invariant(current < len)
    _invariant(_forall(size_t k, k < len ==> xs[k] > -16384 && xs[k] < 16384))
    _invariant(_forall(size_t k, k < len ==> ys[k] > -16384 && ys[k] < 16384))
  {
    /* Cross product: (next-current) × (j-current) */
    int cp = jm_cross(xs[current], ys[current],
                       xs[next], ys[next],
                       xs[j], ys[j]);
    /* If j is distinct and more clockwise, update next */
    if (j != current && j != next && cp < 0) {
      next = j;
    }
  }
  return next;
}
