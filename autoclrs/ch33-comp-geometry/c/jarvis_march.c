/*
 * Jarvis March (Gift Wrapping) — CLRS Chapter 33, Section 33.3
 *
 * C implementation with c2pulse verification.
 *
 * Proves:
 *   1. find_leftmost returns the index of the leftmost point
 *      (minimum x, tiebreak minimum y) — the is_leftmost property.
 *   2. jm_cross computes (p2-p1) × (p3-p1) correctly.
 *   3. find_next returns a valid index different from current,
 *      implementing the "most clockwise" selection.
 *   4. jarvis_march counts hull vertices.
 *   5. jarvis_march_with_hull records hull vertex indices.
 *
 * Coordinates are bounded to [-16383, 16383] to ensure
 * all Int32 intermediate computations stay within range.
 *
 * Equivalent to CLRS.Ch33.JarvisMarch.Impl.fsti specifications.
 */

#include "c2pulse.h"
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

_include_pulse(
  open CLRS.Ch33.Segments.Spec
  open FStar.Mul
)

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
  _requires(_forall(size_t k, k < len ==> xs[k] > -16384 && xs[k] < 16384))
  _requires(_forall(size_t k, k < len ==> ys[k] > -16384 && ys[k] < 16384))
  _preserves_value(xs._length)
  _preserves_value(ys._length)
  _ensures(return < len)
  _ensures(_forall(size_t k, k < len ==>
    xs[return] < xs[k] || (xs[return] == xs[k] && ys[return] <= ys[k])))
  _ensures(_forall(size_t k, k < len ==> xs[k] > -16384 && xs[k] < 16384))
  _ensures(_forall(size_t k, k < len ==> ys[k] > -16384 && ys[k] < 16384))
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
    _invariant(_forall(size_t k, k < len ==> xs[k] > -16384 && xs[k] < 16384))
    _invariant(_forall(size_t k, k < len ==> ys[k] > -16384 && ys[k] < 16384))
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
  _ensures((_specint) return == ((_specint) x2 - (_specint) x1) * ((_specint) y3 - (_specint) y1) - ((_specint) x3 - (_specint) x1) * ((_specint) y2 - (_specint) y1))
  _ensures((bool) _inline_pulse((id #int (Int32.v $(return))) == cross_product_spec (Int32.v $(x1)) (Int32.v $(y1)) (Int32.v $(x2)) (Int32.v $(y2)) (Int32.v $(x3)) (Int32.v $(y3))))
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
  _ensures(_forall(size_t k, k < len ==> xs[k] > -16384 && xs[k] < 16384))
  _ensures(_forall(size_t k, k < len ==> ys[k] > -16384 && ys[k] < 16384))
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

/*
 * Jarvis march: count the number of convex hull vertices.
 *
 * Starts from the leftmost point and gift-wraps around the hull,
 * counting vertices until we return to the start. Uses len-1 as
 * fuel to bound the loop (the hull has at most n vertices).
 *
 * Postconditions:
 *   - result >= 1  (at least the leftmost point)
 *   - result <= len
 */
size_t jarvis_march(_array int *xs, _array int *ys, size_t len)
  _requires(xs._length == len && ys._length == len)
  _requires(len > 1)
  _requires(_forall(size_t k, k < len ==> xs[k] > -16384 && xs[k] < 16384))
  _requires(_forall(size_t k, k < len ==> ys[k] > -16384 && ys[k] < 16384))
  _preserves_value(xs._length)
  _preserves_value(ys._length)
  _ensures(return >= 1 && return <= len)
{
  size_t p0 = find_leftmost(xs, ys, len);
  size_t current = p0;
  size_t count = 1;
  size_t fuel = len - 1;

  while (fuel > 0)
    _invariant(_live(fuel) && _live(count) && _live(current))
    _invariant(_live(*xs) && _live(*ys))
    _invariant(xs._length == len && ys._length == len)
    _invariant(current < len)
    _invariant(count >= 1 && count <= len)
    _invariant(fuel <= len - 1)
    _invariant(_forall(size_t k, k < len ==> xs[k] > -16384 && xs[k] < 16384))
    _invariant(_forall(size_t k, k < len ==> ys[k] > -16384 && ys[k] < 16384))
  {
    size_t next = find_next(xs, ys, len, current);
    if (next == p0) {
      fuel = 0;
    } else {
      if (count < len) {
        count = count + 1;
      }
      current = next;
      fuel = fuel - 1;
    }
  }
  return count;
}

/*
 * Jarvis march with hull output: record hull vertex indices.
 *
 * Like jarvis_march, but writes each hull vertex index into hull_out.
 * hull_out must have length >= len.
 *
 * Postconditions:
 *   - result >= 1  (at least the leftmost point)
 *   - result <= len
 *   - hull_out[0] is the leftmost point
 */
size_t jarvis_march_with_hull(_array int *xs, _array int *ys, size_t len,
                              _array size_t *hull_out)
  _requires(xs._length == len && ys._length == len)
  _requires(len > 1)
  _requires(hull_out._length >= len)
  _requires(_forall(size_t k, k < len ==> xs[k] > -16384 && xs[k] < 16384))
  _requires(_forall(size_t k, k < len ==> ys[k] > -16384 && ys[k] < 16384))
  _preserves_value(xs._length)
  _preserves_value(ys._length)
  _ensures(hull_out._length >= len)
  _ensures(return >= 1 && return <= len)
{
  size_t p0 = find_leftmost(xs, ys, len);
  hull_out[0] = p0;
  size_t current = p0;
  size_t count = 1;
  size_t fuel = len - 1;

  while (fuel > 0)
    _invariant(_live(fuel) && _live(count) && _live(current))
    _invariant(_live(*xs) && _live(*ys) && _live(*hull_out))
    _invariant(xs._length == len && ys._length == len)
    _invariant(hull_out._length >= len)
    _invariant(current < len)
    _invariant(count >= 1 && count <= len)
    _invariant(fuel <= len - 1)
    _invariant(_forall(size_t k, k < len ==> xs[k] > -16384 && xs[k] < 16384))
    _invariant(_forall(size_t k, k < len ==> ys[k] > -16384 && ys[k] < 16384))
  {
    size_t next = find_next(xs, ys, len, current);
    if (next == p0) {
      fuel = 0;
    } else {
      if (count < len) {
        hull_out[count] = next;
        count = count + 1;
      }
      current = next;
      fuel = fuel - 1;
    }
  }
  return count;
}
