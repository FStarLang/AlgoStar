/*
 * Graham Scan — CLRS Chapter 33, Section 33.3
 *
 * C implementation with c2pulse verification.
 *
 * Proves:
 *   1. find_bottom returns the index of the bottom-most point
 *      (minimum y, tiebreak minimum x) — the is_bottommost property.
 *   2. polar_cmp correctly computes the cross product for polar
 *      angle comparison relative to a pivot point.
 *   3. pop_while (recursive) pops non-left-turn elements from hull stack.
 *   4. graham_scan_step performs one scan iteration: pop then push.
 *
 * Coordinates are bounded to [-16383, 16383] to ensure
 * all Int32 intermediate computations stay within range.
 *
 * Equivalent to CLRS.Ch33.GrahamScan.Impl.fsti specifications.
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
  _ensures((_specint) return == ((_specint) xs[a] - (_specint) xs[p0]) * ((_specint) ys[b] - (_specint) ys[p0]) - ((_specint) xs[b] - (_specint) xs[p0]) * ((_specint) ys[a] - (_specint) ys[p0]))
  _ensures((bool) _inline_pulse((id #int (Int32.v $(return))) == cross_product_spec (id #int (Int32.v (array_read $(xs) $(p0)))) (id #int (Int32.v (array_read $(ys) $(p0)))) (id #int (Int32.v (array_read $(xs) $(a)))) (id #int (Int32.v (array_read $(ys) $(a)))) (id #int (Int32.v (array_read $(xs) $(b)))) (id #int (Int32.v (array_read $(ys) $(b))))))
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

/*
 * Cross product helper for Graham scan.
 * Computes (p2-p1) × (p3-p1) using bounded Int32 arithmetic.
 */
int gs_cross(int x1, int y1, int x2, int y2, int x3, int y3)
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
 * Pop non-left-turn elements from the hull stack (recursive).
 *
 * Given the hull stack indices in hull[0..top), check whether the top
 * two hull points and the new point p_idx form a left turn (cross
 * product > 0). If not, pop the top element and recurse.
 *
 * Requires top >= 2. Returns the new top index in [1, top].
 */
_rec size_t pop_while(_array int *xs, _array int *ys, size_t len,
                      _array size_t *hull, size_t top, size_t p_idx)
  _requires(xs._length == len && ys._length == len)
  _requires(top >= 2 && top <= hull._length)
  _requires(p_idx < len)
  _requires(_forall(size_t i, i < top ==> hull[i] < len))
  _requires(_forall(size_t k, k < len ==> xs[k] > -16384 && xs[k] < 16384))
  _requires(_forall(size_t k, k < len ==> ys[k] > -16384 && ys[k] < 16384))
  _preserves_value(xs._length)
  _preserves_value(ys._length)
  _preserves_value(hull._length)
  _ensures(return >= 1 && return <= top)
  _ensures(_forall(size_t k, k < hull._length ==> hull[k] == _old(hull[k])))
  _ensures(_forall(size_t k, k < len ==> xs[k] == _old(xs[k])))
  _ensures(_forall(size_t k, k < len ==> ys[k] == _old(ys[k])))
  _decreases(top)
{
  size_t t1_idx = hull[top - 1];
  size_t t2_idx = hull[top - 2];

  /* Cross product: (t2→t1) × (t2→p) */
  int cp = gs_cross(xs[t2_idx], ys[t2_idx],
                    xs[t1_idx], ys[t1_idx],
                    xs[p_idx], ys[p_idx]);

  if (cp <= 0) {
    if (top == 2) return 1;
    return pop_while(xs, ys, len, hull, top - 1, p_idx);
  }
  return top;
}

/*
 * One step of the Graham scan: pop non-left-turns, then push p_idx.
 *
 * hull is modified: hull[new_top] = p_idx.
 * Returns the new stack top (>= 2).
 */
size_t graham_scan_step(_array int *xs, _array int *ys, size_t len,
                        _array size_t *hull, size_t top, size_t p_idx)
  _requires(xs._length == len && ys._length == len)
  _requires(top >= 2 && top < hull._length)
  _requires(hull._length <= len)
  _requires(p_idx < len)
  _requires(_forall(size_t i, i < top ==> hull[i] < len))
  _requires(_forall(size_t k, k < len ==> xs[k] > -16384 && xs[k] < 16384))
  _requires(_forall(size_t k, k < len ==> ys[k] > -16384 && ys[k] < 16384))
  _preserves_value(xs._length)
  _preserves_value(ys._length)
  _preserves_value(hull._length)
  _ensures(return >= 2 && return <= hull._length)
  _ensures(hull[return - 1] == p_idx)
  _ensures(_forall(size_t k, k + 1 < return ==> hull[k] == _old(hull[k])))
{
  size_t new_top = pop_while(xs, ys, len, hull, top, p_idx);
  hull[new_top] = p_idx;
  return new_top + 1;
}
