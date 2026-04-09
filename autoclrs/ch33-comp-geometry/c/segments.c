/*
 * Computational Geometry Primitives — CLRS Chapter 33, Section 33.1
 *
 * C implementation with c2pulse verification.
 *
 * Proves:
 *   1. cross_product computes (x2-x1)*(y3-y1) - (x3-x1)*(y2-y1)
 *   2. direction equals cross_product
 *   3. on_segment checks bounding-box containment
 *   4. segments_intersect implements the CLRS orientation-based test
 *
 * Coordinates are bounded to [-16383, 16383] to ensure all Int32
 * intermediate computations (differences, products, cross products)
 * stay within the 32-bit range.
 *
 * Equivalent to the specifications in CLRS.Ch33.Segments.Impl.fsti.
 */

#include "c2pulse.h"
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

_include_pulse(
  open CLRS.Ch33.Segments.Spec
  open FStar.Mul
)

/* Cross product (p2-p1) × (p3-p1).
 *   > 0 if p3 is to the left of line p1→p2 (CCW)
 *   < 0 if p3 is to the right (CW)
 *   = 0 if collinear
 */
int cross_product(int x1, int y1, int x2, int y2, int x3, int y3)
  _requires(x1 > -16384 && x1 < 16384 && y1 > -16384 && y1 < 16384)
  _requires(x2 > -16384 && x2 < 16384 && y2 > -16384 && y2 < 16384)
  _requires(x3 > -16384 && x3 < 16384 && y3 > -16384 && y3 < 16384)
  _ensures(return == (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1))
  _ensures((_specint) return == ((_specint) x2 - (_specint) x1) * ((_specint) y3 - (_specint) y1) - ((_specint) x3 - (_specint) x1) * ((_specint) y2 - (_specint) y1))
{
  int dx21 = x2 - x1;
  int dy31 = y3 - y1;
  int dx31 = x3 - x1;
  int dy21 = y2 - y1;
  int term1 = dx21 * dy31;
  int term2 = dx31 * dy21;
  return term1 - term2;
}

/* Direction from p1 through p2 to p3 (equals cross product). */
int direction(int x1, int y1, int x2, int y2, int x3, int y3)
  _requires(x1 > -16384 && x1 < 16384 && y1 > -16384 && y1 < 16384)
  _requires(x2 > -16384 && x2 < 16384 && y2 > -16384 && y2 < 16384)
  _requires(x3 > -16384 && x3 < 16384 && y3 > -16384 && y3 < 16384)
  _ensures(return == (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1))
{
  return cross_product(x1, y1, x2, y2, x3, y3);
}

/* Check if point (x,y) lies on the axis-aligned bounding box of
 * segment (x1,y1)-(x2,y2). Assumes the three points are collinear.
 */
bool on_segment(int x1, int y1, int x2, int y2, int x, int y)
  _ensures(return == ((x <= x1 || x <= x2) && (x >= x1 || x >= x2) &&
                      (y <= y1 || y <= y2) && (y >= y1 || y >= y2)))
{
  int max_x = (x1 >= x2) ? x1 : x2;
  int min_x = (x1 <= x2) ? x1 : x2;
  int max_y = (y1 >= y2) ? y1 : y2;
  int min_y = (y1 <= y2) ? y1 : y2;

  return (x <= max_x && x >= min_x && y <= max_y && y >= min_y);
}

/* Check if segments (p1,p2) and (p3,p4) intersect.
 * Uses the standard orientation-based algorithm from CLRS.
 */
bool segments_intersect(int x1, int y1, int x2, int y2,
                        int x3, int y3, int x4, int y4)
  _requires(x1 > -16384 && x1 < 16384 && y1 > -16384 && y1 < 16384)
  _requires(x2 > -16384 && x2 < 16384 && y2 > -16384 && y2 < 16384)
  _requires(x3 > -16384 && x3 < 16384 && y3 > -16384 && y3 < 16384)
  _requires(x4 > -16384 && x4 < 16384 && y4 > -16384 && y4 < 16384)
  _ensures((bool) _inline_pulse($(return) == segments_intersect_spec (Int32.v $(x1)) (Int32.v $(y1)) (Int32.v $(x2)) (Int32.v $(y2)) (Int32.v $(x3)) (Int32.v $(y3)) (Int32.v $(x4)) (Int32.v $(y4))))
{
  int d1 = cross_product(x3, y3, x4, y4, x1, y1);
  int d2 = cross_product(x3, y3, x4, y4, x2, y2);
  int d3 = cross_product(x1, y1, x2, y2, x3, y3);
  int d4 = cross_product(x1, y1, x2, y2, x4, y4);

  /* General case: segments straddle each other */
  if (((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) &&
      ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0)))
    return true;

  /* Special cases: collinear endpoints */
  if (d1 == 0 && on_segment(x3, y3, x4, y4, x1, y1)) return true;
  if (d2 == 0 && on_segment(x3, y3, x4, y4, x2, y2)) return true;
  if (d3 == 0 && on_segment(x1, y1, x2, y2, x3, y3)) return true;
  if (d4 == 0 && on_segment(x1, y1, x2, y2, x4, y4)) return true;

  return false;
}
