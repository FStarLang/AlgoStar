/*
 * DFS — Stack-based Depth-First Search (CLRS §22.3)
 *
 * C implementation with c2pulse verification annotations.
 *
 * Graph: flat adjacency matrix adj[u*n+v], edge if != 0.
 * Colors: 0 = WHITE, 1 = GRAY (on stack), 2 = BLACK (finished).
 *
 * Single flat while loop — no nested loops.
 * Timestamps and predecessors computed alongside coloring.
 *
 * Proves:
 *   1. All vertices end up BLACK (color[u] == 2)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

void dfs(_array int *adj, size_t n,
         _array int *color, _array int *d, _array int *f,
         _array size_t *pred,
         _array size_t *stack_data, _array size_t *scan_idx)
  _requires(n > 0 && n < 32768)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(adj._length == n * n)
  _preserves(color._length == n)
  _preserves(d._length == n)
  _preserves(f._length == n)
  _preserves(pred._length == n)
  _preserves(stack_data._length == n)
  _preserves(scan_idx._length == n)
  _ensures(_forall(size_t u, u < n ==> color[u] != 0))
{
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*color) && _live(*d) && _live(*f) && _live(*pred) && _live(*scan_idx))
    _invariant(color._length == n && d._length == n && f._length == n)
    _invariant(pred._length == n && scan_idx._length == n)
    _invariant(i <= n)
  {
    color[i] = 0;
    d[i] = 0;
    f[i] = 0;
    pred[i] = n;
    scan_idx[i] = 0;
  }

  int time = 0;
  size_t top = 0;
  size_t next_src = 0;

  /* Main DFS loop */
  while (next_src < n || top > 0)
    _invariant(_live(top) && _live(next_src) && _live(time))
    _invariant(_live(*adj) && _live(*color) && _live(*d) && _live(*f))
    _invariant(_live(*pred) && _live(*stack_data) && _live(*scan_idx))
    _invariant(adj._length == n * n)
    _invariant(color._length == n && d._length == n && f._length == n)
    _invariant(pred._length == n && stack_data._length == n && scan_idx._length == n)
    _invariant(top <= n)
    _invariant(next_src <= n)
    _invariant(time >= 0 && time <= 65534)
    _invariant(_forall(size_t j, j < next_src ==> color[j] != 0))
  {
    if (top == 0 && next_src < n) {
      if (color[next_src] != 0) {
        /* Already discovered/finished, skip */
        next_src = next_src + 1;
      } else {
        /* Discover new source */
        if (time < 65534) {
          time = time + 1;
          color[next_src] = 1;
          d[next_src] = time;
          pred[next_src] = n;
          scan_idx[next_src] = 0;
          stack_data[0] = next_src;
          top = 1;
          next_src = next_src + 1;
        }
      }
    } else {
      if (top > 0) {
        size_t u_idx = top - 1;
        size_t u = stack_data[u_idx];
        if (u >= n) { u = 0; }
        size_t scan = scan_idx[u];
        if (scan >= n) { scan = n; }

        if (scan < n) {
          scan_idx[u] = scan + 1;
          if (adj[u * n + scan] != 0 && color[scan] == 0 && top < n && time < 65534) {
            time = time + 1;
            color[scan] = 1;
            d[scan] = time;
            pred[scan] = u;
            scan_idx[scan] = 0;
            stack_data[top] = scan;
            top = top + 1;
          }
        } else {
          if (time < 65534) {
            time = time + 1;
            f[u] = time;
          }
          color[u] = 2;
          top = top - 1;
        }
      }
    }
  }
}
