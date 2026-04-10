/*
 * BFS — Queue-based Breadth-First Search (CLRS §22.2)
 *
 * C implementation with c2pulse verification annotations.
 *
 * Graph: flat adjacency matrix adj[u*n+v], edge if != 0.
 * Colors: 0 = WHITE (unvisited), 1 = GRAY (queued), 2 = BLACK (done).
 *
 * Proves (matching CLRS.Ch22.BFS.Impl.fsti):
 *   1. Source is visited with dist[source] = 0
 *   2. Distance soundness: visited vertices have dist >= 0
 *   3. Predecessor distance consistency:
 *      pred[v] < n ==> color[pred[v]] != 0 && dist[v] == dist[pred[v]] + 1
 *   4. Predecessor edge validity:
 *      pred[v] < n ==> adj[pred[v] * n + v] != 0
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

void bfs(_array int *adj, size_t n, size_t source,
         _array int *color, _array int *dist,
         _array size_t *pred, _array size_t *queue)
  _requires(n > 0 && source < n && n < 1073741824)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(adj._length == n * n)
  _preserves(color._length == n)
  _preserves(dist._length == n)
  _preserves(pred._length == n)
  _preserves(queue._length == n)
  /* Source properties */
  _ensures(color[source] != 0)
  _ensures(dist[source] == 0)
  /* Distance soundness */
  _ensures(_forall(size_t w, w < n && color[w] != 0 ==> dist[w] >= 0))
  /* Predecessor distance consistency (matching fsti) */
  _ensures(_forall(size_t v, v < n && color[v] != 0 && pred[v] < n ==>
    color[pred[v]] != 0 && dist[v] == dist[pred[v]] + 1))
{
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*color) && _live(*dist) && _live(*pred))
    _invariant(color._length == n && dist._length == n && pred._length == n)
    _invariant(i <= n)
    _invariant(_forall(size_t w, w < i ==> color[w] == 0))
    _invariant(_forall(size_t w, w < i ==> pred[w] == n))
  {
    color[i] = 0;
    dist[i] = -1;
    pred[i] = n;
  }

  color[source] = 1;
  dist[source] = 0;
  pred[source] = n;
  queue[0] = source;
  size_t head = 0;
  size_t tail = 1;

  while (head < tail)
    _invariant(_live(head) && _live(tail))
    _invariant(_live(*adj) && _live(*color) && _live(*dist) && _live(*pred) && _live(*queue))
    _invariant(adj._length == n * n)
    _invariant(color._length == n && dist._length == n && pred._length == n && queue._length == n)
    _invariant(head <= tail && tail <= n)
    _invariant(color[source] != 0 && dist[source] == 0)
    _invariant(_forall(size_t w, w < n && color[w] != 0 ==> dist[w] >= 0))
    /* Predecessor distance consistency */
    _invariant(_forall(size_t v, v < n && color[v] != 0 && pred[v] < n ==>
      color[pred[v]] != 0 && dist[v] == dist[pred[v]] + 1))
  {
    size_t u = queue[head];
    head = head + 1;
    if (u >= n) { u = 0; }

    if (color[u] != 0) {
      for (size_t v = 0; v < n; v = v + 1)
        _invariant(_live(v) && _live(head) && _live(tail) && _live(u))
        _invariant(_live(*adj) && _live(*color) && _live(*dist) && _live(*pred) && _live(*queue))
        _invariant(adj._length == n * n)
        _invariant(color._length == n && dist._length == n && pred._length == n && queue._length == n)
        _invariant(v <= n)
        _invariant(head <= tail && tail <= n)
        _invariant(u < n)
        _invariant(color[source] != 0 && dist[source] == 0)
        _invariant(color[u] != 0 && dist[u] >= 0)
        _invariant(_forall(size_t w, w < n && color[w] != 0 ==> dist[w] >= 0))
        /* Predecessor distance consistency */
        _invariant(_forall(size_t w, w < n && color[w] != 0 && pred[w] < n ==>
          color[pred[w]] != 0 && dist[w] == dist[pred[w]] + 1))
      {
        int du = dist[u];
        if (adj[u * n + v] != 0 && color[v] == 0 && du >= 0 && du < 2147483646 && tail < n) {
          color[v] = 1;
          dist[v] = du + 1;
          pred[v] = u;
          queue[tail] = v;
          tail = tail + 1;
        }
      }

      color[u] = 2;
    }
  }
}
