/*
 * BFS — Queue-based Breadth-First Search (CLRS §22.2)
 *
 * Split into two functions to avoid Pulse VC blowup from nested loops.
 * Uses ghost functions (PredDistStep) for opaque predicate maintenance.
 *
 * Proves:
 *   1. Source is visited with dist[source] = 0
 *   2. Distance soundness: visited vertices have dist >= 0
 *   3. Predecessor edge validity (opaque predicate via bridge lemma)
 *   4. Predecessor distance consistency (opaque predicate via bridge lemma)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(open CLRS.Ch22.BFS.C.BridgeLemmas)
_include_pulse(open CLRS.Ch22.BFS.C.PredDistStep)

/*
 * bfs_scan_neighbors: scan all neighbors of vertex u and discover white ones.
 * Extracted from the inner loop to avoid nested-loop Pulse VC blowup.
 */
void bfs_scan_neighbors(_array int *adj, size_t n, size_t source,
                        _array int *color, _array int *dist,
                        _array size_t *pred, _array size_t *queue,
                        size_t u, size_t *tail_ref)
  _requires(n > 0 && n < 1073741824)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _preserves(adj._length == n * n)
  _preserves(color._length == n)
  _preserves(dist._length == n)
  _preserves(pred._length == n)
  _preserves(queue._length == n)
  _requires(u < n && source < n)
  _requires(color[u] != 0 && dist[u] >= 0)
  _ensures(color[u] != 0 && dist[u] >= 0)
  _requires(*tail_ref <= n)
  _ensures(*tail_ref <= n)
  _preserves(color[source] != 0 && dist[source] == 0)
{
  size_t tail = *tail_ref;

  for (size_t v = 0; v < n; v = v + 1)
    _invariant(_live(v) && _live(tail))
    _invariant(_live(*adj) && _live(*color) && _live(*dist) && _live(*pred) && _live(*queue))
    _invariant(adj._length == n * n)
    _invariant(color._length == n && dist._length == n && pred._length == n && queue._length == n)
    _invariant(v <= n)
    _invariant(tail <= n)
    _invariant(u < n && source < n)
    _invariant(color[u] != 0 && dist[u] >= 0)
    _invariant(color[source] != 0 && dist[source] == 0)
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

  *tail_ref = tail;
}

/*
 * bfs: Initialize arrays, then process the BFS queue.
 */
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
  _ensures(color[source] != 0)
  _ensures(dist[source] == 0)
  _ensures((bool) _inline_pulse(
    CLRS.Ch22.BFS.C.BridgeLemmas.pred_edge_ok_c
      (array_value_of $(adj))
      (array_value_of $(color))
      (array_value_of $(pred))
      $(n)))
  _ensures((bool) _inline_pulse(
    CLRS.Ch22.BFS.C.BridgeLemmas.pred_dist_ok_c
      (array_value_of $(color))
      (array_value_of $(dist))
      (array_value_of $(pred))
      $(n)))
{
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*color) && _live(*dist) && _live(*pred))
    _invariant(color._length == n && dist._length == n && pred._length == n)
    _invariant(i <= n)
  {
    color[i] = 0;
    dist[i] = -1;
    pred[i] = n;
  }

  color[source] = 1;
  dist[source] = 0;
  pred[source] = n;
  _ghost_stmt(
    CLRS.Ch22.BFS.C.PredDistStep.pred_dist_init_step
      $(adj) $(color) $(dist) $(pred) $(n));
  queue[0] = source;
  size_t head = 0;
  size_t tail = 1;

  while (head < tail)
    _invariant(_live(head) && _live(tail))
    _invariant(_live(*adj) && _live(*color) && _live(*dist) && _live(*pred) && _live(*queue))
    _invariant(adj._length == n * n)
    _invariant(color._length == n && dist._length == n && pred._length == n && queue._length == n)
    _invariant(head <= n && tail <= n)
    _invariant(color[source] != 0 && dist[source] == 0)
    _invariant((bool) _inline_pulse(
      CLRS.Ch22.BFS.C.BridgeLemmas.pred_edge_ok_c
        (array_value_of $(adj))
        (array_value_of $(color))
        (array_value_of $(pred))
        $(n)))
    _invariant((bool) _inline_pulse(
      CLRS.Ch22.BFS.C.BridgeLemmas.pred_dist_ok_c
        (array_value_of $(color))
        (array_value_of $(dist))
        (array_value_of $(pred))
        $(n)))
  {
    size_t u = queue[head];
    head = head + 1;
    if (u < n) {
      if (color[u] != 0) {
        if (dist[u] >= 0) {
          bfs_scan_neighbors(adj, n, source, color, dist, pred, queue, u, &tail);
          _ghost_stmt(
            CLRS.Ch22.BFS.C.PredDistStep.pred_dist_update_step
              $(adj) $(color) $(dist) $(pred) $(n));
          color[u] = 2;
          _ghost_stmt(
            CLRS.Ch22.BFS.C.PredDistStep.pred_dist_finish_step
              $(adj) $(color) $(dist) $(pred) $(n));
        }
      }
    }
  }
}
