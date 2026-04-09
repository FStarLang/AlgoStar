/*
 * Topological Sort — Kahn's Algorithm (CLRS §22.4)
 *
 * C implementation with c2pulse verification annotations.
 *
 * Graph: flat adjacency matrix adj[u*n+v], edge if != 0.
 * Uses Kahn's algorithm: repeatedly remove vertices with in-degree 0.
 *
 * Structure: multiple flat loops (no nesting) to avoid Pulse timeouts.
 * Phase 1: zero indeg
 * Phase 2: compute in-degrees (flat two-counter traversal)
 * Phase 3: init output to 0
 * Phase 4: enqueue zero-indeg vertices
 * Phase 5: single flat while loop for Kahn's processing
 *          - alternates between dequeue and neighbor scanning
 *
 * Proves:
 *   Structural safety — no buffer overflows, no arithmetic overflow.
 *   out_count <= n (bounded output)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

void topological_sort(_array int *adj, size_t n,
                      _array int *indeg, _array size_t *queue,
                      _array size_t *output)
  _requires(n > 0 && n < 32768)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(adj._length == n * n)
  _preserves(indeg._length == n)
  _preserves(queue._length == n)
  _preserves(output._length == n)
{
  /* Phase 1: zero indeg */
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*indeg))
    _invariant(indeg._length == n)
    _invariant(i <= n)
  {
    indeg[i] = 0;
  }

  /* Phase 2: compute in-degrees — flat two-counter loop */
  size_t cu = 0;
  size_t cv = 0;
  while (cu < n)
    _invariant(_live(cu) && _live(cv))
    _invariant(_live(*adj) && _live(*indeg))
    _invariant(adj._length == n * n && indeg._length == n)
    _invariant(cu <= n && cv <= n)
  {
    if (cv < n) {
      size_t idx = cu * n + cv;
      int e = adj[idx];
      int deg = indeg[cv];
      if (e != 0 && deg < 2147483646) {
        indeg[cv] = deg + 1;
      }
      cv = cv + 1;
    } else {
      cv = 0;
      cu = cu + 1;
    }
  }

  /* Phase 3: init output */
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*output))
    _invariant(output._length == n)
    _invariant(i <= n)
  {
    output[i] = 0;
  }

  /* Phase 4: enqueue zero-indeg vertices */
  size_t head = 0;
  size_t tail = 0;
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i) && _live(head) && _live(tail))
    _invariant(_live(*indeg) && _live(*queue))
    _invariant(indeg._length == n && queue._length == n)
    _invariant(i <= n)
    _invariant(head == 0 && tail <= n)
  {
    if (indeg[i] == 0 && tail < n) {
      queue[tail] = i;
      tail = tail + 1;
    }
  }

  /* Phase 5: main Kahn loop — while (dequeue) → for (scan neighbors) */
  size_t out_count = 0;

  while (head < tail)
    _invariant(_live(head) && _live(tail) && _live(out_count))
    _invariant(_live(*adj) && _live(*indeg) && _live(*queue) && _live(*output))
    _invariant(adj._length == n * n && indeg._length == n)
    _invariant(queue._length == n && output._length == n)
    _invariant(head <= tail && tail <= n)
    _invariant(out_count <= n)
  {
    size_t u = queue[head];
    if (u >= n) { u = 0; }
    head = head + 1;

    /* Record u in output */
    if (out_count < n) {
      output[out_count] = u;
      out_count = out_count + 1;
    }

    /* Scan all of u's neighbors — output is framed (not _live here) */
    for (size_t v = 0; v < n; v = v + 1)
      _invariant(_live(v) && _live(head) && _live(tail) && _live(out_count) && _live(u))
      _invariant(_live(*adj) && _live(*indeg) && _live(*queue))
      _invariant(adj._length == n * n && indeg._length == n)
      _invariant(queue._length == n)
      _invariant(v <= n && u < n)
      _invariant(head <= tail && tail <= n)
      _invariant(out_count <= n)
    {
      if (adj[u * n + v] != 0 && indeg[v] > 0) {
        if (indeg[v] == 1 && tail < n) {
          queue[tail] = v;
          tail = tail + 1;
        }
        indeg[v] = indeg[v] - 1;
      }
    }
  }
}
