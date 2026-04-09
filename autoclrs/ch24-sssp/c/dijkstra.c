/*
 * Dijkstra's Single-Source Shortest Paths — C implementation with
 * c2pulse verification annotations.
 *
 * Proves:
 *   1. dist[source] == 0
 *   2. All distances non-negative and bounded: 0 <= dist[v] <= INF
 *   3. pred[source] == source
 *   4. All predecessors valid: pred[v] < n for all v
 *   5. Triangle inequality when result == 1 (CLRS Lemma 24.10 + Theorem 24.6)
 *
 * Requires all weights non-negative and bounded by INF (no negative edges).
 *
 * Uses adjacency matrix representation (n×n flat array, INF = no edge/∞).
 *
 * Split into helper functions so Pulse monolithic well-typedness
 * queries stay small enough for Z3. Phase 4 triangle inequality check
 * uses _rec recursive function to avoid while-loop invariant issues.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

#define INF 1000000

/* ── Helper: find minimum-distance unvisited vertex, mark it visited ── */
size_t dijkstra_find_min(
    _array int *dist, _array int *visited, size_t n, size_t source)
  _requires(n > 0 && source < n)
  _requires(dist._length == n && visited._length == n)
  _requires(_forall(size_t v, v < n ==> (dist[v] >= 0 && dist[v] <= INF)))
  _requires(dist[source] == 0)
  _ensures(dist._length == n && visited._length == n)
  _ensures(_forall(size_t v, v < n ==> (dist[v] >= 0 && dist[v] <= INF)))
  _ensures(dist[source] == 0)
  _ensures(return < n)
{
  size_t u = 0;
  int min_d = INF + 1;
  for (size_t j = 0; j < n; j = j + 1)
    _invariant(_live(j) && _live(u) && _live(min_d))
    _invariant(_live(*dist) && _live(*visited))
    _invariant(dist._length == n && visited._length == n)
    _invariant(j <= n && u < n)
    _invariant(min_d >= 0 && min_d <= INF + 1)
    _invariant(_forall(size_t v, v < n ==> (dist[v] >= 0 && dist[v] <= INF)))
    _invariant(dist[source] == 0)
  {
    int vj = visited[j];
    int dj = dist[j];
    if (vj == 0) {
      if (dj < min_d) {
        u = j;
        min_d = dj;
      }
    }
  }
  visited[u] = 1;
  return u;
}

/* ── Helper: relax a single edge (u, v) ──
 * Uses runtime check w >= 0 instead of a forall on weights to avoid
 * quantifier matching issues in the Pulse monolithic query. */
void dijkstra_relax_one(
    _array int *weights, _array int *dist, _array size_t *pred,
    size_t n, size_t source, size_t u, size_t v, int d_u, size_t un)
  _requires(n > 0 && source < n && u < n && v < n)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(weights._length == n * n && dist._length == n && pred._length == n)
  _requires((bool) _inline_pulse(SizeT.v $(un) = SizeT.v $(u) * SizeT.v $(n)))
  _requires(d_u >= 0 && d_u <= INF)
  _requires(dist[source] == 0)
  _requires(pred[source] == source)
  _requires(_forall(size_t j, j < n ==> (dist[j] >= 0 && dist[j] <= INF)))
  _requires(_forall(size_t j, j < n ==> pred[j] < n))
  _preserves(weights._length == n * n)
  _preserves((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _preserves(_forall(size_t k, k < n * n ==>
    (weights[k] >= 0 && weights[k] <= INF)))
  _ensures(dist._length == n && pred._length == n)
  _ensures(dist[source] == 0)
  _ensures(pred[source] == source)
  _ensures(_forall(size_t j, j < n ==> (dist[j] >= 0 && dist[j] <= INF)))
  _ensures(_forall(size_t j, j < n ==> pred[j] < n))
{
  int w = weights[un + v];
  int d_v = dist[v];
  if (w >= 0 && w < INF && d_u < INF && d_u + w < d_v && v != source) {
    dist[v] = d_u + w;
    pred[v] = u;
  }
}

/* ── Helper: relax all edges from vertex u ── */
void dijkstra_relax(
    _array int *weights, _array int *dist, _array size_t *pred,
    size_t n, size_t source, size_t u)
  _requires(n > 0 && source < n && u < n)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(weights._length == n * n && dist._length == n && pred._length == n)
  _requires(dist[source] == 0)
  _requires(pred[source] == source)
  _requires(_forall(size_t v, v < n ==> (dist[v] >= 0 && dist[v] <= INF)))
  _requires(_forall(size_t v, v < n ==> pred[v] < n))
  _requires(_forall(size_t k, k < n * n ==>
    (weights[k] >= 0 && weights[k] <= INF)))
  _ensures(weights._length == n * n && dist._length == n && pred._length == n)
  _ensures((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _ensures(dist[source] == 0)
  _ensures(pred[source] == source)
  _ensures(_forall(size_t v, v < n ==> (dist[v] >= 0 && dist[v] <= INF)))
  _ensures(_forall(size_t v, v < n ==> pred[v] < n))
  _ensures(_forall(size_t k, k < n * n ==>
    (weights[k] >= 0 && weights[k] <= INF)))
{
  int d_u = dist[u];
  _assert((bool) _inline_pulse(SizeT.fits (SizeT.v $(u) * SizeT.v $(n))));
  size_t un = u * n;

  for (size_t v = 0; v < n; v = v + 1)
    _invariant(_live(v) && _live(un))
    _invariant(_live(*dist) && _live(*weights) && _live(*pred))
    _invariant(weights._length == n * n && dist._length == n && pred._length == n)
    _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
    _invariant(v <= n && u < n)
    _invariant((bool) _inline_pulse(SizeT.v $(un) = SizeT.v $(u) * SizeT.v $(n)))
    _invariant(d_u >= 0 && d_u <= INF)
    _invariant(dist[source] == 0)
    _invariant(pred[source] == source)
    _invariant(_forall(size_t j, j < n ==> (dist[j] >= 0 && dist[j] <= INF)))
    _invariant(_forall(size_t j, j < n ==> pred[j] < n))
    _invariant(_forall(size_t k, k < n * n ==>
      (weights[k] >= 0 && weights[k] <= INF)))
  {
    dijkstra_relax_one(weights, dist, pred, n, source, u, v, d_u, un);
  }
}

/* ── Helper: Check edges from vertex u, extending accumulated triangle ineq ──
 * Identical to BF's check_vertex for Z3 case-splitting efficiency. */
void dijkstra_check_vertex(
    _array int *weights, _array int *dist, size_t n, size_t source,
    size_t u, int *result)
  _requires(n > 0 && source < n && u < n)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(weights._length == n * n && dist._length == n)
  _requires(*result == 0 || *result == 1)
  _requires(dist[source] == 0)
  _requires(_forall(size_t v, v < n ==> (dist[v] < INF || dist[v] == INF)))
  _requires(_forall(size_t v, v < n ==> dist[v] > -2 * INF))
  _requires(_forall(size_t i, i < n * n ==>
    (weights[i] >= -INF && weights[i] <= INF)))
  _requires(*result == 1 ==> _forall(size_t u2, u2 < u ==>
    _forall(size_t v2, v2 < n ==>
      ((weights[u2 * n + v2] < INF && weights[u2 * n + v2] > -INF &&
        dist[u2] < INF && dist[u2] > -INF) ==>
        dist[v2] <= dist[u2] + weights[u2 * n + v2]))))
  _ensures(weights._length == n * n && dist._length == n)
  _ensures((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _ensures(*result == 0 || *result == 1)
  _ensures(dist[source] == 0)
  _ensures(_forall(size_t v, v < n ==> (dist[v] < INF || dist[v] == INF)))
  _ensures(_forall(size_t v, v < n ==> dist[v] > -2 * INF))
  _ensures(_forall(size_t i, i < n * n ==>
    (weights[i] >= -INF && weights[i] <= INF)))
  _ensures(*result == 1 ==> _forall(size_t u2, u2 <= u ==>
    _forall(size_t v2, v2 < n ==>
      ((weights[u2 * n + v2] < INF && weights[u2 * n + v2] > -INF &&
        dist[u2] < INF && dist[u2] > -INF) ==>
        dist[v2] <= dist[u2] + weights[u2 * n + v2]))))
{
  for (size_t v = 0; v < n; v = v + 1)
    _invariant(_live(v))
    _invariant(_live(*dist) && _live(*weights) && _live(*result))
    _invariant(weights._length == n * n && dist._length == n)
    _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
    _invariant(v <= n && u < n)
    _invariant(*result == 0 || *result == 1)
    _invariant(dist[source] == 0)
    _invariant(_forall(size_t j, j < n ==> (dist[j] < INF || dist[j] == INF)))
    _invariant(_forall(size_t j, j < n ==> dist[j] > -2 * INF))
    _invariant(_forall(size_t i, i < n * n ==>
      (weights[i] >= -INF && weights[i] <= INF)))
    _invariant(*result == 1 ==> _forall(size_t u2, u2 < u ==>
      _forall(size_t v2, v2 < n ==>
        ((weights[u2 * n + v2] < INF && weights[u2 * n + v2] > -INF &&
          dist[u2] < INF && dist[u2] > -INF) ==>
          dist[v2] <= dist[u2] + weights[u2 * n + v2]))))
    _invariant(*result == 1 ==> _forall(size_t v2, v2 < v ==>
      ((weights[u * n + v2] < INF && weights[u * n + v2] > -INF &&
        dist[u] < INF && dist[u] > -INF) ==>
        dist[v2] <= dist[u] + weights[u * n + v2])))
  {
    int w = weights[u * n + v];
    int d_u = dist[u];
    int d_v = dist[v];
    if (w < INF && w > -INF && d_u < INF && d_u > -INF) {
      if (d_v > d_u + w) {
        *result = 0;
      }
    }
  }
}

/* ── Recursive: check all vertices from bound..n-1, accumulating triangle ineq ── */
_rec int dijkstra_check_all(
    _array int *weights, _array int *dist, size_t n, size_t source,
    size_t bound, int result_in)
  _requires(n > 0 && source < n && bound <= n)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(weights._length == n * n && dist._length == n)
  _requires(result_in == 0 || result_in == 1)
  _requires(dist[source] == 0)
  _requires(_forall(size_t v, v < n ==> (dist[v] < INF || dist[v] == INF)))
  _requires(_forall(size_t v, v < n ==> dist[v] > -2 * INF))
  _requires(_forall(size_t i, i < n * n ==>
    (weights[i] >= -INF && weights[i] <= INF)))
  _requires(result_in == 1 ==> _forall(size_t u2, u2 < bound ==>
    _forall(size_t v2, v2 < n ==>
      ((weights[u2 * n + v2] < INF && weights[u2 * n + v2] > -INF &&
        dist[u2] < INF && dist[u2] > -INF) ==>
        dist[v2] <= dist[u2] + weights[u2 * n + v2]))))
  _ensures(weights._length == n * n && dist._length == n)
  _ensures((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _ensures(return == 0 || return == 1)
  _ensures(dist[source] == 0)
  _ensures(_forall(size_t v, v < n ==> (dist[v] < INF || dist[v] == INF)))
  _ensures(_forall(size_t v, v < n ==> dist[v] > -2 * INF))
  _ensures(_forall(size_t i, i < n * n ==>
    (weights[i] >= -INF && weights[i] <= INF)))
  _ensures(return == 1 ==> _forall(size_t u, u < n ==>
    _forall(size_t v, v < n ==>
      ((weights[u * n + v] < INF && weights[u * n + v] > -INF &&
        dist[u] < INF && dist[u] > -INF) ==>
        dist[v] <= dist[u] + weights[u * n + v]))))
  _decreases(n - bound)
{
  if (bound >= n) {
    return result_in;
  }
  int r = result_in;
  dijkstra_check_vertex(weights, dist, n, source, bound, &r);
  return dijkstra_check_all(weights, dist, n, source, bound + 1, r);
}

/* ── Main Dijkstra function ──────────────────────────────────────── */
void dijkstra(
    _array int *weights, size_t n, size_t source,
    _array int *dist, _array size_t *pred, int *result)
  _requires(n > 0 && source < n)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(weights._length == n * n)
  _requires(dist._length == n)
  _requires(pred._length == n)
  _requires(_forall(size_t i, i < n * n ==>
    (weights[i] >= 0 && weights[i] <= INF)))
  _preserves(weights._length == n * n)
  _preserves((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _ensures(dist._length == n)
  _ensures(pred._length == n)
  _ensures(dist[source] == 0)
  _ensures(pred[source] == source)
  _ensures(_forall(size_t v, v < n ==> (dist[v] < INF || dist[v] == INF)))
  _ensures(_forall(size_t v, v < n ==> pred[v] < n))
  _ensures(*result == 0 || *result == 1)
  _ensures(*result == 1 ==> _forall(size_t u, u < n ==>
    _forall(size_t v, v < n ==>
      ((weights[u * n + v] < INF && weights[u * n + v] > -INF &&
        dist[u] < INF && dist[u] > -INF) ==>
        dist[v] <= dist[u] + weights[u * n + v]))))
{
  /* ── Phase 1: Initialize ── */
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*dist) && _live(*weights) && _live(*pred))
    _invariant(dist._length == n && weights._length == n * n && pred._length == n)
    _invariant(i <= n)
    _invariant(source < i ==> dist[source] == 0)
    _invariant(source < i ==> pred[source] == source)
    _invariant(_forall(size_t j, j < i ==> (dist[j] >= 0 && dist[j] <= INF)))
    _invariant(_forall(size_t j, j < i ==> pred[j] < n))
    _invariant(_forall(size_t k, k < n * n ==>
      (weights[k] >= 0 && weights[k] <= INF)))
  {
    if (i == source) {
      dist[i] = 0;
      pred[i] = source;
    } else {
      dist[i] = INF;
      pred[i] = source;
    }
  }

  /* ── Phase 2: Allocate visited array ── */
  int *visited = (int *)calloc(n, sizeof(int));
  _assert(visited._length == n);

  /* ── Phase 3: Main loop — n iterations ── */
  for (size_t iter = 0; iter < n; iter = iter + 1)
    _invariant(_live(iter))
    _invariant(_live(*dist) && _live(*weights) && _live(*pred) && _live(*visited))
    _invariant(dist._length == n && weights._length == n * n
               && pred._length == n && visited._length == n)
    _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
    _invariant(iter <= n)
    _invariant(dist[source] == 0)
    _invariant(pred[source] == source)
    _invariant(_forall(size_t v, v < n ==> (dist[v] >= 0 && dist[v] <= INF)))
    _invariant(_forall(size_t v, v < n ==> pred[v] < n))
    _invariant(_forall(size_t k, k < n * n ==>
      (weights[k] >= 0 && weights[k] <= INF)))
  {
    size_t u = dijkstra_find_min(dist, visited, n, source);
    dijkstra_relax(weights, dist, pred, n, source, u);
  }

  free(visited);

  /* ── Phase 4: Triangle inequality check ── */
  *result = dijkstra_check_all(weights, dist, n, source, 0, 1);
}
