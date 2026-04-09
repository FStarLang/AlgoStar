/*
 * Bellman-Ford Single-Source Shortest Paths — C implementation with
 * c2pulse verification annotations.
 *
 * Proves:
 *   1. dist[source] == 0
 *   2. Valid distances: each dist[v] < INF or dist[v] == INF
 *   3. result ∈ {0, 1}
 *   4. Triangle inequality when result == 1 (CLRS Corollary 24.2)
 *
 * Split: Phase 1+2 in bellman_ford_relax; Phase 3 in bellman_ford with
 * bellman_ford_check_vertex helper. check_vertex takes the accumulated
 * outer-loop invariant as precondition and extends it by one vertex,
 * avoiding the separation-logic framing issue.
 *
 * Uses adjacency matrix representation (n×n flat array, INF = no edge/∞).
 * All weights must satisfy |w| <= INF to prevent Int32 overflow.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

#define INF 1000000

/* ── Helper: Phase 1 (init) + Phase 2 (relaxation) ── */
void bellman_ford_relax(
    _array int *weights, size_t n, size_t source,
    _array int *dist)
  _requires(n > 0 && source < n)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(weights._length == n * n)
  _requires(dist._length == n)
  _requires(_forall(size_t i, i < n * n ==>
    (weights[i] >= -INF && weights[i] <= INF)))
  _preserves(weights._length == n * n)
  _preserves((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _preserves(_forall(size_t i, i < n * n ==>
    (weights[i] >= -INF && weights[i] <= INF)))
  _ensures(dist._length == n)
  _ensures(dist[source] == 0)
  _ensures(_forall(size_t v, v < n ==> (dist[v] < INF || dist[v] == INF)))
  _ensures(_forall(size_t v, v < n ==> dist[v] > -2 * INF))
{
  /* ── Phase 1: Initialize ──────────────────────────────────────── */
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*dist) && _live(*weights))
    _invariant(dist._length == n && weights._length == n * n)
    _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
    _invariant(i <= n)
    _invariant(source < i ==> dist[source] == 0)
    _invariant(_forall(size_t j, j < i && j != source ==> dist[j] == INF))
    _invariant(_forall(size_t j, j < i ==> (dist[j] < INF || dist[j] == INF)))
    _invariant(_forall(size_t j, j < i ==> dist[j] >= 0))
    _invariant(_forall(size_t k, k < n * n ==>
      (weights[k] >= -INF && weights[k] <= INF)))
  {
    if (i == source) {
      dist[i] = 0;
    } else {
      dist[i] = INF;
    }
  }

  /* ── Phase 2: Relaxation — (n-1) rounds ───────────────────────── */
  for (size_t round = 1; round < n; round = round + 1)
    _invariant(_live(round))
    _invariant(_live(*dist) && _live(*weights))
    _invariant(dist._length == n && weights._length == n * n)
    _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
    _invariant(round >= 1 && round <= n)
    _invariant(dist[source] == 0)
    _invariant(_forall(size_t v, v < n ==> (dist[v] < INF || dist[v] == INF)))
    _invariant(_forall(size_t v, v < n ==> dist[v] > -2 * INF))
    _invariant(_forall(size_t k, k < n * n ==>
      (weights[k] >= -INF && weights[k] <= INF)))
  {
    for (size_t u = 0; u < n; u = u + 1)
      _invariant(_live(u) && _live(round))
      _invariant(_live(*dist) && _live(*weights))
      _invariant(dist._length == n && weights._length == n * n)
      _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
      _invariant(u <= n && round < n)
      _invariant(dist[source] == 0)
      _invariant(_forall(size_t v, v < n ==> (dist[v] < INF || dist[v] == INF)))
      _invariant(_forall(size_t v, v < n ==> dist[v] > -2 * INF))
      _invariant(_forall(size_t k, k < n * n ==>
        (weights[k] >= -INF && weights[k] <= INF)))
    {
      int d_u = dist[u];

      for (size_t v = 0; v < n; v = v + 1)
        _invariant(_live(v) && _live(u) && _live(round))
        _invariant(_live(*dist) && _live(*weights))
        _invariant(dist._length == n && weights._length == n * n)
        _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
        _invariant(v <= n && u < n && round < n)
        _invariant(dist[source] == 0)
        _invariant(_forall(size_t j, j < n ==> (dist[j] < INF || dist[j] == INF)))
        _invariant(_forall(size_t j, j < n ==> dist[j] > -2 * INF))
        _invariant(_forall(size_t k, k < n * n ==>
          (weights[k] >= -INF && weights[k] <= INF)))
      {
        int w = weights[u * n + v];
        int d_v = dist[v];
        if (w < INF && w > -INF && d_u < INF && d_u > -INF
            && d_u + w < d_v && v != source) {
          dist[v] = d_u + w;
        }
      }
    }
  }
}

/* ── Helper: Check edges from vertex u, extending accumulated invariant ── */
void bellman_ford_check_vertex(
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
_rec int bellman_ford_check_all(
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
  bellman_ford_check_vertex(weights, dist, n, source, bound, &r);
  return bellman_ford_check_all(weights, dist, n, source, bound + 1, r);
}

/* ── Main Bellman-Ford function ──────────────────────────────────── */
void bellman_ford(
    _array int *weights, size_t n, size_t source,
    _array int *dist, int *result)
  _requires(n > 0 && source < n)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(weights._length == n * n)
  _requires(dist._length == n)
  _requires(_forall(size_t i, i < n * n ==>
    (weights[i] >= -INF && weights[i] <= INF)))
  _preserves(weights._length == n * n)
  _ensures(dist._length == n)
  _ensures(dist[source] == 0)
  _ensures(_forall(size_t v, v < n ==> (dist[v] < INF || dist[v] == INF)))
  _ensures(*result == 0 || *result == 1)
  _ensures(*result == 1 ==> _forall(size_t u, u < n ==>
    _forall(size_t v, v < n ==>
      ((weights[u * n + v] < INF && weights[u * n + v] > -INF &&
        dist[u] < INF && dist[u] > -INF) ==>
        dist[v] <= dist[u] + weights[u * n + v]))))
{
  bellman_ford_relax(weights, n, source, dist);
  *result = bellman_ford_check_all(weights, dist, n, source, 0, 1);
}
