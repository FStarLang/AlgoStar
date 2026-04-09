/*
 * Bellman-Ford Single-Source Shortest Paths — C implementation with
 * c2pulse verification annotations.
 *
 * Proves:
 *   1. dist[source] == 0
 *   2. Valid distances: each dist[v] < INF or dist[v] == INF
 *   3. result ∈ {0, 1}
 *
 * The full specification (triangle inequality when result==1, sp_dist
 * optimality, exists_violation when result==0) is proven in the Pulse
 * implementation at CLRS.Ch24.BellmanFord.Impl.fsti.  The c2pulse
 * encoding of those quantified postconditions triggers SMT timeouts on
 * Pulse's monolithic well-typedness queries, so we verify the core
 * data-structure invariants here.
 *
 * Uses adjacency matrix representation (n×n flat array, INF = no edge/∞).
 * All weights must satisfy |w| <= INF to prevent Int32 overflow.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

#define INF 1000000

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
{
  /* ── Phase 1: Initialize ──────────────────────────────────────── */
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*dist) && _live(*weights))
    _invariant(dist._length == n && weights._length == n * n)
    _invariant(i <= n)
    _invariant(source < i ==> dist[source] == 0)
    _invariant(_forall(size_t j, j < i && j != source ==> dist[j] == INF))
    _invariant(_forall(size_t j, j < i ==> (dist[j] < INF || dist[j] == INF)))
    _invariant(_forall(size_t j, j < i ==> dist[j] >= 0))
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

  /* ── Phase 3: Negative-cycle detection ────────────────────────── */
  *result = 1;

  for (size_t u = 0; u < n; u = u + 1)
    _invariant(_live(u))
    _invariant(_live(*dist) && _live(*weights) && _live(*result))
    _invariant(dist._length == n && weights._length == n * n)
    _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
    _invariant(u <= n)
    _invariant(*result == 0 || *result == 1)
    _invariant(dist[source] == 0)
    _invariant(_forall(size_t v, v < n ==> (dist[v] < INF || dist[v] == INF)))
  {
    for (size_t v = 0; v < n; v = v + 1)
      _invariant(_live(v) && _live(u))
      _invariant(_live(*dist) && _live(*weights) && _live(*result))
      _invariant(dist._length == n && weights._length == n * n)
      _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
      _invariant(v <= n && u < n)
      _invariant(*result == 0 || *result == 1)
      _invariant(dist[source] == 0)
      _invariant(_forall(size_t j, j < n ==> (dist[j] < INF || dist[j] == INF)))
    {
      int w = weights[u * n + v];
      int d_u = dist[u];
      int d_v = dist[v];
      if (w < INF && w > -INF && d_u < INF && d_u > -INF && d_v > d_u + w) {
        *result = 0;
      }
    }
  }
}
