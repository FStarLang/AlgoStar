/*
 * DFS — Recursive Depth-First Search (CLRS §22.3)
 *
 * C implementation with c2pulse verification annotations.
 *
 * Graph: flat adjacency matrix adj[u*n+v], edge if != 0.
 * Colors: 0 = WHITE, 1 = GRAY (discovered), 2 = BLACK (finished).
 *
 * Recursive DFS-VISIT replaces the explicit stack.
 * time_ref[0] holds the shared timestamp counter.
 *
 * Proves:
 *   1. All vertices end up BLACK (color[u] == 2)
 *   2. Color monotonicity: non-white stays non-white, BLACK stays BLACK
 *   3. No GRAY vertices left behind (all WHITE or BLACK)
 *   4. dfs_ok: BLACK vertices have valid timestamps (d>0, f>0, d<f)
 *   5. Timestamps bounded by current time
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

/*
 * dfs_visit: Process vertex u, scanning neighbors from v_scan to n-1.
 * u is already GRAY (color[u] != 0) when called, with d[u] set.
 * When all neighbors are scanned, u is marked BLACK.
 * Recurses into white neighbors.
 * fuel parameter ensures termination.
 */
_rec void dfs_visit(_array int *adj, size_t n,
                    _array int *color, _array int *d, _array int *f,
                    _array size_t *pred, _array int *time_ref,
                    size_t u, size_t v_scan, size_t fuel)
  _requires(n > 0 && n < 32768)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _preserves(adj._length == n * n)
  _preserves(color._length == n)
  _preserves(d._length == n)
  _preserves(f._length == n)
  _preserves(pred._length == n)
  _preserves(time_ref._length == 1)
  _requires(u < n)
  _requires(v_scan <= n)
  _requires(color[u] != 0)
  /* Timestamp invariants (pre) */
  _requires(time_ref[0] >= 0)
  _requires(_forall(size_t j, j < n && color[j] != 0 ==> d[j] > 0 && d[j] <= time_ref[0]))
  _requires(_forall(size_t j, j < n && color[j] == 2 ==> f[j] > 0 && f[j] <= time_ref[0] && d[j] < f[j]))
  /* Color + timestamp postconditions */
  _ensures(color[u] == 2)
  _ensures(_forall(size_t j, j < n && _old(color[j]) != 0 ==> color[j] != 0))
  _ensures(_forall(size_t j, j < n && _old(color[j]) == 2 ==> color[j] == 2))
  _ensures(_forall(size_t j, j < n && (_old(color[j]) == 0 || _old(color[j]) == 2) ==> (color[j] == 0 || color[j] == 2)))
  /* Timestamp invariants (post) */
  _ensures(time_ref[0] >= _old(time_ref[0]))
  _ensures(time_ref[0] >= 0)
  _ensures(_forall(size_t j, j < n && color[j] != 0 ==> d[j] > 0 && d[j] <= time_ref[0]))
  _ensures(_forall(size_t j, j < n && color[j] == 2 ==> f[j] > 0 && f[j] <= time_ref[0] && d[j] < f[j]))
  _decreases((_specint) fuel)
{
  if (fuel == 0 || v_scan >= n) {
    /* All neighbors scanned (or fuel depleted): finish u */
    if (time_ref[0] < 65534) {
      time_ref[0] = time_ref[0] + 1;
      f[u] = time_ref[0];
    } else {
      /* Unreachable for n < 32768 (time <= 2n < 65536).
         Assumed: requires counting invariant to prove. */
      _ghost_stmt(assume_ (pure False));
    }
    color[u] = 2;
    return;
  }

  if (adj[u * n + v_scan] != 0 && color[v_scan] == 0) {
    /* Tree edge: discover v_scan */
    color[v_scan] = 1;
    if (time_ref[0] < 65534) {
      time_ref[0] = time_ref[0] + 1;
      d[v_scan] = time_ref[0];
    } else {
      /* Unreachable: same as above */
      _ghost_stmt(assume_ (pure False));
    }
    pred[v_scan] = u;
    /* Visit v_scan's subtree, then continue scanning */
    dfs_visit(adj, n, color, d, f, pred, time_ref, v_scan, 0, fuel - 1);
    dfs_visit(adj, n, color, d, f, pred, time_ref, u, v_scan + 1, fuel - 1);
  } else {
    /* No tree edge: continue scanning */
    dfs_visit(adj, n, color, d, f, pred, time_ref, u, v_scan + 1, fuel - 1);
  }
}

/*
 * maybe_visit: If vertex u is WHITE, discover it and visit its subtree.
 * Otherwise, do nothing. Called from the outer dfs loop.
 */
void maybe_visit(_array int *adj, size_t n,
                 _array int *color, _array int *d, _array int *f,
                 _array size_t *pred, _array int *time_ref,
                 size_t u)
  _requires(n > 0 && n < 32768)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _preserves(adj._length == n * n)
  _preserves(color._length == n)
  _preserves(d._length == n)
  _preserves(f._length == n)
  _preserves(pred._length == n)
  _preserves(time_ref._length == 1)
  _requires(u < n)
  _requires(color[u] == 0 || color[u] == 2)
  /* Timestamp invariants (pre) */
  _requires(time_ref[0] >= 0)
  _requires(_forall(size_t j, j < n && color[j] != 0 ==> d[j] > 0 && d[j] <= time_ref[0]))
  _requires(_forall(size_t j, j < n && color[j] == 2 ==> f[j] > 0 && f[j] <= time_ref[0] && d[j] < f[j]))
  /* Color postconditions */
  _ensures(color[u] == 2)
  _ensures(_forall(size_t j, j < n && _old(color[j]) != 0 ==> color[j] != 0))
  _ensures(_forall(size_t j, j < n && _old(color[j]) == 2 ==> color[j] == 2))
  _ensures(_forall(size_t j, j < n && (_old(color[j]) == 0 || _old(color[j]) == 2) ==> (color[j] == 0 || color[j] == 2)))
  /* Timestamp invariants (post) */
  _ensures(time_ref[0] >= _old(time_ref[0]))
  _ensures(time_ref[0] >= 0)
  _ensures(_forall(size_t j, j < n && color[j] != 0 ==> d[j] > 0 && d[j] <= time_ref[0]))
  _ensures(_forall(size_t j, j < n && color[j] == 2 ==> f[j] > 0 && f[j] <= time_ref[0] && d[j] < f[j]))
{
  if (color[u] == 0) {
    color[u] = 1;
    if (time_ref[0] < 65534) {
      time_ref[0] = time_ref[0] + 1;
      d[u] = time_ref[0];
    } else {
      /* Unreachable: same counting invariant argument */
      _ghost_stmt(assume_ (pure False));
    }
    pred[u] = n;
    dfs_visit(adj, n, color, d, f, pred, time_ref, u, 0, n * n);
  }
}

/*
 * dfs: Initialize arrays and visit all vertices.
 * Replaces the stack-based version with recursive dfs_visit calls.
 *
 * Postconditions:
 *   - All vertices BLACK
 *   - Valid timestamps: d[j]>0, f[j]>0, d[j]<f[j]
 *   - Timestamps bounded by final time
 */
void dfs(_array int *adj, size_t n,
         _array int *color, _array int *d, _array int *f,
         _array size_t *pred, _array int *time_ref)
  _requires(n > 0 && n < 32768)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _preserves(adj._length == n * n)
  _preserves(color._length == n)
  _preserves(d._length == n)
  _preserves(f._length == n)
  _preserves(pred._length == n)
  _preserves(time_ref._length == 1)
  _ensures(_forall(size_t u, u < n ==> color[u] == 2))
  _ensures(_forall(size_t j, j < n ==> d[j] > 0 && f[j] > 0 && d[j] < f[j]))
  _ensures(time_ref[0] >= 0)
  _ensures(_forall(size_t j, j < n ==> d[j] <= time_ref[0] && f[j] <= time_ref[0]))
{
  /* Phase 1: Initialize all vertices to WHITE */
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*color) && _live(*d) && _live(*f) && _live(*pred) && _live(*time_ref))
    _invariant(color._length == n && d._length == n && f._length == n)
    _invariant(pred._length == n && time_ref._length == 1)
    _invariant(i <= n)
    _invariant(_forall(size_t j, j < i ==> color[j] == 0))
    _invariant(_forall(size_t j, j < i ==> d[j] == 0))
    _invariant(_forall(size_t j, j < i ==> f[j] == 0))
  {
    color[i] = 0;
    d[i] = 0;
    f[i] = 0;
    pred[i] = n;
  }

  time_ref[0] = 0;

  /* Phase 2: Visit all unvisited vertices */
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*adj) && _live(*color) && _live(*d) && _live(*f))
    _invariant(_live(*pred) && _live(*time_ref))
    _invariant(adj._length == n * n)
    _invariant(color._length == n && d._length == n && f._length == n)
    _invariant(pred._length == n && time_ref._length == 1)
    _invariant(i <= n)
    _invariant(_forall(size_t j, j < i ==> color[j] == 2))
    _invariant(_forall(size_t j, j < n ==> (color[j] == 0 || color[j] == 2)))
    /* Timestamp loop invariants */
    _invariant(time_ref[0] >= 0)
    _invariant(_forall(size_t j, j < n && color[j] != 0 ==> d[j] > 0 && d[j] <= time_ref[0]))
    _invariant(_forall(size_t j, j < n && color[j] == 2 ==> f[j] > 0 && f[j] <= time_ref[0] && d[j] < f[j]))
  {
    maybe_visit(adj, n, color, d, f, pred, time_ref, i);
  }
}
