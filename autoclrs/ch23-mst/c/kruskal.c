/*
 * Kruskal's MST Algorithm — C implementation with c2pulse verification.
 *
 * Simplified variant: each round scans the full n×n adjacency matrix for
 * the minimum-weight cross-component edge, then adds it to the forest.
 *
 * Proves:
 *   1. All selected edge endpoints are valid vertices (< n).
 *   2. Edge count < n.
 *   3. Union-find parent values always valid (< n).
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

/* Find root of vertex v in union-find (recursive, bounded by fuel steps). */
_rec size_t uf_find(_array size_t *parent, size_t n, size_t v, size_t fuel)
  _preserves(parent._length == n)
  _requires(n > 0 && v < n && fuel <= n)
  _preserves(_forall(size_t i, i < n ==> parent[i] < n))
  _ensures(return < n)
  _decreases((_specint) fuel)
{
  if (fuel == 0) {
    return v;
  }
  size_t p = parent[v];
  return uf_find(parent, n, p, fuel - 1);
}

/* Pre-compute roots for all vertices into roots[] array.
 * Calls recursive uf_find for each vertex. */
void compute_roots(_array size_t *parent, size_t n, _array size_t *roots)
  _requires(n > 0)
  _preserves(parent._length == n)
  _preserves(_forall(size_t i, i < n ==> parent[i] < n))
  _requires(roots._length == n)
  _ensures(roots._length == n)
  _ensures(_forall(size_t i, i < n ==> roots[i] < n))
{
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*parent) && _live(*roots))
    _invariant(parent._length == n && roots._length == n)
    _invariant(i <= n && n > 0)
    _invariant(_forall(size_t j, j < n ==> parent[j] < n))
    _invariant(_forall(size_t j, j < i ==> roots[j] < n))
  {
    roots[i] = uf_find(parent, n, i, n);
  }
}

/* Scan one row using pre-computed roots (no function calls in loop body).
 * Uses flat index (base = u*n) to avoid SizeT.mul. */
void scan_row(_array int *adj, size_t adj_len,
              _array size_t *roots, size_t n,
              size_t u, size_t base,
              size_t *out_u, size_t *out_v, int *out_w)
  _requires(n > 1 && u < n)
  _requires(adj._length == adj_len && roots._length == n)
  _requires((bool) _inline_pulse(SizeT.v $(adj_len) = SizeT.v $(n) * SizeT.v $(n)))
  _requires((bool) _inline_pulse(SizeT.v $(base) = SizeT.v $(u) * SizeT.v $(n)))
  _requires((bool) _inline_pulse(SizeT.v $(base) + SizeT.v $(n) <= SizeT.v $(adj_len)))
  _preserves(*out_u < n && *out_v < n)
  _preserves(*out_w >= 0)
  _ensures(adj._length == adj_len && roots._length == n)
{
  size_t root_u = roots[u];
  size_t idx = base;
  for (size_t v = 0; v < n; v = v + 1)
    _invariant(_live(v) && _live(idx) && _live(root_u))
    _invariant(_live(*out_u) && _live(*out_v) && _live(*out_w))
    _invariant(_live(*roots) && _live(*adj))
    _invariant(roots._length == n && adj._length == adj_len)
    _invariant((bool) _inline_pulse(SizeT.v $(adj_len) = SizeT.v $(n) * SizeT.v $(n)))
    _invariant((bool) _inline_pulse(SizeT.v $(idx) = SizeT.v $(base) + SizeT.v $(v)))
    _invariant((bool) _inline_pulse(SizeT.v $(base) + SizeT.v $(n) <= SizeT.v $(adj_len)))
    _invariant(v <= n && n > 1 && u < n)
    _invariant(*out_u < n && *out_v < n)
    _invariant(*out_w >= 0)
  {
    int w = adj[idx];
    size_t root_v = roots[v];
    if (w > 0 && root_u != root_v && (*out_w == 0 || w < *out_w)) {
      *out_u = u;
      *out_v = v;
      *out_w = w;
    }
    idx = idx + 1;
  }
}

/* Scan the full adjacency matrix for min-weight cross-component edge.
 * Pre-computes roots, then calls scan_row for each row.
 * Base index is computed incrementally (base += n each iteration). */
void find_min_edge(_array int *adj, size_t adj_len,
                   _array size_t *parent, size_t n,
                   size_t *out_u, size_t *out_v, int *out_w)
  _requires(adj._length == adj_len && parent._length == n)
  _requires(n > 1)
  _requires((bool) _inline_pulse(SizeT.v $(adj_len) = SizeT.v $(n) * SizeT.v $(n)))
  _requires(_forall(size_t i, i < n ==> parent[i] < n))
  _ensures(adj._length == adj_len && parent._length == n)
  _ensures(_forall(size_t i, i < n ==> parent[i] < n))
  _ensures(*out_u < n && *out_v < n)
  _ensures(*out_w >= 0)
{
  *out_u = 0;
  *out_v = 0;
  *out_w = 0;

  size_t *roots = (size_t *)calloc(n, sizeof(size_t));
  _assert(roots._length == n);
  compute_roots(parent, n, roots);

  size_t base = 0;
  for (size_t u = 0; u < n; u = u + 1)
    _invariant(_live(u) && _live(base))
    _invariant(_live(*out_u) && _live(*out_v) && _live(*out_w))
    _invariant(_live(*roots) && _live(*adj) && _live(*parent))
    _invariant(roots._length == n && adj._length == adj_len && parent._length == n)
    _invariant((bool) _inline_pulse(SizeT.v $(adj_len) = SizeT.v $(n) * SizeT.v $(n)))
    _invariant((bool) _inline_pulse(SizeT.v $(base) = SizeT.v $(u) * SizeT.v $(n)))
    _invariant(u <= n && n > 1)
    _invariant(base <= adj_len)
    _invariant(*out_u < n && *out_v < n)
    _invariant(*out_w >= 0)
    _invariant(_forall(size_t i, i < n ==> parent[i] < n))
  {
    _ghost_stmt(NLArith.base_bound (SizeT.v $(u)) (SizeT.v $(n)));
    scan_row(adj, adj_len, roots, n, u, base, out_u, out_v, out_w);
    base = base + n;
  }

  free(roots);
}

/* Insert an edge at position ec in the edge arrays.
 * Isolates the quantifier-extension proof (forall k < ec ==> ... to forall k < ec+1 ==> ...). */
void insert_edge(_array size_t *edge_u, _array size_t *edge_v,
                 size_t n, size_t ec, size_t u, size_t v)
  _requires(ec < n && u < n && v < n)
  _preserves(edge_u._length == n && edge_v._length == n)
  _requires(_forall(size_t k, k < ec ==> edge_u[k] < n))
  _requires(_forall(size_t k, k < ec ==> edge_v[k] < n))
  _ensures(_forall(size_t k, k < ec + 1 ==> edge_u[k] < n))
  _ensures(_forall(size_t k, k < ec + 1 ==> edge_v[k] < n))
{
  edge_u[ec] = u;
  edge_v[ec] = v;
}

/* Try to add one MST edge: find min cross-component edge, union if found.
 * Returns updated edge_count. Postconditions re-establish all kruskal invariants. */
void try_add_edge(_array int *adj, size_t adj_len,
                  _array size_t *parent, size_t n,
                  _array size_t *edge_u, _array size_t *edge_v,
                  size_t *edge_count, size_t round)
  _requires(adj._length == adj_len && parent._length == n)
  _requires(edge_u._length == n && edge_v._length == n)
  _requires(n > 1)
  _requires((bool) _inline_pulse(SizeT.v $(adj_len) = SizeT.v $(n) * SizeT.v $(n)))
  _requires(_forall(size_t i, i < n ==> parent[i] < n))
  _requires(*edge_count <= round && round + 1 < n)
  _requires(_forall(size_t k, k < *edge_count ==> edge_u[k] < n))
  _requires(_forall(size_t k, k < *edge_count ==> edge_v[k] < n))
  _ensures(adj._length == adj_len && parent._length == n)
  _ensures(edge_u._length == n && edge_v._length == n)
  _ensures(_forall(size_t i, i < n ==> parent[i] < n))
  _ensures(*edge_count <= round + 1 && *edge_count < n)
  _ensures(_forall(size_t k, k < *edge_count ==> edge_u[k] < n))
  _ensures(_forall(size_t k, k < *edge_count ==> edge_v[k] < n))
{
  size_t best_u = 0;
  size_t best_v = 0;
  int best_w = 0;
  find_min_edge(adj, adj_len, parent, n, &best_u, &best_v, &best_w);

  size_t root_u = uf_find(parent, n, best_u, n);
  size_t root_v = uf_find(parent, n, best_v, n);
  size_t ec = *edge_count;
  if (best_w > 0 && root_u != root_v) {
    insert_edge(edge_u, edge_v, n, ec, best_u, best_v);
    *edge_count = ec + 1;
    parent[root_u] = root_v;
  }
}

/*
 * Kruskal's algorithm: builds MST by greedy edge selection.
 *
 * Input:
 *   adj[adj_len]  — flat adjacency matrix (adj_len == n*n)
 *   n             — number of vertices (> 0)
 *
 * Output:
 *   edge_u[n], edge_v[n] — endpoint arrays for selected edges
 *   *edge_count          — number of edges selected
 */
void kruskal(_array int *adj, size_t adj_len, size_t n,
             _array size_t *edge_u, _array size_t *edge_v,
             size_t *edge_count)
  _requires(adj._length == adj_len && n > 0)
  _requires((bool) _inline_pulse(SizeT.v $(adj_len) = SizeT.v $(n) * SizeT.v $(n)))
  _requires(edge_u._length == n && edge_v._length == n)
  _requires(*edge_count == 0)
  _ensures(adj._length == adj_len)
  _ensures(edge_u._length == n && edge_v._length == n)
  _ensures(*edge_count < n)
  _ensures(_forall(size_t k, k < *edge_count ==> edge_u[k] < n))
  _ensures(_forall(size_t k, k < *edge_count ==> edge_v[k] < n))
{
  if (n <= 1) return;

  size_t *parent = (size_t *)calloc(n, sizeof(size_t));
  _assert(parent._length == n);

  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*parent))
    _invariant(parent._length == n)
    _invariant(i <= n && n > 1)
    _invariant(_forall(size_t j, j < i ==> parent[j] == j))
    _invariant(_forall(size_t j, j < i ==> parent[j] < n))
  {
    parent[i] = i;
  }

  size_t max_rounds = n - 1;
  for (size_t round = 0; round < max_rounds; round = round + 1)
    _invariant(_live(round) && _live(max_rounds))
    _invariant(_live(*parent) && _live(*adj))
    _invariant(_live(*edge_u) && _live(*edge_v) && _live(*edge_count))
    _invariant(parent._length == n && adj._length == adj_len)
    _invariant(edge_u._length == n && edge_v._length == n)
    _invariant(round <= max_rounds)
    _invariant((bool) _inline_pulse(SizeT.v $(max_rounds) + 1 = SizeT.v $(n)))
    _invariant((bool) _inline_pulse(SizeT.v $(adj_len) = SizeT.v $(n) * SizeT.v $(n)))
    _invariant(n > 1)
    _invariant(*edge_count <= round)
    _invariant(*edge_count < n)
    _invariant(_forall(size_t i, i < n ==> parent[i] < n))
    _invariant(_forall(size_t k, k < *edge_count ==> edge_u[k] < n))
    _invariant(_forall(size_t k, k < *edge_count ==> edge_v[k] < n))
  {
    try_add_edge(adj, adj_len, parent, n, edge_u, edge_v, edge_count, round);
  }

  free(parent);
}
