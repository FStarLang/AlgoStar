/*
 * Prim's MST Algorithm — C implementation with c2pulse verification.
 *
 * Uses adjacency matrix representation with linear-scan extract-min.
 *
 * Proves (matching CLRS.Ch23.Prim.Impl.fsti prim_correct):
 *   1. key[source] == 0
 *   2. All keys bounded by INFINITY  (all_keys_bounded)
 *   3. parent[source] == source
 *   4. All parent values < n          (parent_valid)
 *
 * Note: property 5 (key_parent_consistent) requires a forall with
 * multi-array reads inside _inline_pulse loop invariants, which
 * triggers a c2pulse code generation limitation (quantified variables
 * are incorrectly threaded through exists* bindings).
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

#define INFINITY_VAL ((size_t)65535)

/* Extract vertex with minimum key among non-MST vertices. */
size_t extract_min(_array size_t *key_out, _array size_t *in_mst, size_t n)
  _requires(n > 0)
  _preserves(key_out._length == n && in_mst._length == n)
  _preserves(_forall(size_t v, v < n ==> key_out[v] <= INFINITY_VAL))
  _ensures(return < n)
{
  size_t u = 0;
  size_t min_key = INFINITY_VAL;

  for (size_t j = 0; j < n; j = j + 1)
    _invariant(_live(j) && _live(u) && _live(min_key))
    _invariant(_live(*key_out) && _live(*in_mst))
    _invariant(key_out._length == n && in_mst._length == n)
    _invariant(j <= n && n > 0)
    _invariant(u < n)
    _invariant(min_key <= INFINITY_VAL)
    _invariant(_forall(size_t v, v < n ==> key_out[v] <= INFINITY_VAL))
  {
    if (in_mst[j] == 0 && key_out[j] <= min_key) {
      min_key = key_out[j];
      u = j;
    }
  }
  return u;
}

/* Compute base = u * n by iterating (avoids SizeT.mul).
 * Extracted so ghost_stmt is in a non-nested loop body. */
size_t compute_base(size_t u, size_t n, size_t weights_len)
  _requires(u < n && n > 0)
  _requires((bool) _inline_pulse(SizeT.v $(weights_len) = SizeT.v $(n) * SizeT.v $(n)))
  _ensures((bool) _inline_pulse(SizeT.v $(return) = SizeT.v $(u) * SizeT.v $(n)))
  _ensures(return <= weights_len)
{
  size_t base = 0;
  for (size_t k = 0; k < u; k = k + 1)
    _invariant(_live(k) && _live(base))
    _invariant((bool) _inline_pulse(SizeT.v $(base) = SizeT.v $(k) * SizeT.v $(n)))
    _invariant((bool) _inline_pulse(SizeT.v $(weights_len) = SizeT.v $(n) * SizeT.v $(n)))
    _invariant(k <= u && u < n && n > 0)
    _invariant(base <= weights_len)
  {
    _ghost_stmt(NLArith.base_bound (SizeT.v $(k)) (SizeT.v $(n)));
    base = base + n;
  }
  return base;
}

/* Update keys of non-MST neighbors of vertex u.
 * Uses flat index (base = u*n) to avoid SizeT.mul. */
void update_keys(_array size_t *weights, size_t weights_len,
                 _array size_t *key_out, _array size_t *parent_out,
                 _array size_t *in_mst, size_t n, size_t u, size_t base)
  _requires(n > 0 && u < n)
  _requires(weights._length == weights_len)
  _requires((bool) _inline_pulse(SizeT.v $(weights_len) = SizeT.v $(n) * SizeT.v $(n)))
  _requires((bool) _inline_pulse(SizeT.v $(base) = SizeT.v $(u) * SizeT.v $(n)))
  _requires((bool) _inline_pulse(SizeT.v $(base) + SizeT.v $(n) <= SizeT.v $(weights_len)))
  _preserves(key_out._length == n && parent_out._length == n && in_mst._length == n)
  _ensures(weights._length == weights_len)
  _preserves(_forall(size_t v, v < n ==> key_out[v] <= INFINITY_VAL))
  _preserves(_forall(size_t v, v < n ==> parent_out[v] < n))
{
  size_t idx = base;
  for (size_t v = 0; v < n; v = v + 1)
    _invariant(_live(v) && _live(idx))
    _invariant(_live(*key_out) && _live(*parent_out))
    _invariant(_live(*weights) && _live(*in_mst))
    _invariant(key_out._length == n && parent_out._length == n)
    _invariant(weights._length == weights_len && in_mst._length == n)
    _invariant((bool) _inline_pulse(SizeT.v $(weights_len) = SizeT.v $(n) * SizeT.v $(n)))
    _invariant((bool) _inline_pulse(SizeT.v $(idx) = SizeT.v $(base) + SizeT.v $(v)))
    _invariant((bool) _inline_pulse(SizeT.v $(base) + SizeT.v $(n) <= SizeT.v $(weights_len)))
    _invariant(v <= n && n > 0 && u < n)
    _invariant(_forall(size_t j, j < n ==> key_out[j] <= INFINITY_VAL))
    _invariant(_forall(size_t j, j < n ==> parent_out[j] < n))
  {
    size_t w_uv = weights[idx];
    if (in_mst[v] == 0 && w_uv > 0 && w_uv < key_out[v]) {
      key_out[v] = w_uv;
      parent_out[v] = u;
    }
    idx = idx + 1;
  }
}

/*
 * Prim's algorithm: builds MST by greedy key relaxation.
 *
 * Input:
 *   weights[weights_len] — flat weight matrix (weights_len == n*n)
 *   n                    — number of vertices (> 0)
 *   source               — starting vertex (< n)
 *
 * Output:
 *   key_out[n]    — minimum edge weight connecting each vertex to the MST
 *   parent_out[n] — parent of each vertex in the MST
 */
void prim(_array size_t *weights, size_t weights_len, size_t n, size_t source,
          _array size_t *key_out, _array size_t *parent_out)
  _requires(weights._length == weights_len && n > 0 && source < n)
  _requires((bool) _inline_pulse(SizeT.v $(weights_len) = SizeT.v $(n) * SizeT.v $(n)))
  _requires(key_out._length == n && parent_out._length == n)
  _ensures(weights._length == weights_len)
  _ensures(key_out._length == n && parent_out._length == n)
  _ensures(key_out[source] == 0)
  _ensures(_forall(size_t v, v < n ==> key_out[v] <= INFINITY_VAL))
  _ensures(parent_out[source] == source)
  _ensures(_forall(size_t v, v < n ==> parent_out[v] < n))
{
  for (size_t v = 0; v < n; v = v + 1)
    _invariant(_live(v))
    _invariant(_live(*key_out) && _live(*parent_out) && _live(*weights))
    _invariant(key_out._length == n && parent_out._length == n)
    _invariant(weights._length == weights_len)
    _invariant(v <= n && n > 0 && source < n)
    _invariant(_forall(size_t j, j < v ==> key_out[j] == INFINITY_VAL))
    _invariant(_forall(size_t j, j < v ==> key_out[j] <= INFINITY_VAL))
    _invariant(_forall(size_t j, j < v ==> parent_out[j] == source))
    _invariant(_forall(size_t j, j < v ==> parent_out[j] < n))
  {
    key_out[v] = INFINITY_VAL;
    parent_out[v] = source;
  }

  key_out[source] = 0;

  size_t *in_mst = (size_t *)calloc(n, sizeof(size_t));
  _assert(in_mst._length == n);

  /* Main loop: n iterations, each adds one vertex to MST */
  for (size_t iter = 0; iter < n; iter = iter + 1)
    _invariant(_live(iter))
    _invariant(_live(*key_out) && _live(*parent_out))
    _invariant(_live(*weights) && _live(*in_mst))
    _invariant(key_out._length == n && parent_out._length == n)
    _invariant(weights._length == weights_len && in_mst._length == n)
    _invariant((bool) _inline_pulse(SizeT.v $(weights_len) = SizeT.v $(n) * SizeT.v $(n)))
    _invariant(iter <= n && n > 0 && source < n)
    _invariant(_forall(size_t v, v < n ==> key_out[v] <= INFINITY_VAL))
    _invariant(_forall(size_t v, v < n ==> parent_out[v] < n))
  {
    size_t u = extract_min(key_out, in_mst, n);
    in_mst[u] = 1;

    size_t base = compute_base(u, n, weights_len);

    _ghost_stmt(NLArith.base_bound (SizeT.v $(u)) (SizeT.v $(n)));
    update_keys(weights, weights_len, key_out, parent_out, in_mst, n, u, base);
  }

  key_out[source] = 0;
  parent_out[source] = source;
  free(in_mst);
}
