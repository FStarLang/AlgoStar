/*
 * Maximum Flow — Edmonds-Karp (BFS-based Ford-Fulkerson)
 * C implementation with c2pulse verification annotations.
 *
 * Implements CLRS §26.2:
 *   1. BFS on residual graph to find shortest augmenting path
 *   2. Find bottleneck (min residual capacity) along the path
 *   3. Augment flow along the path
 *   4. Repeat until no augmenting path exists
 *
 * Representation: flat n×n arrays (row-major) for capacity and flow.
 *   Element (u,v) is stored at index u*n+v.
 *
 * Type strategy: size_t for all vertex indices and counts (n, source, sink,
 * loop counters). int for data values (capacity, flow, colors, distances).
 * Queue and pred arrays are size_t* (store vertex indices).
 * Sentinel for "no predecessor" is n (invalid vertex).
 *
 * Verified properties (no admit):
 *   - zero_init: all elements set to 0
 *   - bfs_init: color/pred/dist correctly initialized for BFS
 *   - find_bottleneck_rec/find_bottleneck: returns positive bottleneck,
 *     array bounds + SizeT arithmetic fully verified via index_fits lemma,
 *     Int32 subtraction overflow proved via non-negativity preconditions
 *
 * Admitted (Int32 overflow — c2pulse uses Int32.t, Pulse Impl uses int):
 *   - bfs_residual: dist[u]+1 can overflow for n > 2^31
 *   - augment_flow_rec/augment_flow: flow[i]+bn can overflow
 *   - compute_flow_value: accumulator fv can overflow
 *   - max_flow: depends on above; also nested let-mut structural limitation
 *
 * Target spec: CLRS.Ch26.MaxFlow.Impl.fsti
 * Bridge lemmas: CLRS.Ch26.MaxFlow.C.BridgeLemmas.fst
 */

#include <stdlib.h>
#include <stdint.h>
#include "c2pulse.h"

_include_pulse(open CLRS.Ch26.MaxFlow.C.BridgeLemmas)

/* ================================================================
   ZERO INITIALIZATION
   ================================================================ */

void zero_init(_array int *arr, size_t len)
  _requires(arr._length == len)
  _ensures(arr._length == len)
  _ensures(_forall(size_t k, k < len ==> arr[k] == 0))
{
  for (size_t i = 0; i < len; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*arr))
    _invariant(arr._length == len)
    _invariant(i <= len)
    _invariant(_forall(size_t k, k < i ==> arr[k] == 0))
  {
    arr[i] = 0;
  }
}

/* ================================================================
   BFS INITIALIZATION
   ================================================================ */

void bfs_init(
    _array int *color,
    _array size_t *pred,
    _array int *dist,
    size_t n,
    size_t source)
  _requires(color._length == n && pred._length == n && dist._length == n)
  _requires(n > 0 && source < n)
  _ensures(color._length == n && pred._length == n && dist._length == n)
  _ensures(color[source] == 1 && dist[source] == 0)
  _ensures(_forall(size_t i, i < n && i != source ==> color[i] == 0))
  _ensures(_forall(size_t i, i < n && i != source ==> pred[i] == n))
  _ensures(_forall(size_t i, i < n && i != source ==> dist[i] == -1))
{
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant(_live(*color) && _live(*pred) && _live(*dist))
    _invariant(color._length == n && pred._length == n && dist._length == n)
    _invariant(i <= n)
    _invariant(_forall(size_t k, k < i ==> color[k] == 0))
    _invariant(_forall(size_t k, k < i ==> pred[k] == n))
    _invariant(_forall(size_t k, k < i ==> dist[k] == -1))
  {
    color[i] = 0;
    pred[i] = n;
    dist[i] = -1;
  }
  color[source] = 1;
  dist[source] = 0;
}

/* ================================================================
   BFS ON RESIDUAL GRAPH
   ================================================================ */

/*
 * Run BFS on the residual graph. Returns 1 if sink is reachable.
 * Residual edge (u,v) exists if cap(u,v)-flow(u,v) > 0 or flow(v,u) > 0.
 */
int bfs_residual(
    _array int *cap,
    _array int *flow,
    _array int *color,
    _array size_t *pred,
    _array int *dist,
    _array size_t *queue,
    size_t n,
    size_t source,
    size_t sink)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(cap._length == (_specint)n * (_specint)n && flow._length == (_specint)n * (_specint)n)
  _requires(color._length == n && pred._length == n &&
            dist._length == n && queue._length == n)
  _requires(n > 0 && source < n && sink < n && source != sink)
  _requires(_forall(size_t p, p < (_specint)n * (_specint)n ==> cap[p] >= 0))
  _requires(_forall(size_t p, p < (_specint)n * (_specint)n ==> flow[p] >= 0))
  _ensures(cap._length == (_specint)n * (_specint)n && flow._length == (_specint)n * (_specint)n)
  _ensures(color._length == n && pred._length == n &&
           dist._length == n && queue._length == n)
{
  _ghost_stmt(admit());
  bfs_init(color, pred, dist, n, source);

  queue[0] = source;
  size_t q_head = 0;
  size_t q_tail = 1;

  while (q_head < q_tail)
    _invariant(_live(q_head) && _live(q_tail))
    _invariant(_live(*cap) && _live(*flow))
    _invariant(_live(*color) && _live(*pred) && _live(*dist) && _live(*queue))
    _invariant(cap._length == (_specint)n * (_specint)n && flow._length == (_specint)n * (_specint)n)
    _invariant(color._length == n && pred._length == n &&
               dist._length == n && queue._length == n)
    _invariant(q_head <= q_tail && q_tail <= n)
    _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
    _invariant(_forall(size_t p, p < (_specint)n * (_specint)n ==> cap[p] >= 0))
    _invariant(_forall(size_t p, p < (_specint)n * (_specint)n ==> flow[p] >= 0))
  {
    size_t u = queue[q_head];
    q_head = q_head + 1;

    if (u < n) {
      for (size_t v = 0; v < n; v = v + 1)
        _invariant(_live(v) && _live(q_head) && _live(q_tail) && _live(u))
        _invariant(_live(*cap) && _live(*flow))
        _invariant(_live(*color) && _live(*pred) && _live(*dist) && _live(*queue))
        _invariant(cap._length == (_specint)n * (_specint)n && flow._length == (_specint)n * (_specint)n)
        _invariant(color._length == n && pred._length == n &&
                   dist._length == n && queue._length == n)
        _invariant(v <= n)
        _invariant(q_head <= q_tail && q_tail <= n)
        _invariant(u < n)
        _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
        _invariant(_forall(size_t p, p < (_specint)n * (_specint)n ==> cap[p] >= 0))
        _invariant(_forall(size_t p, p < (_specint)n * (_specint)n ==> flow[p] >= 0))
      {
        _ghost_stmt(index_fits (SizeT.v $(u)) (SizeT.v $(v)) (SizeT.v $(n)));
        _ghost_stmt(index_fits (SizeT.v $(v)) (SizeT.v $(u)) (SizeT.v $(n)));
        int color_v = color[v];
        int res_fwd = cap[u * n + v] - flow[u * n + v];
        int res_bwd = flow[v * n + u];
        int dist_u = dist[u];

        if (color_v == 0 && (res_fwd > 0 || res_bwd > 0)) {
          color[v] = 1;
          pred[v] = u;
          dist[v] = dist_u + 1;

          if (q_tail < n) {
            queue[q_tail] = v;
            q_tail = q_tail + 1;
          }
        }
      }

      color[u] = 2;
    }
  }

  int result = color[sink];
  if (result != 0) return 1;
  return 0;
}

/* ================================================================
   BOTTLENECK COMPUTATION (recursive)
   ================================================================ */

/*
 * Recursive helper: walk pred chain from cur to source, tracking min
 * residual capacity in bn.  fuel limits recursion depth (≤ n).
 */
_rec int find_bottleneck_rec(
    _array int *cap,
    _array int *flow,
    _array size_t *pred,
    size_t n,
    size_t source,
    size_t cur,
    int bn,
    size_t fuel)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(cap._length == (_specint)n * (_specint)n && flow._length == (_specint)n * (_specint)n &&
            pred._length == n)
  _requires(n > 0 && source < n && cur < n && bn > 0 && fuel <= n)
  _requires(_forall(size_t p, p < (_specint)n * (_specint)n ==> cap[p] >= 0))
  _requires(_forall(size_t p, p < (_specint)n * (_specint)n ==> flow[p] >= 0))
  _preserves_value(cap._length)
  _preserves_value(flow._length)
  _preserves_value(pred._length)
  _ensures(return > 0)
  _decreases((_specint) fuel)
{
  if (cur == source || fuel == 0) {
    return bn;
  }
  size_t u = pred[cur];
  if (u >= n) {
    return bn;
  }

  _ghost_stmt(index_fits (SizeT.v $(u)) (SizeT.v $(cur)) (SizeT.v $(n)));
  _ghost_stmt(index_fits (SizeT.v $(cur)) (SizeT.v $(u)) (SizeT.v $(n)));
  int res_fwd = cap[u * n + cur] - flow[u * n + cur];
  int res_bwd = flow[cur * n + u];
  int new_bn = bn;
  if (res_fwd > 0) {
    if (res_fwd < bn) new_bn = res_fwd;
  } else {
    if (res_bwd > 0 && res_bwd < bn) new_bn = res_bwd;
  }

  return find_bottleneck_rec(cap, flow, pred, n, source, u, new_bn, fuel - 1);
}

/*
 * Find min residual capacity along pred chain from sink to source.
 */
int find_bottleneck(
    _array int *cap,
    _array int *flow,
    _array size_t *pred,
    size_t n,
    size_t source,
    size_t sink)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(cap._length == (_specint)n * (_specint)n && flow._length == (_specint)n * (_specint)n &&
            pred._length == n)
  _requires(n > 0 && source < n && sink < n && source != sink)
  _requires(_forall(size_t p, p < (_specint)n * (_specint)n ==> cap[p] >= 0))
  _requires(_forall(size_t p, p < (_specint)n * (_specint)n ==> flow[p] >= 0))
  _ensures(cap._length == (_specint)n * (_specint)n && flow._length == (_specint)n * (_specint)n &&
           pred._length == n)
  _ensures(return > 0)
{
  return find_bottleneck_rec(cap, flow, pred, n, source, sink, 2147483647, n);
}

/* ================================================================
   FLOW AUGMENTATION (recursive)
   ================================================================ */

/*
 * Recursive helper: walk pred chain from cur to source, augmenting
 * flow by bn units along each edge.  fuel limits recursion depth.
 */
_rec void augment_flow_rec(
    _array int *cap,
    _array int *flow,
    _array size_t *pred,
    size_t n,
    size_t source,
    size_t cur,
    int bn,
    size_t fuel)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(cap._length == (_specint)n * (_specint)n && flow._length == (_specint)n * (_specint)n &&
            pred._length == n)
  _requires(n > 0 && source < n && cur < n && bn > 0 && fuel <= n)
  _requires(_forall(size_t p, p < (_specint)n * (_specint)n ==> cap[p] >= 0))
  _requires(_forall(size_t p, p < (_specint)n * (_specint)n ==> flow[p] >= 0))
  _preserves_value(cap._length)
  _preserves_value(pred._length)
  _ensures(flow._length == (_specint)n * (_specint)n)
  _decreases((_specint) fuel)
{
  _ghost_stmt(admit());
  if (cur == source || fuel == 0) {
    return;
  }
  size_t u = pred[cur];
  if (u >= n) {
    return;
  }

  int res_fwd = cap[u * n + cur] - flow[u * n + cur];
  if (res_fwd > 0) {
    flow[u * n + cur] = flow[u * n + cur] + bn;
  } else {
    flow[cur * n + u] = flow[cur * n + u] - bn;
  }

  augment_flow_rec(cap, flow, pred, n, source, u, bn, fuel - 1);
}

/*
 * Augment flow along the pred chain by bn units.
 */
void augment_flow(
    _array int *cap,
    _array int *flow,
    _array size_t *pred,
    size_t n,
    size_t source,
    size_t sink,
    int bn)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(cap._length == (_specint)n * (_specint)n && flow._length == (_specint)n * (_specint)n &&
            pred._length == n)
  _requires(n > 0 && source < n && sink < n && source != sink && bn > 0)
  _requires(_forall(size_t p, p < (_specint)n * (_specint)n ==> cap[p] >= 0))
  _requires(_forall(size_t p, p < (_specint)n * (_specint)n ==> flow[p] >= 0))
  _ensures(cap._length == (_specint)n * (_specint)n && flow._length == (_specint)n * (_specint)n &&
           pred._length == n)
{
  augment_flow_rec(cap, flow, pred, n, source, sink, bn, n);
}

/* ================================================================
   FLOW VALUE COMPUTATION
   ================================================================ */

int compute_flow_value(
    _array int *flow,
    size_t n,
    size_t source)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(flow._length == (_specint)n * (_specint)n)
  _requires(n > 0 && source < n)
  _ensures(flow._length == (_specint)n * (_specint)n)
{
  _ghost_stmt(admit());
  int fv = 0;

  for (size_t v = 0; v < n; v = v + 1)
    _invariant(_live(v) && _live(fv))
    _invariant(_live(*flow))
    _invariant(flow._length == (_specint)n * (_specint)n)
    _invariant(v <= n)
  {
    _ghost_stmt(index_fits (SizeT.v $(source)) (SizeT.v $(v)) (SizeT.v $(n)));
    _ghost_stmt(index_fits (SizeT.v $(v)) (SizeT.v $(source)) (SizeT.v $(n)));
    fv = fv + flow[source * n + v] - flow[v * n + source];
  }

  return fv;
}

/* ================================================================
   MAIN: EDMONDS-KARP MAX FLOW
   ================================================================ */

/*
 * Compute maximum flow from source to sink using Edmonds-Karp.
 *
 * Parameters:
 *   cap:    n×n flat capacity matrix (all entries >= 0)
 *   flow:   n×n flat flow matrix (output, overwritten to zero then filled)
 *   n:      number of vertices (n > 0)
 *   source: source vertex index
 *   sink:   sink vertex index
 *
 * Returns: the maximum flow value (>= 0).
 */
int max_flow(
    _array int *cap,
    _array int *flow,
    size_t n,
    size_t source,
    size_t sink)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(cap._length == (_specint)n * (_specint)n && flow._length == (_specint)n * (_specint)n)
  _requires(n > 0 && source < n && sink < n && source != sink)
  _requires(_forall(size_t k, k < (_specint)n * (_specint)n ==> cap[k] >= 0))
  _ensures(cap._length == (_specint)n * (_specint)n && flow._length == (_specint)n * (_specint)n)
  _ensures(return >= 0)
  _ensures(_forall(size_t k, k < (_specint)n * (_specint)n ==> flow[k] >= 0))
{
  _ghost_stmt(admit());
  zero_init(flow, n * n);

  _array int *color = (int *)calloc(n, sizeof(int));
  _assert(color._length == n);
  _array size_t *pred_arr = (size_t *)calloc(n, sizeof(size_t));
  _assert(pred_arr._length == n);
  _array int *dist_arr = (int *)calloc(n, sizeof(int));
  _assert(dist_arr._length == n);
  _array size_t *queue_arr = (size_t *)calloc(n, sizeof(size_t));
  _assert(queue_arr._length == n);

  int done = 0;

  while (done == 0)
    _invariant(_live(done))
    _invariant(_live(*cap) && _live(*flow))
    _invariant(_live(*color) && _live(*pred_arr) &&
               _live(*dist_arr) && _live(*queue_arr))
    _invariant(cap._length == (_specint)n * (_specint)n && flow._length == (_specint)n * (_specint)n)
    _invariant(color._length == n && pred_arr._length == n &&
               dist_arr._length == n && queue_arr._length == n)
  {
    int found = bfs_residual(cap, flow, color, pred_arr,
                             dist_arr, queue_arr, n, source, sink);

    if (found != 0) {
      int bn = find_bottleneck(cap, flow, pred_arr, n, source, sink);
      augment_flow(cap, flow, pred_arr, n, source, sink, bn);
    } else {
      done = 1;
    }
  }

  int fv = compute_flow_value(flow, n, source);

  free(color);
  free(pred_arr);
  free(dist_arr);
  free(queue_arr);

  return fv;
}
