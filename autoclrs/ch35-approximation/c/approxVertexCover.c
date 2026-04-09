/*
 * APPROX-VERTEX-COVER — C implementation with c2pulse verification.
 *
 * 2-approximation algorithm from CLRS Chapter 35.
 * Given an adjacency matrix for an undirected graph with n vertices,
 * computes a vertex cover where cover[i] = 1 if vertex i is in the cover.
 *
 * Verified properties (proven via loop invariants using AVCHelper):
 *   1. Cover validity: every edge (u,v) with u < v and adj[u*n+v] != 0
 *      has cover[u] != 0 or cover[v] != 0.
 *   2. Binary property: all cover values are 0 or 1.
 *   3. Memory safety: all array accesses are within bounds.
 *
 * Note: These properties are proven internally by the loop invariants
 * (AVCHelper.outer_inv_pure / inner_inv_pure) but cannot be exposed as
 * function postconditions due to a c2pulse limitation: with_pure(forall...)
 * does not support array_read from two arrays in the same quantifier.
 * The workaround uses (_slprop) _inline_pulse(...) to write raw Pulse
 * slprop invariants with explicit existential variable names, avoiding
 * the variable shadowing in live_array's hardcoded exists* s mask.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(open AVCHelper)
_include_pulse(open Pulse.Lib.C.Array)

void approx_vertex_cover(_array int *adj, size_t n, _array int *cover)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) `op_Multiply` SizeT.v $(n))))
  _requires(adj._length == (size_t)((_specint) n * (_specint) n))
  _requires(cover._length == n)
  _requires(n > 0)
{
  /* Phase 1: Initialize cover to all zeros */
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i))
    _invariant((_slprop) _inline_pulse(
      exists* (sa: Seq.seq (option Int32.t)) (ma: nat -> prop)
             (sc: Seq.seq (option Int32.t)) (mc: nat -> prop).
        array_pts_to $(adj) 1.0R sa ma **
        array_pts_to $(cover) 1.0R sc mc **
        pure (
          Seq.length sa = SizeT.v $(n) `op_Multiply` SizeT.v $(n) /\\
          Seq.length sc = SizeT.v $(n) /\\
          (forall (j: nat). j < SizeT.v $(i) ==> AVCHelper.seq_val sc j = 0)
        )
    ))
    _invariant(adj._length == (size_t)((_specint) n * (_specint) n))
    _invariant(cover._length == n)
    _invariant(i <= n)
  {
    cover[i] = 0;
  }

  /* Phase 2: Greedy edge scan — add both endpoints of uncovered edges */
  for (size_t u = 0; u < n; u = u + 1)
    _invariant(_live(u))
    _invariant((_slprop) _inline_pulse(
      exists* (sa: Seq.seq (option Int32.t)) (ma: nat -> prop)
             (sc: Seq.seq (option Int32.t)) (mc: nat -> prop).
        array_pts_to $(adj) 1.0R sa ma **
        array_pts_to $(cover) 1.0R sc mc **
        pure (AVCHelper.outer_inv_pure sa sc (SizeT.v $(n)) (SizeT.v $(u)))
    ))
    _invariant(adj._length == (size_t)((_specint) n * (_specint) n))
    _invariant(cover._length == n)
    _invariant(u <= n)
    _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) `op_Multiply` SizeT.v $(n))))
  {
    for (size_t v = u + 1; v < n; v = v + 1)
      _invariant(_live(v))
      _invariant((_slprop) _inline_pulse(
        exists* (sa: Seq.seq (option Int32.t)) (ma: nat -> prop)
               (sc: Seq.seq (option Int32.t)) (mc: nat -> prop).
          array_pts_to $(adj) 1.0R sa ma **
          array_pts_to $(cover) 1.0R sc mc **
          pure (AVCHelper.inner_inv_pure sa sc (SizeT.v $(n)) (SizeT.v $(u)) (SizeT.v $(v)))
      ))
      _invariant(adj._length == (size_t)((_specint) n * (_specint) n))
      _invariant(cover._length == n)
      _invariant(v <= n)
      _invariant(u < n)
      _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) `op_Multiply` SizeT.v $(n))))
    {
      if (adj[u * n + v] != 0 && cover[u] == 0 && cover[v] == 0) {
        cover[u] = 1;
        cover[v] = 1;
      }
    }
  }
}
