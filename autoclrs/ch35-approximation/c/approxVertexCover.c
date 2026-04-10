/*
 * APPROX-VERTEX-COVER — C implementation with c2pulse verification.
 *
 * 2-approximation algorithm from CLRS Chapter 35.
 * Given an adjacency matrix for an undirected graph with n vertices,
 * computes a vertex cover where cover[i] = 1 if vertex i is in the cover.
 *
 * Verified properties (exposed as postconditions):
 *   1. Cover validity: every edge (u,v) with u < v and adj[u*n+v] != 0
 *      has cover[u] != 0 or cover[v] != 0.
 *   2. Binary property: all cover values are 0 or 1.
 *   3. 2-approximation: cover size <= 2 * OPT.
 *   4. Even cover count: cover size = 2*k for some k.
 *   5. Memory safety: all array accesses are within bounds.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(open AVCHelper)
_include_pulse(open Pulse.Lib.C.Array)
_include_pulse(open AVCBridgeLemmas)
_include_pulse(open CLRS.Ch35.VertexCover.Spec)
_include_pulse(open AVCGhostStep)
_include_pulse(module GR = Pulse.Lib.GhostReference)

void approx_vertex_cover(_array int *adj, size_t n, _array int *cover)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) `op_Multiply` SizeT.v $(n))))
  _requires(adj._length == (size_t)((_specint) n * (_specint) n))
  _requires(cover._length == n)
  _requires(n > 0)
  /* Cover validity + binary via outer_inv_pure */
  _ensures((bool) _inline_pulse(
    AVCHelper.outer_inv_pure
      (array_value_of $(adj))
      (array_value_of $(cover))
      (SizeT.v $(n))
      (SizeT.v $(n))))
  /* Spec-level: is_cover */
  _ensures((bool) _inline_pulse(
    CLRS.Ch35.VertexCover.Spec.is_cover
      (AVCBridgeLemmas.to_int_seq (array_value_of $(adj)))
      (AVCBridgeLemmas.to_int_seq (array_value_of $(cover)))
      (SizeT.v $(n)) (SizeT.v $(n)) 0))
  /* 2-approximation bound */
  _ensures((bool) _inline_pulse(
    forall (opt: nat). CLRS.Ch35.VertexCover.Spec.min_vertex_cover_size
      (AVCBridgeLemmas.to_int_seq (array_value_of $(adj))) (SizeT.v $(n)) opt ==>
    CLRS.Ch35.VertexCover.Spec.count_cover
      (CLRS.Ch35.VertexCover.Spec.seq_to_cover_fn
        (AVCBridgeLemmas.to_int_seq (array_value_of $(cover))) (SizeT.v $(n)))
      (SizeT.v $(n)) <= 2 `op_Multiply` opt))
  /* Even cover count */
  _ensures((bool) _inline_pulse(
    exists (k: nat). CLRS.Ch35.VertexCover.Spec.count_cover
      (CLRS.Ch35.VertexCover.Spec.seq_to_cover_fn
        (AVCBridgeLemmas.to_int_seq (array_value_of $(cover))) (SizeT.v $(n)))
      (SizeT.v $(n)) = 2 `op_Multiply` k))
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

  /* Ghost: allocate matching tracker */
  _ghost_stmt(
    let matching_ref = GR.alloc #(list CLRS.Ch35.VertexCover.Spec.edge)
      (Nil #CLRS.Ch35.VertexCover.Spec.edge)
  );

  /* Phase 2: Greedy edge scan — add both endpoints of uncovered edges */
  for (size_t u = 0; u < n; u = u + 1)
    _invariant(_live(u))
    _invariant((_slprop) _inline_pulse(
      exists* (sa: Seq.seq (option Int32.t)) (ma: nat -> prop)
             (sc: Seq.seq (option Int32.t)) (mc: nat -> prop)
             (vm: list CLRS.Ch35.VertexCover.Spec.edge).
        array_pts_to $(adj) 1.0R sa ma **
        array_pts_to $(cover) 1.0R sc mc **
        GR.pts_to matching_ref vm **
        pure (AVCHelper.outer_inv_pure sa sc (SizeT.v $(n)) (SizeT.v $(u)) /\\
              AVCHelper.matching_inv_opt sa sc (SizeT.v $(n)) vm)
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
               (sc: Seq.seq (option Int32.t)) (mc: nat -> prop)
               (vm: list CLRS.Ch35.VertexCover.Spec.edge).
          array_pts_to $(adj) 1.0R sa ma **
          array_pts_to $(cover) 1.0R sc mc **
          GR.pts_to matching_ref vm **
          pure (AVCHelper.inner_inv_pure sa sc (SizeT.v $(n)) (SizeT.v $(u)) (SizeT.v $(v)) /\\
                AVCHelper.matching_inv_opt sa sc (SizeT.v $(n)) vm)
      ))
      _invariant(adj._length == (size_t)((_specint) n * (_specint) n))
      _invariant(cover._length == n)
      _invariant(v <= n)
      _invariant(u < n)
      _invariant(u < v)
      _invariant((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) `op_Multiply` SizeT.v $(n))))
    {
      int has_edge = adj[u * n + v];
      int cu = cover[u];
      int cv = cover[v];
      int new_cu = cu;
      int new_cv = cv;
      if (has_edge != 0 && cu == 0 && cv == 0) {
        new_cu = 1;
        new_cv = 1;
      }
      /* Ghost: unconditional matching step */
      _ghost_stmt(
        AVCGhostStep.matching_step_ghost matching_ref $(adj) $(cover) $(n) $(u) $(v)
          $(has_edge) $(cu) $(cv) $(new_cu) $(new_cv)
      );
      /* Unconditional cover writes */
      cover[u] = new_cu;
      cover[v] = new_cv;
    }
  }

  /* Ghost: apply bridge lemmas and free ghost ref */
  _ghost_stmt(
    let vm_final = GR.op_Bang matching_ref;
    AVCBridgeLemmas.bridge_full
      (array_value_of $(adj)) (array_value_of $(cover)) (SizeT.v $(n));
    AVCBridgeLemmas.bridge_apply_approximation
      (array_value_of $(adj)) (array_value_of $(cover)) (SizeT.v $(n)) vm_final;
    AVCBridgeLemmas.bridge_derive_even_count
      (array_value_of $(adj)) (array_value_of $(cover)) (SizeT.v $(n)) vm_final;
    GR.free matching_ref
  );
}
