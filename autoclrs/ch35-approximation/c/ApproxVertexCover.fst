module ApproxVertexCover
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

open AVCHelper

#restart-solver

open Pulse.Lib.C.Array

#restart-solver

open AVCBridgeLemmas

#restart-solver

open CLRS.Ch35.VertexCover.Spec

#restart-solver

open AVCGhostStep

#restart-solver

module GR = Pulse.Lib.GhostReference

#restart-solver

fn func_approx_vertex_cover (var_adj: (array Int32.t)) (var_n: SizeT.t) (var_cover: (array Int32.t))
  requires
    exists* (val_adj_0: (Seq.seq (option Int32.t))) (val_adj_1: (nat->prop)).
    ((array_pts_to var_adj 1.0R val_adj_0 val_adj_1))
  requires
    exists* (val_cover_0: (Seq.seq (option Int32.t))) (val_cover_1: (nat->prop)).
    ((array_pts_to var_cover 1.0R val_cover_0 val_cover_1))
  requires (with_pure (SizeT.fits (SizeT.v var_n `op_Multiply` SizeT.v var_n)))
  requires
    (with_pure
      ((reveal (length_of var_adj)) =
        (SizeT.v (SizeT.uint_to_t ((SizeT.v var_n) `op_Multiply` (SizeT.v var_n))))))
  requires (with_pure ((reveal (length_of var_cover)) = (SizeT.v var_n)))
  requires (with_pure (0 < (SizeT.v var_n)))
  returns return_1 : unit
  ensures
    exists* (val_adj_0: (Seq.seq (option Int32.t))) (val_adj_1: (nat->prop)).
    ((array_pts_to var_adj 1.0R val_adj_0 val_adj_1))
  ensures
    exists* (val_cover_0: (Seq.seq (option Int32.t))) (val_cover_1: (nat->prop)).
    ((array_pts_to var_cover 1.0R val_cover_0 val_cover_1))
  ensures
    (with_pure
      (AVCHelper.outer_inv_pure
(array_value_of var_adj)
(array_value_of var_cover)
(SizeT.v var_n)
(SizeT.v var_n)))
  ensures
    (with_pure
      (CLRS.Ch35.VertexCover.Spec.is_cover
(AVCBridgeLemmas.to_int_seq (array_value_of var_adj))
(AVCBridgeLemmas.to_int_seq (array_value_of var_cover))
(SizeT.v var_n) (SizeT.v var_n) 0))
  ensures
    (with_pure
      (exists (opt: nat). CLRS.Ch35.VertexCover.Spec.min_vertex_cover_size
(AVCBridgeLemmas.to_int_seq (array_value_of var_adj)) (SizeT.v var_n) opt))
  ensures
    (with_pure
      (forall (opt: nat). CLRS.Ch35.VertexCover.Spec.min_vertex_cover_size
(AVCBridgeLemmas.to_int_seq (array_value_of var_adj)) (SizeT.v var_n) opt ==>
CLRS.Ch35.VertexCover.Spec.count_cover
(CLRS.Ch35.VertexCover.Spec.seq_to_cover_fn
(AVCBridgeLemmas.to_int_seq (array_value_of var_cover)) (SizeT.v var_n))
(SizeT.v var_n) <= 2 `op_Multiply` opt))
  ensures
    (with_pure
      (exists (k: nat). CLRS.Ch35.VertexCover.Spec.count_cover
(CLRS.Ch35.VertexCover.Spec.seq_to_cover_fn
(AVCBridgeLemmas.to_int_seq (array_value_of var_cover)) (SizeT.v var_n))
(SizeT.v var_n) = 2 `op_Multiply` k))
{
  let mut var_adj = var_adj;
  let mut var_n = var_n;
  let mut var_cover = var_cover;
  let mut var_i : SizeT.t;
  var_i := 0sz;
  while (((!var_i) `SizeT.lt` (!var_n)))
    invariant (live var_i)
    invariant (exists* (sa: Seq.seq (option Int32.t)) (ma: nat -> prop)
(sc: Seq.seq (option Int32.t)) (mc: nat -> prop).
array_pts_to (!var_adj) 1.0R sa ma **
array_pts_to (!var_cover) 1.0R sc mc **
pure (
Seq.length sa = SizeT.v (!var_n) `op_Multiply` SizeT.v (!var_n) /\ Seq.length sc = SizeT.v (!var_n) /\ (forall (j: nat). j < SizeT.v (!var_i) ==> AVCHelper.seq_val sc j = 0)
))
    invariant (with_pure
        ((reveal (length_of (!var_adj))) =
          (SizeT.v (SizeT.uint_to_t ((SizeT.v (!var_n)) `op_Multiply` (SizeT.v (!var_n)))))))
    invariant (with_pure ((reveal (length_of (!var_cover))) = (SizeT.v (!var_n))))
    invariant (with_pure ((!var_i) `SizeT.lte` (!var_n)))
  {
    (array_write (!var_cover) (!var_i) (Int32.int_to_t 0));
    var_i := ((!var_i) `SizeT.add` 1sz);
  };
  let matching_ref = GR.alloc #(list CLRS.Ch35.VertexCover.Spec.edge)
(Nil #CLRS.Ch35.VertexCover.Spec.edge);
  let mut var_u : SizeT.t;
  var_u := 0sz;
  while (((!var_u) `SizeT.lt` (!var_n)))
    invariant (live var_u)
    invariant (exists* (sa: Seq.seq (option Int32.t)) (ma: nat -> prop)
(sc: Seq.seq (option Int32.t)) (mc: nat -> prop)
(vm: list CLRS.Ch35.VertexCover.Spec.edge).
array_pts_to (!var_adj) 1.0R sa ma **
array_pts_to (!var_cover) 1.0R sc mc **
GR.pts_to matching_ref vm **
pure (AVCHelper.outer_inv_pure sa sc (SizeT.v (!var_n)) (SizeT.v (!var_u)) /\ AVCHelper.matching_inv_opt sa sc (SizeT.v (!var_n)) vm))
    invariant (with_pure
        ((reveal (length_of (!var_adj))) =
          (SizeT.v (SizeT.uint_to_t ((SizeT.v (!var_n)) `op_Multiply` (SizeT.v (!var_n)))))))
    invariant (with_pure ((reveal (length_of (!var_cover))) = (SizeT.v (!var_n))))
    invariant (with_pure ((!var_u) `SizeT.lte` (!var_n)))
    invariant (with_pure (SizeT.fits (SizeT.v (!var_n) `op_Multiply` SizeT.v (!var_n))))
  {
    let mut var_v : SizeT.t;
    var_v := ((!var_u) `SizeT.add` 1sz);
    while (((!var_v) `SizeT.lt` (!var_n)))
      invariant (live var_v)
      invariant (exists* (sa: Seq.seq (option Int32.t)) (ma: nat -> prop)
(sc: Seq.seq (option Int32.t)) (mc: nat -> prop)
(vm: list CLRS.Ch35.VertexCover.Spec.edge).
array_pts_to (!var_adj) 1.0R sa ma **
array_pts_to (!var_cover) 1.0R sc mc **
GR.pts_to matching_ref vm **
pure (AVCHelper.inner_inv_pure sa sc (SizeT.v (!var_n)) (SizeT.v (!var_u)) (SizeT.v (!var_v)) /\ AVCHelper.matching_inv_opt sa sc (SizeT.v (!var_n)) vm))
      invariant (with_pure
          ((reveal (length_of (!var_adj))) =
            (SizeT.v (SizeT.uint_to_t ((SizeT.v (!var_n)) `op_Multiply` (SizeT.v (!var_n)))))))
      invariant (with_pure ((reveal (length_of (!var_cover))) = (SizeT.v (!var_n))))
      invariant (with_pure ((!var_v) `SizeT.lte` (!var_n)))
      invariant (with_pure ((!var_u) `SizeT.lt` (!var_n)))
      invariant (with_pure ((!var_u) `SizeT.lt` (!var_v)))
      invariant (with_pure (SizeT.fits (SizeT.v (!var_n) `op_Multiply` SizeT.v (!var_n))))
    {
      let mut var_has_edge : Int32.t;
      var_has_edge :=
        ((array_read (!var_adj) (((!var_u) `SizeT.mul` (!var_n)) `SizeT.add` (!var_v))));
      let mut var_cu : Int32.t;
      var_cu := ((array_read (!var_cover) (!var_u)));
      let mut var_cv : Int32.t;
      var_cv := ((array_read (!var_cover) (!var_v)));
      let mut var_new_cu : Int32.t;
      var_new_cu := (!var_cu);
      let mut var_new_cv : Int32.t;
      var_new_cv := (!var_cv);
      if ((((not ((!var_has_edge) = (Int32.int_to_t 0))) && ((!var_cu) = (Int32.int_to_t 0))) &&
            ((!var_cv) = (Int32.int_to_t 0)))) {
        var_new_cu := (Int32.int_to_t 1);
        var_new_cv := (Int32.int_to_t 1);
      } else {};
      AVCGhostStep.matching_step_ghost matching_ref (!var_adj) (!var_cover) (!var_n) (!var_u) (!var_v)
(!var_has_edge) (!var_cu) (!var_cv) (!var_new_cu) (!var_new_cv);
      (array_write (!var_cover) (!var_u) (!var_new_cu));
      (array_write (!var_cover) (!var_v) (!var_new_cv));
      var_v := ((!var_v) `SizeT.add` 1sz);
    };
    var_u := ((!var_u) `SizeT.add` 1sz);
  };
  let vm_final = GR.op_Bang matching_ref;
AVCBridgeLemmas.bridge_full
(array_value_of (!var_adj)) (array_value_of (!var_cover)) (SizeT.v (!var_n));
AVCBridgeLemmas.bridge_apply_approximation
(array_value_of (!var_adj)) (array_value_of (!var_cover)) (SizeT.v (!var_n)) vm_final;
AVCBridgeLemmas.bridge_derive_even_count
(array_value_of (!var_adj)) (array_value_of (!var_cover)) (SizeT.v (!var_n)) vm_final;
GR.free matching_ref;
}