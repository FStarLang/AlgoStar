module ApproxVertexCover
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

open AVCHelper

#restart-solver

open Pulse.Lib.C.Array

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
  let mut var_u : SizeT.t;
  var_u := 0sz;
  while (((!var_u) `SizeT.lt` (!var_n)))
    invariant (live var_u)
    invariant (exists* (sa: Seq.seq (option Int32.t)) (ma: nat -> prop)
(sc: Seq.seq (option Int32.t)) (mc: nat -> prop).
array_pts_to (!var_adj) 1.0R sa ma **
array_pts_to (!var_cover) 1.0R sc mc **
pure (AVCHelper.outer_inv_pure sa sc (SizeT.v (!var_n)) (SizeT.v (!var_u))))
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
(sc: Seq.seq (option Int32.t)) (mc: nat -> prop).
array_pts_to (!var_adj) 1.0R sa ma **
array_pts_to (!var_cover) 1.0R sc mc **
pure (AVCHelper.inner_inv_pure sa sc (SizeT.v (!var_n)) (SizeT.v (!var_u)) (SizeT.v (!var_v))))
      invariant (with_pure
          ((reveal (length_of (!var_adj))) =
            (SizeT.v (SizeT.uint_to_t ((SizeT.v (!var_n)) `op_Multiply` (SizeT.v (!var_n)))))))
      invariant (with_pure ((reveal (length_of (!var_cover))) = (SizeT.v (!var_n))))
      invariant (with_pure ((!var_v) `SizeT.lte` (!var_n)))
      invariant (with_pure ((!var_u) `SizeT.lt` (!var_n)))
      invariant (with_pure (SizeT.fits (SizeT.v (!var_n) `op_Multiply` SizeT.v (!var_n))))
    {
      if ((((not
                (((array_read (!var_adj) (((!var_u) `SizeT.mul` (!var_n)) `SizeT.add` (!var_v)))) =
                  (Int32.int_to_t 0)))
              &&
              (((array_read (!var_cover) (!var_u))) = (Int32.int_to_t 0)))
            &&
            (((array_read (!var_cover) (!var_v))) = (Int32.int_to_t 0)))) {
        (array_write (!var_cover) (!var_u) (Int32.int_to_t 1));
        (array_write (!var_cover) (!var_v) (Int32.int_to_t 1));
      } else {};
      var_v := ((!var_v) `SizeT.add` 1sz);
    };
    var_u := ((!var_u) `SizeT.add` 1sz);
  };
}