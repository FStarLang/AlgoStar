module Prim
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

open Pulse.Lib.C.Array

#restart-solver

open CLRS.Ch23.Prim.C.BridgeLemmas

#restart-solver

open CLRS.Ch23.Prim.Impl

#restart-solver

fn func_extract_min
    (var_key_out: (array SizeT.t))
    (var_in_mst: (array SizeT.t))
    (var_n: SizeT.t)
    (var_parent_out: (array SizeT.t))
    (var_weights: (array SizeT.t))
    (var_weights_len: SizeT.t)
    (var_source: SizeT.t)
  requires
    exists* (val_key_out_0: (Seq.seq (option SizeT.t))) (val_key_out_1: (nat->prop)).
    ((array_pts_to var_key_out 1.0R val_key_out_0 val_key_out_1))
  requires
    exists* (val_in_mst_0: (Seq.seq (option SizeT.t))) (val_in_mst_1: (nat->prop)).
    ((array_pts_to var_in_mst 1.0R val_in_mst_0 val_in_mst_1))
  requires
    exists* (val_parent_out_0: (Seq.seq (option SizeT.t))) (val_parent_out_1: (nat->prop)).
    ((array_pts_to var_parent_out 1.0R val_parent_out_0 val_parent_out_1))
  requires
    exists* (val_weights_0: (Seq.seq (option SizeT.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  requires (with_pure ((0 < (SizeT.v var_n)) && (var_source `SizeT.lt` var_n)))
  requires
    (with_pure
      (((reveal (length_of var_key_out)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_in_mst)) = (SizeT.v var_n))))
  requires
    (with_pure
      (((reveal (length_of var_parent_out)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_weights)) = (SizeT.v var_weights_len))))
  requires
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==> (((array_read var_key_out var_v)) `SizeT.lte` 65535sz))))
  requires
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==> (((array_read var_parent_out var_v)) `SizeT.lt` var_n))))
  requires (with_pure (SizeT.v var_weights_len = SizeT.v var_n * SizeT.v var_n))
  requires
    (with_pure
      (CLRS.Ch23.Prim.C.BridgeLemmas.kpc_opt
(array_value_of var_key_out)
(array_value_of var_parent_out)
(array_value_of var_weights)
(SizeT.v var_n)
(SizeT.v var_source)))
  returns return_1 : SizeT.t
  ensures
    exists* (val_key_out_0: (Seq.seq (option SizeT.t))) (val_key_out_1: (nat->prop)).
    ((array_pts_to var_key_out 1.0R val_key_out_0 val_key_out_1))
  ensures
    exists* (val_in_mst_0: (Seq.seq (option SizeT.t))) (val_in_mst_1: (nat->prop)).
    ((array_pts_to var_in_mst 1.0R val_in_mst_0 val_in_mst_1))
  ensures
    exists* (val_parent_out_0: (Seq.seq (option SizeT.t))) (val_parent_out_1: (nat->prop)).
    ((array_pts_to var_parent_out 1.0R val_parent_out_0 val_parent_out_1))
  ensures
    exists* (val_weights_0: (Seq.seq (option SizeT.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  ensures
    (with_pure
      (((reveal (length_of var_key_out)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_in_mst)) = (SizeT.v var_n))))
  ensures
    (with_pure
      (((reveal (length_of var_parent_out)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_weights)) = (SizeT.v var_weights_len))))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==> (((array_read var_key_out var_v)) `SizeT.lte` 65535sz))))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==> (((array_read var_parent_out var_v)) `SizeT.lt` var_n))))
  ensures (with_pure (SizeT.v var_weights_len = SizeT.v var_n * SizeT.v var_n))
  ensures
    (with_pure
      (CLRS.Ch23.Prim.C.BridgeLemmas.kpc_opt
(array_value_of var_key_out)
(array_value_of var_parent_out)
(array_value_of var_weights)
(SizeT.v var_n)
(SizeT.v var_source)))
  ensures (with_pure (return_1 `SizeT.lt` var_n))
{
  let mut var_key_out = var_key_out;
  let mut var_in_mst = var_in_mst;
  let mut var_n = var_n;
  let mut var_parent_out = var_parent_out;
  let mut var_weights = var_weights;
  let mut var_weights_len = var_weights_len;
  let mut var_source = var_source;
  let mut var_u : SizeT.t;
  var_u := 0sz;
  let mut var_min_key : SizeT.t;
  var_min_key := 65535sz;
  let mut var_j : SizeT.t;
  var_j := 0sz;
  while (((!var_j) `SizeT.lt` (!var_n)))
    invariant (((live var_j) ** (live var_u)) ** (live var_min_key))
    invariant ((Pulse.Lib.C.Array.live_array (!var_key_out)) **
        (Pulse.Lib.C.Array.live_array (!var_in_mst)))
    invariant ((Pulse.Lib.C.Array.live_array (!var_parent_out)) **
        (Pulse.Lib.C.Array.live_array (!var_weights)))
    invariant (with_pure
        (((reveal (length_of (!var_key_out))) = (SizeT.v (!var_n))) &&
          ((reveal (length_of (!var_in_mst))) = (SizeT.v (!var_n)))))
    invariant (with_pure
        (((reveal (length_of (!var_parent_out))) = (SizeT.v (!var_n))) &&
          ((reveal (length_of (!var_weights))) = (SizeT.v (!var_weights_len)))))
    invariant (with_pure
        ((((!var_j) `SizeT.lte` (!var_n)) && (0 < (SizeT.v (!var_n)))) &&
          ((!var_source) `SizeT.lt` (!var_n))))
    invariant (with_pure ((!var_u) `SizeT.lt` (!var_n)))
    invariant (with_pure ((!var_min_key) `SizeT.lte` 65535sz))
    invariant (with_pure
        (forall
          (var_v: SizeT.t).
          ((var_v `SizeT.lt` (!var_n)) ==>
            (((array_read (!var_key_out) var_v)) `SizeT.lte` 65535sz))))
    invariant (with_pure
        (forall
          (var_v: SizeT.t).
          ((var_v `SizeT.lt` (!var_n)) ==>
            (((array_read (!var_parent_out) var_v)) `SizeT.lt` (!var_n)))))
    invariant (with_pure (SizeT.v (!var_weights_len) = SizeT.v (!var_n) * SizeT.v (!var_n)))
    invariant (with_pure
        (CLRS.Ch23.Prim.C.BridgeLemmas.kpc_opt
(array_value_of (!var_key_out))
(array_value_of (!var_parent_out))
(array_value_of (!var_weights))
(SizeT.v (!var_n))
(SizeT.v (!var_source))))
  {
    if (((((array_read (!var_in_mst) (!var_j))) = 0sz) &&
          (((array_read (!var_key_out) (!var_j))) `SizeT.lte` (!var_min_key)))) {
      var_min_key := ((array_read (!var_key_out) (!var_j)));
      var_u := (!var_j);
    } else {};
    var_j := ((!var_j) `SizeT.add` 1sz);
  };
  return (!var_u);
}

#restart-solver

fn func_compute_base (var_u: SizeT.t) (var_n: SizeT.t) (var_weights_len: SizeT.t)
  requires (with_pure ((var_u `SizeT.lt` var_n) && (0 < (SizeT.v var_n))))
  requires (with_pure (SizeT.v var_weights_len = SizeT.v var_n * SizeT.v var_n))
  returns return_1 : SizeT.t
  ensures (with_pure (SizeT.v return_1 = SizeT.v var_u * SizeT.v var_n))
  ensures (with_pure (return_1 `SizeT.lte` var_weights_len))
{
  let mut var_u = var_u;
  let mut var_n = var_n;
  let mut var_weights_len = var_weights_len;
  let mut var_base : SizeT.t;
  var_base := 0sz;
  let mut var_k : SizeT.t;
  var_k := 0sz;
  while (((!var_k) `SizeT.lt` (!var_u)))
    invariant ((live var_k) ** (live var_base))
    invariant (with_pure (SizeT.v (!var_base) = SizeT.v (!var_k) * SizeT.v (!var_n)))
    invariant (with_pure (SizeT.v (!var_weights_len) = SizeT.v (!var_n) * SizeT.v (!var_n)))
    invariant (with_pure
        ((((!var_k) `SizeT.lte` (!var_u)) && ((!var_u) `SizeT.lt` (!var_n))) &&
          (0 < (SizeT.v (!var_n)))))
    invariant (with_pure ((!var_base) `SizeT.lte` (!var_weights_len)))
  {
    NLArith.base_bound (SizeT.v (!var_k)) (SizeT.v (!var_n));
    var_base := ((!var_base) `SizeT.add` (!var_n));
    var_k := ((!var_k) `SizeT.add` 1sz);
  };
  return (!var_base);
}

#restart-solver

fn func_update_keys
    (var_weights: (array SizeT.t))
    (var_weights_len: SizeT.t)
    (var_key_out: (array SizeT.t))
    (var_parent_out: (array SizeT.t))
    (var_in_mst: (array SizeT.t))
    (var_n: SizeT.t)
    (var_u: SizeT.t)
    (var_base: SizeT.t)
    (var_source: SizeT.t)
  requires
    exists* (val_weights_0: (Seq.seq (option SizeT.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  requires
    exists* (val_key_out_0: (Seq.seq (option SizeT.t))) (val_key_out_1: (nat->prop)).
    ((array_pts_to var_key_out 1.0R val_key_out_0 val_key_out_1))
  requires
    exists* (val_parent_out_0: (Seq.seq (option SizeT.t))) (val_parent_out_1: (nat->prop)).
    ((array_pts_to var_parent_out 1.0R val_parent_out_0 val_parent_out_1))
  requires
    exists* (val_in_mst_0: (Seq.seq (option SizeT.t))) (val_in_mst_1: (nat->prop)).
    ((array_pts_to var_in_mst 1.0R val_in_mst_0 val_in_mst_1))
  requires
    (with_pure
      (((0 < (SizeT.v var_n)) && (var_u `SizeT.lt` var_n)) && (var_source `SizeT.lt` var_n)))
  requires (with_pure ((reveal (length_of var_weights)) = (SizeT.v var_weights_len)))
  requires (with_pure (SizeT.v var_weights_len = SizeT.v var_n * SizeT.v var_n))
  requires (with_pure (SizeT.v var_base = SizeT.v var_u * SizeT.v var_n))
  requires (with_pure (SizeT.v var_base + SizeT.v var_n <= SizeT.v var_weights_len))
  requires
    (with_pure
      ((((reveal (length_of var_key_out)) = (SizeT.v var_n)) &&
          ((reveal (length_of var_parent_out)) = (SizeT.v var_n)))
        &&
        ((reveal (length_of var_in_mst)) = (SizeT.v var_n))))
  requires
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==> (((array_read var_key_out var_v)) `SizeT.lte` 65535sz))))
  requires
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==> (((array_read var_parent_out var_v)) `SizeT.lt` var_n))))
  requires
    (with_pure
      (CLRS.Ch23.Prim.C.BridgeLemmas.kpc_opt
(array_value_of var_key_out)
(array_value_of var_parent_out)
(array_value_of var_weights)
(SizeT.v var_n)
(SizeT.v var_source)))
  returns return_1 : unit
  ensures
    exists* (val_weights_0: (Seq.seq (option SizeT.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  ensures
    exists* (val_key_out_0: (Seq.seq (option SizeT.t))) (val_key_out_1: (nat->prop)).
    ((array_pts_to var_key_out 1.0R val_key_out_0 val_key_out_1))
  ensures
    exists* (val_parent_out_0: (Seq.seq (option SizeT.t))) (val_parent_out_1: (nat->prop)).
    ((array_pts_to var_parent_out 1.0R val_parent_out_0 val_parent_out_1))
  ensures
    exists* (val_in_mst_0: (Seq.seq (option SizeT.t))) (val_in_mst_1: (nat->prop)).
    ((array_pts_to var_in_mst 1.0R val_in_mst_0 val_in_mst_1))
  ensures
    (with_pure
      ((((reveal (length_of var_key_out)) = (SizeT.v var_n)) &&
          ((reveal (length_of var_parent_out)) = (SizeT.v var_n)))
        &&
        ((reveal (length_of var_in_mst)) = (SizeT.v var_n))))
  ensures (with_pure ((reveal (length_of var_weights)) = (SizeT.v var_weights_len)))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==> (((array_read var_key_out var_v)) `SizeT.lte` 65535sz))))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==> (((array_read var_parent_out var_v)) `SizeT.lt` var_n))))
  ensures
    (with_pure
      (CLRS.Ch23.Prim.C.BridgeLemmas.kpc_opt
(array_value_of var_key_out)
(array_value_of var_parent_out)
(array_value_of var_weights)
(SizeT.v var_n)
(SizeT.v var_source)))
{
  let mut var_weights = var_weights;
  let mut var_weights_len = var_weights_len;
  let mut var_key_out = var_key_out;
  let mut var_parent_out = var_parent_out;
  let mut var_in_mst = var_in_mst;
  let mut var_n = var_n;
  let mut var_u = var_u;
  let mut var_base = var_base;
  let mut var_source = var_source;
  let mut var_idx : SizeT.t;
  var_idx := (!var_base);
  let mut var_v : SizeT.t;
  var_v := 0sz;
  while (((!var_v) `SizeT.lt` (!var_n)))
    invariant ((live var_v) ** (live var_idx))
    invariant ((Pulse.Lib.C.Array.live_array (!var_key_out)) **
        (Pulse.Lib.C.Array.live_array (!var_parent_out)))
    invariant ((Pulse.Lib.C.Array.live_array (!var_weights)) **
        (Pulse.Lib.C.Array.live_array (!var_in_mst)))
    invariant (with_pure
        (((reveal (length_of (!var_key_out))) = (SizeT.v (!var_n))) &&
          ((reveal (length_of (!var_parent_out))) = (SizeT.v (!var_n)))))
    invariant (with_pure
        (((reveal (length_of (!var_weights))) = (SizeT.v (!var_weights_len))) &&
          ((reveal (length_of (!var_in_mst))) = (SizeT.v (!var_n)))))
    invariant (with_pure (SizeT.v (!var_weights_len) = SizeT.v (!var_n) * SizeT.v (!var_n)))
    invariant (with_pure (SizeT.v (!var_idx) = SizeT.v (!var_base) + SizeT.v (!var_v)))
    invariant (with_pure (SizeT.v (!var_base) = SizeT.v (!var_u) * SizeT.v (!var_n)))
    invariant (with_pure (SizeT.v (!var_base) + SizeT.v (!var_n) <= SizeT.v (!var_weights_len)))
    invariant (with_pure
        (((((!var_v) `SizeT.lte` (!var_n)) && (0 < (SizeT.v (!var_n)))) &&
            ((!var_u) `SizeT.lt` (!var_n)))
          &&
          ((!var_source) `SizeT.lt` (!var_n))))
    invariant (with_pure (Pulse.Lib.C.Array.array_initialized (array_value_of (!var_weights))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_n)) ==>
            (((array_read (!var_key_out) var_j)) `SizeT.lte` 65535sz))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_n)) ==>
            (((array_read (!var_parent_out) var_j)) `SizeT.lt` (!var_n)))))
    invariant (with_pure
        (CLRS.Ch23.Prim.C.BridgeLemmas.kpc_opt
(array_value_of (!var_key_out))
(array_value_of (!var_parent_out))
(array_value_of (!var_weights))
(SizeT.v (!var_n))
(SizeT.v (!var_source))))
  {
    let mut var_w_uv : SizeT.t;
    var_w_uv := ((array_read (!var_weights) (!var_idx)));
    NLArith.index_bound (SizeT.v (!var_u)) (SizeT.v (!var_v)) (SizeT.v (!var_n));
    CLRS.Ch23.Prim.C.BridgeLemmas.kpc_opt_step
(array_value_of (!var_key_out))
(array_value_of (!var_parent_out))
(array_value_of (!var_weights))
(SizeT.v (!var_n))
(SizeT.v (!var_source))
(!var_u) (!var_v) (!var_w_uv);
    if ((((((array_read (!var_in_mst) (!var_v))) = 0sz) && (0sz `SizeT.lt` (!var_w_uv))) &&
          ((!var_w_uv) `SizeT.lt` ((array_read (!var_key_out) (!var_v)))))) {
      (array_write (!var_key_out) (!var_v) (!var_w_uv));
      (array_write (!var_parent_out) (!var_v) (!var_u));
    } else {};
    var_idx := ((!var_idx) `SizeT.add` 1sz);
    var_v := ((!var_v) `SizeT.add` 1sz);
  };
}

#restart-solver

fn func_prim
    (var_weights: (array SizeT.t))
    (var_weights_len: SizeT.t)
    (var_n: SizeT.t)
    (var_source: SizeT.t)
    (var_key_out: (array SizeT.t))
    (var_parent_out: (array SizeT.t))
  requires
    exists* (val_weights_0: (Seq.seq (option SizeT.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  requires
    exists* (val_key_out_0: (Seq.seq (option SizeT.t))) (val_key_out_1: (nat->prop)).
    ((array_pts_to var_key_out 1.0R val_key_out_0 val_key_out_1))
  requires
    exists* (val_parent_out_0: (Seq.seq (option SizeT.t))) (val_parent_out_1: (nat->prop)).
    ((array_pts_to var_parent_out 1.0R val_parent_out_0 val_parent_out_1))
  requires
    (with_pure
      ((((reveal (length_of var_weights)) = (SizeT.v var_weights_len)) && (0 < (SizeT.v var_n))) &&
        (var_source `SizeT.lt` var_n)))
  requires (with_pure (SizeT.v var_weights_len = SizeT.v var_n * SizeT.v var_n))
  requires
    (with_pure
      (((reveal (length_of var_key_out)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_parent_out)) = (SizeT.v var_n))))
  returns return_1 : unit
  ensures
    exists* (val_weights_0: (Seq.seq (option SizeT.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  ensures
    exists* (val_key_out_0: (Seq.seq (option SizeT.t))) (val_key_out_1: (nat->prop)).
    ((array_pts_to var_key_out 1.0R val_key_out_0 val_key_out_1))
  ensures
    exists* (val_parent_out_0: (Seq.seq (option SizeT.t))) (val_parent_out_1: (nat->prop)).
    ((array_pts_to var_parent_out 1.0R val_parent_out_0 val_parent_out_1))
  ensures (with_pure ((reveal (length_of var_weights)) = (SizeT.v var_weights_len)))
  ensures
    (with_pure
      (((reveal (length_of var_key_out)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_parent_out)) = (SizeT.v var_n))))
  ensures (with_pure ((SizeT.v ((array_read var_key_out var_source))) = 0))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==> (((array_read var_key_out var_v)) `SizeT.lte` 65535sz))))
  ensures (with_pure (((array_read var_parent_out var_source)) = var_source))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==> (((array_read var_parent_out var_v)) `SizeT.lt` var_n))))
  ensures
    (with_pure
      (CLRS.Ch23.Prim.Impl.prim_correct
(CLRS.Ch23.Prim.C.BridgeLemmas.unwrap_sizet_seq (array_value_of var_key_out) (SizeT.v var_n))
(CLRS.Ch23.Prim.C.BridgeLemmas.unwrap_sizet_seq (array_value_of var_parent_out) (SizeT.v var_n))
(CLRS.Ch23.Prim.C.BridgeLemmas.unwrap_sizet_seq (array_value_of var_weights) (SizeT.v var_n `op_Multiply` SizeT.v var_n))
(SizeT.v var_n)
(SizeT.v var_source)))
{
  let mut var_weights = var_weights;
  let mut var_weights_len = var_weights_len;
  let mut var_n = var_n;
  let mut var_source = var_source;
  let mut var_key_out = var_key_out;
  let mut var_parent_out = var_parent_out;
  let mut var_v : SizeT.t;
  var_v := 0sz;
  while (((!var_v) `SizeT.lt` (!var_n)))
    invariant (live var_v)
    invariant (((Pulse.Lib.C.Array.live_array (!var_key_out)) **
          (Pulse.Lib.C.Array.live_array (!var_parent_out)))
        **
        (Pulse.Lib.C.Array.live_array (!var_weights)))
    invariant (with_pure
        (((reveal (length_of (!var_key_out))) = (SizeT.v (!var_n))) &&
          ((reveal (length_of (!var_parent_out))) = (SizeT.v (!var_n)))))
    invariant (with_pure ((reveal (length_of (!var_weights))) = (SizeT.v (!var_weights_len))))
    invariant (with_pure
        ((((!var_v) `SizeT.lte` (!var_n)) && (0 < (SizeT.v (!var_n)))) &&
          ((!var_source) `SizeT.lt` (!var_n))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_v)) ==> (((array_read (!var_key_out) var_j)) = 65535sz))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_v)) ==>
            (((array_read (!var_key_out) var_j)) `SizeT.lte` 65535sz))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_v)) ==>
            (((array_read (!var_parent_out) var_j)) = (!var_source)))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_v)) ==>
            (((array_read (!var_parent_out) var_j)) `SizeT.lt` (!var_n)))))
    invariant (with_pure
        (forall (vi: nat). vi < SizeT.v (!var_v) ==>
Seq.index (array_value_of (!var_key_out)) vi == Some 65535sz))
  {
    (array_write (!var_key_out) (!var_v) 65535sz);
    (array_write (!var_parent_out) (!var_v) (!var_source));
    var_v := ((!var_v) `SizeT.add` 1sz);
  };
  CLRS.Ch23.Prim.C.BridgeLemmas.kpc_opt_init
(array_value_of (!var_key_out))
(array_value_of (!var_parent_out))
(array_value_of (!var_weights))
(SizeT.v (!var_n))
(SizeT.v (!var_source));
  CLRS.Ch23.Prim.C.BridgeLemmas.kpc_opt_write_source_key
(array_value_of (!var_key_out))
(array_value_of (!var_parent_out))
(array_value_of (!var_weights))
(SizeT.v (!var_n))
(SizeT.v (!var_source))
0sz;
  (array_write (!var_key_out) (!var_source) 0sz);
  let mut var_in_mst : (array SizeT.t);
  var_in_mst := (Pulse.Lib.C.Array.calloc_array_mask #SizeT.t (!var_n));
  assert (with_pure ((reveal (length_of (!var_in_mst))) = (SizeT.v (!var_n))));
  let mut var_iter : SizeT.t;
  var_iter := 0sz;
  while (((!var_iter) `SizeT.lt` (!var_n)))
    invariant (live var_iter)
    invariant ((Pulse.Lib.C.Array.live_array (!var_key_out)) **
        (Pulse.Lib.C.Array.live_array (!var_parent_out)))
    invariant ((Pulse.Lib.C.Array.live_array (!var_weights)) **
        (Pulse.Lib.C.Array.live_array (!var_in_mst)))
    invariant (with_pure
        (((reveal (length_of (!var_key_out))) = (SizeT.v (!var_n))) &&
          ((reveal (length_of (!var_parent_out))) = (SizeT.v (!var_n)))))
    invariant (with_pure
        (((reveal (length_of (!var_weights))) = (SizeT.v (!var_weights_len))) &&
          ((reveal (length_of (!var_in_mst))) = (SizeT.v (!var_n)))))
    invariant (with_pure (SizeT.v (!var_weights_len) = SizeT.v (!var_n) * SizeT.v (!var_n)))
    invariant (with_pure
        ((((!var_iter) `SizeT.lte` (!var_n)) && (0 < (SizeT.v (!var_n)))) &&
          ((!var_source) `SizeT.lt` (!var_n))))
    invariant (with_pure
        (forall
          (var_v: SizeT.t).
          ((var_v `SizeT.lt` (!var_n)) ==>
            (((array_read (!var_key_out) var_v)) `SizeT.lte` 65535sz))))
    invariant (with_pure
        (forall
          (var_v: SizeT.t).
          ((var_v `SizeT.lt` (!var_n)) ==>
            (((array_read (!var_parent_out) var_v)) `SizeT.lt` (!var_n)))))
    invariant (with_pure
        (CLRS.Ch23.Prim.C.BridgeLemmas.kpc_opt
(array_value_of (!var_key_out))
(array_value_of (!var_parent_out))
(array_value_of (!var_weights))
(SizeT.v (!var_n))
(SizeT.v (!var_source))))
  {
    let mut var_u : SizeT.t;
    var_u :=
      (func_extract_min
        (!var_key_out)
        (!var_in_mst)
        (!var_n)
        (!var_parent_out)
        (!var_weights)
        (!var_weights_len)
        (!var_source));
    (array_write (!var_in_mst) (!var_u) 1sz);
    let mut var_base : SizeT.t;
    var_base := (func_compute_base (!var_u) (!var_n) (!var_weights_len));
    NLArith.base_bound (SizeT.v (!var_u)) (SizeT.v (!var_n));
    (func_update_keys
        (!var_weights)
        (!var_weights_len)
        (!var_key_out)
        (!var_parent_out)
        (!var_in_mst)
        (!var_n)
        (!var_u)
        (!var_base)
        (!var_source));
    var_iter := ((!var_iter) `SizeT.add` 1sz);
  };
  CLRS.Ch23.Prim.C.BridgeLemmas.kpc_opt_write_source_key
(array_value_of (!var_key_out))
(array_value_of (!var_parent_out))
(array_value_of (!var_weights))
(SizeT.v (!var_n))
(SizeT.v (!var_source))
0sz;
  (array_write (!var_key_out) (!var_source) 0sz);
  CLRS.Ch23.Prim.C.BridgeLemmas.kpc_opt_write_source_parent
(array_value_of (!var_key_out))
(array_value_of (!var_parent_out))
(array_value_of (!var_weights))
(SizeT.v (!var_n))
(SizeT.v (!var_source))
(!var_source);
  (array_write (!var_parent_out) (!var_source) (!var_source));
  CLRS.Ch23.Prim.C.BridgeLemmas.keys_bounded_nat
(array_value_of (!var_key_out))
(!var_n);
  CLRS.Ch23.Prim.C.BridgeLemmas.parents_valid_nat
(array_value_of (!var_parent_out))
(!var_n);
  CLRS.Ch23.Prim.C.BridgeLemmas.prim_correct_assembly
(array_value_of (!var_key_out))
(array_value_of (!var_parent_out))
(array_value_of (!var_weights))
(SizeT.v (!var_n))
(SizeT.v (!var_source));
  (Pulse.Lib.C.Array.free_array (!var_in_mst));
}