module Kruskal
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

open CLRS.Ch23.Kruskal.C.BridgeLemmas

#restart-solver

open CLRS.Ch23.Kruskal.Impl

#restart-solver

fn rec func_uf_find
    (var_parent: (array SizeT.t))
    (var_n: SizeT.t)
    (var_v: SizeT.t)
    (var_fuel: SizeT.t)
  requires
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  requires (with_pure ((reveal (length_of var_parent)) = (SizeT.v var_n)))
  requires
    (with_pure
      (((0 < (SizeT.v var_n)) && (var_v `SizeT.lt` var_n)) && (var_fuel `SizeT.lte` var_n)))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  returns return_1 : SizeT.t
  ensures
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  ensures (with_pure ((reveal (length_of var_parent)) = (SizeT.v var_n)))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  ensures (with_pure (return_1 `SizeT.lt` var_n))
  decreases (SizeT.v var_fuel)
{
  let mut var_parent = var_parent;
  let mut var_n = var_n;
  let mut var_v = var_v;
  let mut var_fuel = var_fuel;
  if (((!var_fuel) = 0sz)) {
    return (!var_v);
  } else {};
  let mut var_p : SizeT.t;
  var_p := ((array_read (!var_parent) (!var_v)));
  return (func_uf_find (!var_parent) (!var_n) (!var_p) ((!var_fuel) `SizeT.sub` 1sz));
}

#restart-solver

fn func_compute_roots (var_parent: (array SizeT.t)) (var_n: SizeT.t) (var_roots: (array SizeT.t))
  requires
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  requires
    exists* (val_roots_0: (Seq.seq (option SizeT.t))) (val_roots_1: (nat->prop)).
    ((array_pts_to var_roots 1.0R val_roots_0 val_roots_1))
  requires (with_pure (0 < (SizeT.v var_n)))
  requires (with_pure ((reveal (length_of var_parent)) = (SizeT.v var_n)))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  requires (with_pure ((reveal (length_of var_roots)) = (SizeT.v var_n)))
  returns return_1 : unit
  ensures
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  ensures
    exists* (val_roots_0: (Seq.seq (option SizeT.t))) (val_roots_1: (nat->prop)).
    ((array_pts_to var_roots 1.0R val_roots_0 val_roots_1))
  ensures (with_pure ((reveal (length_of var_parent)) = (SizeT.v var_n)))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  ensures (with_pure ((reveal (length_of var_roots)) = (SizeT.v var_n)))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_roots var_i)) `SizeT.lt` var_n))))
{
  let mut var_parent = var_parent;
  let mut var_n = var_n;
  let mut var_roots = var_roots;
  let mut var_i : SizeT.t;
  var_i := 0sz;
  while (((!var_i) `SizeT.lt` (!var_n)))
    invariant (live var_i)
    invariant ((Pulse.Lib.C.Array.live_array (!var_parent)) **
        (Pulse.Lib.C.Array.live_array (!var_roots)))
    invariant (with_pure
        (((reveal (length_of (!var_parent))) = (SizeT.v (!var_n))) &&
          ((reveal (length_of (!var_roots))) = (SizeT.v (!var_n)))))
    invariant (with_pure (((!var_i) `SizeT.lte` (!var_n)) && (0 < (SizeT.v (!var_n)))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_n)) ==>
            (((array_read (!var_parent) var_j)) `SizeT.lt` (!var_n)))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_i)) ==>
            (((array_read (!var_roots) var_j)) `SizeT.lt` (!var_n)))))
  {
    (array_write (!var_roots) (!var_i) (func_uf_find (!var_parent) (!var_n) (!var_i) (!var_n)));
    var_i := ((!var_i) `SizeT.add` 1sz);
  };
}

#restart-solver

fn func_scan_row
    (var_adj: (array Int32.t))
    (var_adj_len: SizeT.t)
    (var_roots: (array SizeT.t))
    (var_n: SizeT.t)
    (var_u: SizeT.t)
    (var_base: SizeT.t)
    (var_out_u: (ref SizeT.t))
    (var_out_v: (ref SizeT.t))
    (var_out_w: (ref Int32.t))
  requires
    exists* (val_adj_0: (Seq.seq (option Int32.t))) (val_adj_1: (nat->prop)).
    ((array_pts_to var_adj 1.0R val_adj_0 val_adj_1))
  requires
    exists* (val_roots_0: (Seq.seq (option SizeT.t))) (val_roots_1: (nat->prop)).
    ((array_pts_to var_roots 1.0R val_roots_0 val_roots_1))
  requires exists* (val_out_u_0: SizeT.t). ((pts_to var_out_u #1.0R val_out_u_0))
  requires exists* (val_out_v_0: SizeT.t). ((pts_to var_out_v #1.0R val_out_v_0))
  requires exists* (val_out_w_0: Int32.t). ((pts_to var_out_w #1.0R val_out_w_0))
  requires (with_pure ((1 < (SizeT.v var_n)) && (var_u `SizeT.lt` var_n)))
  requires
    (with_pure
      (((reveal (length_of var_adj)) = (SizeT.v var_adj_len)) &&
        ((reveal (length_of var_roots)) = (SizeT.v var_n))))
  requires (with_pure (SizeT.v var_adj_len = SizeT.v var_n * SizeT.v var_n))
  requires (with_pure (SizeT.v var_base = SizeT.v var_u * SizeT.v var_n))
  requires (with_pure (SizeT.v var_base + SizeT.v var_n <= SizeT.v var_adj_len))
  requires (with_pure (((!var_out_u) `SizeT.lt` var_n) && ((!var_out_v) `SizeT.lt` var_n)))
  requires (with_pure (0 <= (id #int (Int32.v (!var_out_w)))))
  returns return_1 : unit
  ensures
    exists* (val_adj_0: (Seq.seq (option Int32.t))) (val_adj_1: (nat->prop)).
    ((array_pts_to var_adj 1.0R val_adj_0 val_adj_1))
  ensures
    exists* (val_roots_0: (Seq.seq (option SizeT.t))) (val_roots_1: (nat->prop)).
    ((array_pts_to var_roots 1.0R val_roots_0 val_roots_1))
  ensures exists* (val_out_u_0: SizeT.t). ((pts_to var_out_u #1.0R val_out_u_0))
  ensures exists* (val_out_v_0: SizeT.t). ((pts_to var_out_v #1.0R val_out_v_0))
  ensures exists* (val_out_w_0: Int32.t). ((pts_to var_out_w #1.0R val_out_w_0))
  ensures (with_pure (((!var_out_u) `SizeT.lt` var_n) && ((!var_out_v) `SizeT.lt` var_n)))
  ensures (with_pure (0 <= (id #int (Int32.v (!var_out_w)))))
  ensures
    (with_pure
      (((reveal (length_of var_adj)) = (SizeT.v var_adj_len)) &&
        ((reveal (length_of var_roots)) = (SizeT.v var_n))))
{
  let mut var_adj = var_adj;
  let mut var_adj_len = var_adj_len;
  let mut var_roots = var_roots;
  let mut var_n = var_n;
  let mut var_u = var_u;
  let mut var_base = var_base;
  let mut var_out_u = var_out_u;
  let mut var_out_v = var_out_v;
  let mut var_out_w = var_out_w;
  let mut var_root_u : SizeT.t;
  var_root_u := ((array_read (!var_roots) (!var_u)));
  let mut var_idx : SizeT.t;
  var_idx := (!var_base);
  let mut var_v : SizeT.t;
  var_v := 0sz;
  while (((!var_v) `SizeT.lt` (!var_n)))
    invariant (((live var_v) ** (live var_idx)) ** (live var_root_u))
    invariant (((live (!var_out_u)) ** (live (!var_out_v))) ** (live (!var_out_w)))
    invariant ((Pulse.Lib.C.Array.live_array (!var_roots)) **
        (Pulse.Lib.C.Array.live_array (!var_adj)))
    invariant (with_pure
        (((reveal (length_of (!var_roots))) = (SizeT.v (!var_n))) &&
          ((reveal (length_of (!var_adj))) = (SizeT.v (!var_adj_len)))))
    invariant (with_pure (SizeT.v (!var_adj_len) = SizeT.v (!var_n) * SizeT.v (!var_n)))
    invariant (with_pure (SizeT.v (!var_idx) = SizeT.v (!var_base) + SizeT.v (!var_v)))
    invariant (with_pure (SizeT.v (!var_base) + SizeT.v (!var_n) <= SizeT.v (!var_adj_len)))
    invariant (with_pure
        ((((!var_v) `SizeT.lte` (!var_n)) && (1 < (SizeT.v (!var_n)))) &&
          ((!var_u) `SizeT.lt` (!var_n))))
    invariant (with_pure
        (((!(!var_out_u)) `SizeT.lt` (!var_n)) && ((!(!var_out_v)) `SizeT.lt` (!var_n))))
    invariant (with_pure (0 <= (id #int (Int32.v (!(!var_out_w))))))
  {
    let mut var_w : Int32.t;
    var_w := ((array_read (!var_adj) (!var_idx)));
    let mut var_root_v : SizeT.t;
    var_root_v := ((array_read (!var_roots) (!var_v)));
    if (((((Int32.int_to_t 0) `Int32.lt` (!var_w)) && (not ((!var_root_u) = (!var_root_v)))) &&
          (((!(!var_out_w)) = (Int32.int_to_t 0)) || ((!var_w) `Int32.lt` (!(!var_out_w)))))) {
      (!var_out_u) := (!var_u);
      (!var_out_v) := (!var_v);
      (!var_out_w) := (!var_w);
    } else {};
    var_idx := ((!var_idx) `SizeT.add` 1sz);
    var_v := ((!var_v) `SizeT.add` 1sz);
  };
}

#restart-solver

fn func_find_min_edge
    (var_adj: (array Int32.t))
    (var_adj_len: SizeT.t)
    (var_parent: (array SizeT.t))
    (var_n: SizeT.t)
    (var_out_u: (ref SizeT.t))
    (var_out_v: (ref SizeT.t))
    (var_out_w: (ref Int32.t))
  requires
    exists* (val_adj_0: (Seq.seq (option Int32.t))) (val_adj_1: (nat->prop)).
    ((array_pts_to var_adj 1.0R val_adj_0 val_adj_1))
  requires
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  requires exists* (val_out_u_0: SizeT.t). ((pts_to var_out_u #1.0R val_out_u_0))
  requires exists* (val_out_v_0: SizeT.t). ((pts_to var_out_v #1.0R val_out_v_0))
  requires exists* (val_out_w_0: Int32.t). ((pts_to var_out_w #1.0R val_out_w_0))
  requires
    (with_pure
      (((reveal (length_of var_adj)) = (SizeT.v var_adj_len)) &&
        ((reveal (length_of var_parent)) = (SizeT.v var_n))))
  requires (with_pure (1 < (SizeT.v var_n)))
  requires (with_pure (SizeT.v var_adj_len = SizeT.v var_n * SizeT.v var_n))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  returns return_1 : unit
  ensures
    exists* (val_adj_0: (Seq.seq (option Int32.t))) (val_adj_1: (nat->prop)).
    ((array_pts_to var_adj 1.0R val_adj_0 val_adj_1))
  ensures
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  ensures exists* (val_out_u_0: SizeT.t). ((pts_to var_out_u #1.0R val_out_u_0))
  ensures exists* (val_out_v_0: SizeT.t). ((pts_to var_out_v #1.0R val_out_v_0))
  ensures exists* (val_out_w_0: Int32.t). ((pts_to var_out_w #1.0R val_out_w_0))
  ensures
    (with_pure
      (((reveal (length_of var_adj)) = (SizeT.v var_adj_len)) &&
        ((reveal (length_of var_parent)) = (SizeT.v var_n))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  ensures (with_pure (((!var_out_u) `SizeT.lt` var_n) && ((!var_out_v) `SizeT.lt` var_n)))
  ensures (with_pure (0 <= (id #int (Int32.v (!var_out_w)))))
{
  let mut var_adj = var_adj;
  let mut var_adj_len = var_adj_len;
  let mut var_parent = var_parent;
  let mut var_n = var_n;
  let mut var_out_u = var_out_u;
  let mut var_out_v = var_out_v;
  let mut var_out_w = var_out_w;
  (!var_out_u) := 0sz;
  (!var_out_v) := 0sz;
  (!var_out_w) := (Int32.int_to_t 0);
  let mut var_roots : (array SizeT.t);
  var_roots := (Pulse.Lib.C.Array.calloc_array_mask #SizeT.t (!var_n));
  assert (with_pure ((reveal (length_of (!var_roots))) = (SizeT.v (!var_n))));
  (func_compute_roots (!var_parent) (!var_n) (!var_roots));
  let mut var_base : SizeT.t;
  var_base := 0sz;
  let mut var_u : SizeT.t;
  var_u := 0sz;
  while (((!var_u) `SizeT.lt` (!var_n)))
    invariant ((live var_u) ** (live var_base))
    invariant (((live (!var_out_u)) ** (live (!var_out_v))) ** (live (!var_out_w)))
    invariant (((Pulse.Lib.C.Array.live_array (!var_roots)) **
          (Pulse.Lib.C.Array.live_array (!var_adj)))
        **
        (Pulse.Lib.C.Array.live_array (!var_parent)))
    invariant (with_pure
        ((((reveal (length_of (!var_roots))) = (SizeT.v (!var_n))) &&
            ((reveal (length_of (!var_adj))) = (SizeT.v (!var_adj_len))))
          &&
          ((reveal (length_of (!var_parent))) = (SizeT.v (!var_n)))))
    invariant (with_pure (SizeT.v (!var_adj_len) = SizeT.v (!var_n) * SizeT.v (!var_n)))
    invariant (with_pure (SizeT.v (!var_base) = SizeT.v (!var_u) * SizeT.v (!var_n)))
    invariant (with_pure (((!var_u) `SizeT.lte` (!var_n)) && (1 < (SizeT.v (!var_n)))))
    invariant (with_pure ((!var_base) `SizeT.lte` (!var_adj_len)))
    invariant (with_pure
        (((!(!var_out_u)) `SizeT.lt` (!var_n)) && ((!(!var_out_v)) `SizeT.lt` (!var_n))))
    invariant (with_pure (0 <= (id #int (Int32.v (!(!var_out_w))))))
    invariant (with_pure
        (forall
          (var_i: SizeT.t).
          ((var_i `SizeT.lt` (!var_n)) ==>
            (((array_read (!var_parent) var_i)) `SizeT.lt` (!var_n)))))
  {
    NLArith.base_bound (SizeT.v (!var_u)) (SizeT.v (!var_n));
    (func_scan_row
        (!var_adj)
        (!var_adj_len)
        (!var_roots)
        (!var_n)
        (!var_u)
        (!var_base)
        (!var_out_u)
        (!var_out_v)
        (!var_out_w));
    var_base := ((!var_base) `SizeT.add` (!var_n));
    var_u := ((!var_u) `SizeT.add` 1sz);
  };
  (Pulse.Lib.C.Array.free_array (!var_roots));
}

#restart-solver

fn func_insert_edge
    (var_edge_u: (array SizeT.t))
    (var_edge_v: (array SizeT.t))
    (var_n: SizeT.t)
    (var_ec: SizeT.t)
    (var_u: SizeT.t)
    (var_v: SizeT.t)
  requires
    exists* (val_edge_u_0: (Seq.seq (option SizeT.t))) (val_edge_u_1: (nat->prop)).
    ((array_pts_to var_edge_u 1.0R val_edge_u_0 val_edge_u_1))
  requires
    exists* (val_edge_v_0: (Seq.seq (option SizeT.t))) (val_edge_v_1: (nat->prop)).
    ((array_pts_to var_edge_v 1.0R val_edge_v_0 val_edge_v_1))
  requires
    (with_pure
      (((var_ec `SizeT.lt` var_n) && (var_u `SizeT.lt` var_n)) && (var_v `SizeT.lt` var_n)))
  requires
    (with_pure
      (((reveal (length_of var_edge_u)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_edge_v)) = (SizeT.v var_n))))
  requires
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((var_k `SizeT.lt` var_ec) ==> (((array_read var_edge_u var_k)) `SizeT.lt` var_n))))
  requires
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((var_k `SizeT.lt` var_ec) ==> (((array_read var_edge_v var_k)) `SizeT.lt` var_n))))
  returns return_1 : unit
  ensures
    exists* (val_edge_u_0: (Seq.seq (option SizeT.t))) (val_edge_u_1: (nat->prop)).
    ((array_pts_to var_edge_u 1.0R val_edge_u_0 val_edge_u_1))
  ensures
    exists* (val_edge_v_0: (Seq.seq (option SizeT.t))) (val_edge_v_1: (nat->prop)).
    ((array_pts_to var_edge_v 1.0R val_edge_v_0 val_edge_v_1))
  ensures
    (with_pure
      (((reveal (length_of var_edge_u)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_edge_v)) = (SizeT.v var_n))))
  ensures
    (with_pure
      (forall
        (var_k: SizeT.t).
        (((SizeT.v var_k) < ((SizeT.v var_ec) + 1)) ==>
          (((array_read var_edge_u var_k)) `SizeT.lt` var_n))))
  ensures
    (with_pure
      (forall
        (var_k: SizeT.t).
        (((SizeT.v var_k) < ((SizeT.v var_ec) + 1)) ==>
          (((array_read var_edge_v var_k)) `SizeT.lt` var_n))))
{
  let mut var_edge_u = var_edge_u;
  let mut var_edge_v = var_edge_v;
  let mut var_n = var_n;
  let mut var_ec = var_ec;
  let mut var_u = var_u;
  let mut var_v = var_v;
  (array_write (!var_edge_u) (!var_ec) (!var_u));
  (array_write (!var_edge_v) (!var_ec) (!var_v));
}

#restart-solver

fn func_try_add_edge
    (var_adj: (array Int32.t))
    (var_adj_len: SizeT.t)
    (var_parent: (array SizeT.t))
    (var_n: SizeT.t)
    (var_edge_u: (array SizeT.t))
    (var_edge_v: (array SizeT.t))
    (var_edge_count: (ref SizeT.t))
    (var_round: SizeT.t)
  requires
    exists* (val_adj_0: (Seq.seq (option Int32.t))) (val_adj_1: (nat->prop)).
    ((array_pts_to var_adj 1.0R val_adj_0 val_adj_1))
  requires
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  requires
    exists* (val_edge_u_0: (Seq.seq (option SizeT.t))) (val_edge_u_1: (nat->prop)).
    ((array_pts_to var_edge_u 1.0R val_edge_u_0 val_edge_u_1))
  requires
    exists* (val_edge_v_0: (Seq.seq (option SizeT.t))) (val_edge_v_1: (nat->prop)).
    ((array_pts_to var_edge_v 1.0R val_edge_v_0 val_edge_v_1))
  requires exists* (val_edge_count_0: SizeT.t). ((pts_to var_edge_count #1.0R val_edge_count_0))
  requires
    (with_pure
      (((reveal (length_of var_adj)) = (SizeT.v var_adj_len)) &&
        ((reveal (length_of var_parent)) = (SizeT.v var_n))))
  requires
    (with_pure
      (((reveal (length_of var_edge_u)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_edge_v)) = (SizeT.v var_n))))
  requires (with_pure (1 < (SizeT.v var_n)))
  requires (with_pure (SizeT.v var_adj_len = SizeT.v var_n * SizeT.v var_n))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  requires
    (with_pure
      (((!var_edge_count) `SizeT.lte` var_round) && (((SizeT.v var_round) + 1) < (SizeT.v var_n))))
  requires
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((var_k `SizeT.lt` (!var_edge_count)) ==>
          (((array_read var_edge_u var_k)) `SizeT.lt` var_n))))
  requires
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((var_k `SizeT.lt` (!var_edge_count)) ==>
          (((array_read var_edge_v var_k)) `SizeT.lt` var_n))))
  returns return_1 : unit
  ensures
    exists* (val_adj_0: (Seq.seq (option Int32.t))) (val_adj_1: (nat->prop)).
    ((array_pts_to var_adj 1.0R val_adj_0 val_adj_1))
  ensures
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  ensures
    exists* (val_edge_u_0: (Seq.seq (option SizeT.t))) (val_edge_u_1: (nat->prop)).
    ((array_pts_to var_edge_u 1.0R val_edge_u_0 val_edge_u_1))
  ensures
    exists* (val_edge_v_0: (Seq.seq (option SizeT.t))) (val_edge_v_1: (nat->prop)).
    ((array_pts_to var_edge_v 1.0R val_edge_v_0 val_edge_v_1))
  ensures exists* (val_edge_count_0: SizeT.t). ((pts_to var_edge_count #1.0R val_edge_count_0))
  ensures
    (with_pure
      (((reveal (length_of var_adj)) = (SizeT.v var_adj_len)) &&
        ((reveal (length_of var_parent)) = (SizeT.v var_n))))
  ensures
    (with_pure
      (((reveal (length_of var_edge_u)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_edge_v)) = (SizeT.v var_n))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  ensures
    (with_pure
      (((SizeT.v (!var_edge_count)) <= ((SizeT.v var_round) + 1)) &&
        ((!var_edge_count) `SizeT.lt` var_n)))
  ensures
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((var_k `SizeT.lt` (!var_edge_count)) ==>
          (((array_read var_edge_u var_k)) `SizeT.lt` var_n))))
  ensures
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((var_k `SizeT.lt` (!var_edge_count)) ==>
          (((array_read var_edge_v var_k)) `SizeT.lt` var_n))))
{
  let mut var_adj = var_adj;
  let mut var_adj_len = var_adj_len;
  let mut var_parent = var_parent;
  let mut var_n = var_n;
  let mut var_edge_u = var_edge_u;
  let mut var_edge_v = var_edge_v;
  let mut var_edge_count = var_edge_count;
  let mut var_round = var_round;
  let mut var_best_u : SizeT.t;
  var_best_u := 0sz;
  let mut var_best_v : SizeT.t;
  var_best_v := 0sz;
  let mut var_best_w : Int32.t;
  var_best_w := (Int32.int_to_t 0);
  (func_find_min_edge
      (!var_adj)
      (!var_adj_len)
      (!var_parent)
      (!var_n)
      var_best_u
      var_best_v
      var_best_w);
  let mut var_root_u : SizeT.t;
  var_root_u := (func_uf_find (!var_parent) (!var_n) (!var_best_u) (!var_n));
  let mut var_root_v : SizeT.t;
  var_root_v := (func_uf_find (!var_parent) (!var_n) (!var_best_v) (!var_n));
  let mut var_ec : SizeT.t;
  var_ec := (!(!var_edge_count));
  if ((((Int32.int_to_t 0) `Int32.lt` (!var_best_w)) && (not ((!var_root_u) = (!var_root_v))))) {
    (func_insert_edge (!var_edge_u) (!var_edge_v) (!var_n) (!var_ec) (!var_best_u) (!var_best_v));
    (!var_edge_count) := ((!var_ec) `SizeT.add` 1sz);
    (array_write (!var_parent) (!var_root_u) (!var_root_v));
  } else {};
}

#restart-solver

fn func_kruskal
    (var_adj: (array Int32.t))
    (var_adj_len: SizeT.t)
    (var_n: SizeT.t)
    (var_edge_u: (array SizeT.t))
    (var_edge_v: (array SizeT.t))
    (var_edge_count: (ref SizeT.t))
  requires
    exists* (val_adj_0: (Seq.seq (option Int32.t))) (val_adj_1: (nat->prop)).
    ((array_pts_to var_adj 1.0R val_adj_0 val_adj_1))
  requires
    exists* (val_edge_u_0: (Seq.seq (option SizeT.t))) (val_edge_u_1: (nat->prop)).
    ((array_pts_to var_edge_u 1.0R val_edge_u_0 val_edge_u_1))
  requires
    exists* (val_edge_v_0: (Seq.seq (option SizeT.t))) (val_edge_v_1: (nat->prop)).
    ((array_pts_to var_edge_v 1.0R val_edge_v_0 val_edge_v_1))
  requires exists* (val_edge_count_0: SizeT.t). ((pts_to var_edge_count #1.0R val_edge_count_0))
  requires
    (with_pure (((reveal (length_of var_adj)) = (SizeT.v var_adj_len)) && (0 < (SizeT.v var_n))))
  requires (with_pure (SizeT.v var_adj_len = SizeT.v var_n * SizeT.v var_n))
  requires
    (with_pure
      (((reveal (length_of var_edge_u)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_edge_v)) = (SizeT.v var_n))))
  requires (with_pure ((SizeT.v (!var_edge_count)) = 0))
  returns return_1 : unit
  ensures
    exists* (val_adj_0: (Seq.seq (option Int32.t))) (val_adj_1: (nat->prop)).
    ((array_pts_to var_adj 1.0R val_adj_0 val_adj_1))
  ensures
    exists* (val_edge_u_0: (Seq.seq (option SizeT.t))) (val_edge_u_1: (nat->prop)).
    ((array_pts_to var_edge_u 1.0R val_edge_u_0 val_edge_u_1))
  ensures
    exists* (val_edge_v_0: (Seq.seq (option SizeT.t))) (val_edge_v_1: (nat->prop)).
    ((array_pts_to var_edge_v 1.0R val_edge_v_0 val_edge_v_1))
  ensures exists* (val_edge_count_0: SizeT.t). ((pts_to var_edge_count #1.0R val_edge_count_0))
  ensures (with_pure ((reveal (length_of var_adj)) = (SizeT.v var_adj_len)))
  ensures
    (with_pure
      (((reveal (length_of var_edge_u)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_edge_v)) = (SizeT.v var_n))))
  ensures (with_pure ((!var_edge_count) `SizeT.lt` var_n))
  ensures
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((var_k `SizeT.lt` (!var_edge_count)) ==>
          (((array_read var_edge_u var_k)) `SizeT.lt` var_n))))
  ensures
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((var_k `SizeT.lt` (!var_edge_count)) ==>
          (((array_read var_edge_v var_k)) `SizeT.lt` var_n))))
  ensures
    (with_pure
      (kruskal_result_post
(array_value_of var_adj)
(array_value_of var_edge_u)
(array_value_of var_edge_v)
(SizeT.v var_n)
(SizeT.v var_adj_len)
(SizeT.v (!(var_edge_count)))))
{
  let mut var_adj = var_adj;
  let mut var_adj_len = var_adj_len;
  let mut var_n = var_n;
  let mut var_edge_u = var_edge_u;
  let mut var_edge_v = var_edge_v;
  let mut var_edge_count = var_edge_count;
  if (((!var_n) `SizeT.lte` 1sz)) {
    CLRS.Ch23.Kruskal.C.BridgeLemmas.kruskal_result_assembly
(array_value_of (!var_adj))
(array_value_of (!var_edge_u))
(array_value_of (!var_edge_v))
(!var_n)
0sz
(SizeT.v (!var_adj_len));
    return;
  } else {};
  let mut var_parent : (array SizeT.t);
  var_parent := (Pulse.Lib.C.Array.calloc_array_mask #SizeT.t (!var_n));
  assert (with_pure ((reveal (length_of (!var_parent))) = (SizeT.v (!var_n))));
  let mut var_i : SizeT.t;
  var_i := 0sz;
  while (((!var_i) `SizeT.lt` (!var_n)))
    invariant (live var_i)
    invariant (Pulse.Lib.C.Array.live_array (!var_parent))
    invariant (with_pure ((reveal (length_of (!var_parent))) = (SizeT.v (!var_n))))
    invariant (with_pure (((!var_i) `SizeT.lte` (!var_n)) && (1 < (SizeT.v (!var_n)))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_i)) ==> (((array_read (!var_parent) var_j)) = var_j))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_i)) ==>
            (((array_read (!var_parent) var_j)) `SizeT.lt` (!var_n)))))
  {
    (array_write (!var_parent) (!var_i) (!var_i));
    var_i := ((!var_i) `SizeT.add` 1sz);
  };
  let mut var_max_rounds : SizeT.t;
  var_max_rounds := ((!var_n) `SizeT.sub` 1sz);
  let mut var_round : SizeT.t;
  var_round := 0sz;
  while (((!var_round) `SizeT.lt` (!var_max_rounds)))
    invariant ((live var_round) ** (live var_max_rounds))
    invariant ((Pulse.Lib.C.Array.live_array (!var_parent)) **
        (Pulse.Lib.C.Array.live_array (!var_adj)))
    invariant (((Pulse.Lib.C.Array.live_array (!var_edge_u)) **
          (Pulse.Lib.C.Array.live_array (!var_edge_v)))
        **
        (live (!var_edge_count)))
    invariant (with_pure
        (((reveal (length_of (!var_parent))) = (SizeT.v (!var_n))) &&
          ((reveal (length_of (!var_adj))) = (SizeT.v (!var_adj_len)))))
    invariant (with_pure
        (((reveal (length_of (!var_edge_u))) = (SizeT.v (!var_n))) &&
          ((reveal (length_of (!var_edge_v))) = (SizeT.v (!var_n)))))
    invariant (with_pure ((!var_round) `SizeT.lte` (!var_max_rounds)))
    invariant (with_pure (SizeT.v (!var_max_rounds) + 1 = SizeT.v (!var_n)))
    invariant (with_pure (SizeT.v (!var_adj_len) = SizeT.v (!var_n) * SizeT.v (!var_n)))
    invariant (with_pure (1 < (SizeT.v (!var_n))))
    invariant (with_pure ((!(!var_edge_count)) `SizeT.lte` (!var_round)))
    invariant (with_pure ((!(!var_edge_count)) `SizeT.lt` (!var_n)))
    invariant (with_pure
        (forall
          (var_i: SizeT.t).
          ((var_i `SizeT.lt` (!var_n)) ==>
            (((array_read (!var_parent) var_i)) `SizeT.lt` (!var_n)))))
    invariant (with_pure
        (forall
          (var_k: SizeT.t).
          ((var_k `SizeT.lt` (!(!var_edge_count))) ==>
            (((array_read (!var_edge_u) var_k)) `SizeT.lt` (!var_n)))))
    invariant (with_pure
        (forall
          (var_k: SizeT.t).
          ((var_k `SizeT.lt` (!(!var_edge_count))) ==>
            (((array_read (!var_edge_v) var_k)) `SizeT.lt` (!var_n)))))
  {
    (func_try_add_edge
        (!var_adj)
        (!var_adj_len)
        (!var_parent)
        (!var_n)
        (!var_edge_u)
        (!var_edge_v)
        (!var_edge_count)
        (!var_round));
    var_round := ((!var_round) `SizeT.add` 1sz);
  };
  let mut var_ec_final : SizeT.t;
  var_ec_final := (!(!var_edge_count));
  CLRS.Ch23.Kruskal.C.BridgeLemmas.kruskal_result_assembly
(array_value_of (!var_adj))
(array_value_of (!var_edge_u))
(array_value_of (!var_edge_v))
(!var_n)
(!var_ec_final)
(SizeT.v (!var_adj_len));
  (Pulse.Lib.C.Array.free_array (!var_parent));
}