module BellmanFord
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

fn func_bellman_ford
    (var_weights: (array Int32.t))
    (var_n: SizeT.t)
    (var_source: SizeT.t)
    (var_dist: (array Int32.t))
    (var_result: (ref Int32.t))
  requires
    exists* (val_weights_0: (Seq.seq (option Int32.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  requires
    exists* (val_dist_0: (Seq.seq (option Int32.t))) (val_dist_1: (nat->prop)).
    ((array_pts_to var_dist 1.0R val_dist_0 val_dist_1))
  requires exists* (val_result_0: Int32.t). ((pts_to var_result #1.0R val_result_0))
  requires (with_pure ((0 < (SizeT.v var_n)) && (var_source `SizeT.lt` var_n)))
  requires (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  requires (with_pure ((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))))
  requires (with_pure ((reveal (length_of var_dist)) = (SizeT.v var_n)))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          (((op_Minus 1000000) <= (id #int (Int32.v ((array_read var_weights var_i))))) &&
            ((id #int (Int32.v ((array_read var_weights var_i)))) <= 1000000)))))
  requires (with_pure ((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))))
  returns return_1 : unit
  ensures
    exists* (val_weights_0: (Seq.seq (option Int32.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  ensures
    exists* (val_dist_0: (Seq.seq (option Int32.t))) (val_dist_1: (nat->prop)).
    ((array_pts_to var_dist 1.0R val_dist_0 val_dist_1))
  ensures exists* (val_result_0: Int32.t). ((pts_to var_result #1.0R val_result_0))
  ensures (with_pure ((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))))
  ensures (with_pure ((reveal (length_of var_dist)) = (SizeT.v var_n)))
  ensures (with_pure ((id #int (Int32.v ((array_read var_dist var_source)))) = 0))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==>
          (((id #int (Int32.v ((array_read var_dist var_v)))) < 1000000) ||
            ((id #int (Int32.v ((array_read var_dist var_v)))) = 1000000)))))
  ensures
    (with_pure (((id #int (Int32.v (!var_result))) = 0) || ((id #int (Int32.v (!var_result))) = 1)))
{
  let mut var_weights = var_weights;
  let mut var_n = var_n;
  let mut var_source = var_source;
  let mut var_dist = var_dist;
  let mut var_result = var_result;
  let mut var_i : SizeT.t;
  var_i := 0sz;
  while (((!var_i) `SizeT.lt` (!var_n)))
    invariant (live var_i)
    invariant ((Pulse.Lib.C.Array.live_array (!var_dist)) **
        (Pulse.Lib.C.Array.live_array (!var_weights)))
    invariant (with_pure
        (((reveal (length_of (!var_dist))) = (SizeT.v (!var_n))) &&
          ((reveal (length_of (!var_weights))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n))))))
    invariant (with_pure ((!var_i) `SizeT.lte` (!var_n)))
    invariant (with_pure
        (((!var_source) `SizeT.lt` (!var_i)) ==>
          ((id #int (Int32.v ((array_read (!var_dist) (!var_source))))) = 0)))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          (((var_j `SizeT.lt` (!var_i)) && (not (var_j = (!var_source)))) ==>
            ((id #int (Int32.v ((array_read (!var_dist) var_j)))) = 1000000))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_i)) ==>
            (((id #int (Int32.v ((array_read (!var_dist) var_j)))) < 1000000) ||
              ((id #int (Int32.v ((array_read (!var_dist) var_j)))) = 1000000)))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_i)) ==>
            (0 <= (id #int (Int32.v ((array_read (!var_dist) var_j))))))))
  {
    if (((!var_i) = (!var_source))) {
      (array_write (!var_dist) (!var_i) (Int32.int_to_t 0));
    } else {
      (array_write (!var_dist) (!var_i) (Int32.int_to_t 1000000));
    };
    var_i := ((!var_i) `SizeT.add` 1sz);
  };
  let mut var_round : SizeT.t;
  var_round := 1sz;
  while (((!var_round) `SizeT.lt` (!var_n)))
    invariant (live var_round)
    invariant ((Pulse.Lib.C.Array.live_array (!var_dist)) **
        (Pulse.Lib.C.Array.live_array (!var_weights)))
    invariant (with_pure
        (((reveal (length_of (!var_dist))) = (SizeT.v (!var_n))) &&
          ((reveal (length_of (!var_weights))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n))))))
    invariant (with_pure (SizeT.fits (SizeT.v (!var_n) * SizeT.v (!var_n))))
    invariant (with_pure ((1 <= (SizeT.v (!var_round))) && ((!var_round) `SizeT.lte` (!var_n))))
    invariant (with_pure ((id #int (Int32.v ((array_read (!var_dist) (!var_source))))) = 0))
    invariant (with_pure
        (forall
          (var_v: SizeT.t).
          ((var_v `SizeT.lt` (!var_n)) ==>
            (((id #int (Int32.v ((array_read (!var_dist) var_v)))) < 1000000) ||
              ((id #int (Int32.v ((array_read (!var_dist) var_v)))) = 1000000)))))
    invariant (with_pure
        (forall
          (var_v: SizeT.t).
          ((var_v `SizeT.lt` (!var_n)) ==>
            (((op_Minus 2) `op_Multiply` 1000000) <
              (id #int (Int32.v ((array_read (!var_dist) var_v))))))))
  {
    let mut var_u : SizeT.t;
    var_u := 0sz;
    while (((!var_u) `SizeT.lt` (!var_n)))
      invariant ((live var_u) ** (live var_round))
      invariant ((Pulse.Lib.C.Array.live_array (!var_dist)) **
          (Pulse.Lib.C.Array.live_array (!var_weights)))
      invariant (with_pure
          (((reveal (length_of (!var_dist))) = (SizeT.v (!var_n))) &&
            ((reveal (length_of (!var_weights))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n))))))
      invariant (with_pure (SizeT.fits (SizeT.v (!var_n) * SizeT.v (!var_n))))
      invariant (with_pure (((!var_u) `SizeT.lte` (!var_n)) && ((!var_round) `SizeT.lt` (!var_n))))
      invariant (with_pure ((id #int (Int32.v ((array_read (!var_dist) (!var_source))))) = 0))
      invariant (with_pure
          (forall
            (var_v: SizeT.t).
            ((var_v `SizeT.lt` (!var_n)) ==>
              (((id #int (Int32.v ((array_read (!var_dist) var_v)))) < 1000000) ||
                ((id #int (Int32.v ((array_read (!var_dist) var_v)))) = 1000000)))))
      invariant (with_pure
          (forall
            (var_v: SizeT.t).
            ((var_v `SizeT.lt` (!var_n)) ==>
              (((op_Minus 2) `op_Multiply` 1000000) <
                (id #int (Int32.v ((array_read (!var_dist) var_v))))))))
    {
      let mut var_d_u : Int32.t;
      var_d_u := ((array_read (!var_dist) (!var_u)));
      let mut var_v : SizeT.t;
      var_v := 0sz;
      while (((!var_v) `SizeT.lt` (!var_n)))
        invariant (((live var_v) ** (live var_u)) ** (live var_round))
        invariant ((Pulse.Lib.C.Array.live_array (!var_dist)) **
            (Pulse.Lib.C.Array.live_array (!var_weights)))
        invariant (with_pure
            (((reveal (length_of (!var_dist))) = (SizeT.v (!var_n))) &&
              ((reveal (length_of (!var_weights))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n))))))
        invariant (with_pure (SizeT.fits (SizeT.v (!var_n) * SizeT.v (!var_n))))
        invariant (with_pure
            ((((!var_v) `SizeT.lte` (!var_n)) && ((!var_u) `SizeT.lt` (!var_n))) &&
              ((!var_round) `SizeT.lt` (!var_n))))
        invariant (with_pure ((id #int (Int32.v ((array_read (!var_dist) (!var_source))))) = 0))
        invariant (with_pure
            (forall
              (var_j: SizeT.t).
              ((var_j `SizeT.lt` (!var_n)) ==>
                (((id #int (Int32.v ((array_read (!var_dist) var_j)))) < 1000000) ||
                  ((id #int (Int32.v ((array_read (!var_dist) var_j)))) = 1000000)))))
        invariant (with_pure
            (forall
              (var_j: SizeT.t).
              ((var_j `SizeT.lt` (!var_n)) ==>
                (((op_Minus 2) `op_Multiply` 1000000) <
                  (id #int (Int32.v ((array_read (!var_dist) var_j))))))))
      {
        let mut var_w : Int32.t;
        var_w :=
          ((array_read (!var_weights) (((!var_u) `SizeT.mul` (!var_n)) `SizeT.add` (!var_v))));
        let mut var_d_v : Int32.t;
        var_d_v := ((array_read (!var_dist) (!var_v)));
        if ((((((((!var_w) `Int32.lt` (Int32.int_to_t 1000000)) &&
                      ((Int32.sub Int32.zero (Int32.int_to_t 1000000)) `Int32.lt` (!var_w)))
                    &&
                    ((!var_d_u) `Int32.lt` (Int32.int_to_t 1000000)))
                  &&
                  ((Int32.sub Int32.zero (Int32.int_to_t 1000000)) `Int32.lt` (!var_d_u)))
                &&
                (((!var_d_u) `Int32.add` (!var_w)) `Int32.lt` (!var_d_v)))
              &&
              (not ((!var_v) = (!var_source))))) {
          (array_write (!var_dist) (!var_v) ((!var_d_u) `Int32.add` (!var_w)));
        } else {};
        var_v := ((!var_v) `SizeT.add` 1sz);
      };
      var_u := ((!var_u) `SizeT.add` 1sz);
    };
    var_round := ((!var_round) `SizeT.add` 1sz);
  };
  (!var_result) := (Int32.int_to_t 1);
  let mut var_u : SizeT.t;
  var_u := 0sz;
  while (((!var_u) `SizeT.lt` (!var_n)))
    invariant (live var_u)
    invariant (((Pulse.Lib.C.Array.live_array (!var_dist)) **
          (Pulse.Lib.C.Array.live_array (!var_weights)))
        **
        (live (!var_result)))
    invariant (with_pure
        (((reveal (length_of (!var_dist))) = (SizeT.v (!var_n))) &&
          ((reveal (length_of (!var_weights))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n))))))
    invariant (with_pure (SizeT.fits (SizeT.v (!var_n) * SizeT.v (!var_n))))
    invariant (with_pure ((!var_u) `SizeT.lte` (!var_n)))
    invariant (with_pure
        (((id #int (Int32.v (!(!var_result)))) = 0) || ((id #int (Int32.v (!(!var_result)))) = 1)))
    invariant (with_pure ((id #int (Int32.v ((array_read (!var_dist) (!var_source))))) = 0))
    invariant (with_pure
        (forall
          (var_v: SizeT.t).
          ((var_v `SizeT.lt` (!var_n)) ==>
            (((id #int (Int32.v ((array_read (!var_dist) var_v)))) < 1000000) ||
              ((id #int (Int32.v ((array_read (!var_dist) var_v)))) = 1000000)))))
  {
    let mut var_v : SizeT.t;
    var_v := 0sz;
    while (((!var_v) `SizeT.lt` (!var_n)))
      invariant ((live var_v) ** (live var_u))
      invariant (((Pulse.Lib.C.Array.live_array (!var_dist)) **
            (Pulse.Lib.C.Array.live_array (!var_weights)))
          **
          (live (!var_result)))
      invariant (with_pure
          (((reveal (length_of (!var_dist))) = (SizeT.v (!var_n))) &&
            ((reveal (length_of (!var_weights))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n))))))
      invariant (with_pure (SizeT.fits (SizeT.v (!var_n) * SizeT.v (!var_n))))
      invariant (with_pure (((!var_v) `SizeT.lte` (!var_n)) && ((!var_u) `SizeT.lt` (!var_n))))
      invariant (with_pure
          (((id #int (Int32.v (!(!var_result)))) = 0) ||
            ((id #int (Int32.v (!(!var_result)))) = 1)))
      invariant (with_pure ((id #int (Int32.v ((array_read (!var_dist) (!var_source))))) = 0))
      invariant (with_pure
          (forall
            (var_j: SizeT.t).
            ((var_j `SizeT.lt` (!var_n)) ==>
              (((id #int (Int32.v ((array_read (!var_dist) var_j)))) < 1000000) ||
                ((id #int (Int32.v ((array_read (!var_dist) var_j)))) = 1000000)))))
    {
      let mut var_w : Int32.t;
      var_w := ((array_read (!var_weights) (((!var_u) `SizeT.mul` (!var_n)) `SizeT.add` (!var_v))));
      let mut var_d_u : Int32.t;
      var_d_u := ((array_read (!var_dist) (!var_u)));
      let mut var_d_v : Int32.t;
      var_d_v := ((array_read (!var_dist) (!var_v)));
      if (((((((!var_w) `Int32.lt` (Int32.int_to_t 1000000)) &&
                  ((Int32.sub Int32.zero (Int32.int_to_t 1000000)) `Int32.lt` (!var_w)))
                &&
                ((!var_d_u) `Int32.lt` (Int32.int_to_t 1000000)))
              &&
              ((Int32.sub Int32.zero (Int32.int_to_t 1000000)) `Int32.lt` (!var_d_u)))
            &&
            (((!var_d_u) `Int32.add` (!var_w)) `Int32.lt` (!var_d_v)))) {
        (!var_result) := (Int32.int_to_t 0);
      } else {};
      var_v := ((!var_v) `SizeT.add` 1sz);
    };
    var_u := ((!var_u) `SizeT.add` 1sz);
  };
}