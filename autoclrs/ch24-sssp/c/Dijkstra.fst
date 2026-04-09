module Dijkstra
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

fn func_dijkstra_find_min
    (var_dist: (array Int32.t))
    (var_visited: (array Int32.t))
    (var_n: SizeT.t)
    (var_source: SizeT.t)
  requires
    exists* (val_dist_0: (Seq.seq (option Int32.t))) (val_dist_1: (nat->prop)).
    ((array_pts_to var_dist 1.0R val_dist_0 val_dist_1))
  requires
    exists* (val_visited_0: (Seq.seq (option Int32.t))) (val_visited_1: (nat->prop)).
    ((array_pts_to var_visited 1.0R val_visited_0 val_visited_1))
  requires (with_pure ((0 < (SizeT.v var_n)) && (var_source `SizeT.lt` var_n)))
  requires
    (with_pure
      (((reveal (length_of var_dist)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_visited)) = (SizeT.v var_n))))
  requires
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==>
          ((0 <= (id #int (Int32.v ((array_read var_dist var_v))))) &&
            ((id #int (Int32.v ((array_read var_dist var_v)))) <= 1000000)))))
  requires (with_pure ((id #int (Int32.v ((array_read var_dist var_source)))) = 0))
  returns return_1 : SizeT.t
  ensures
    exists* (val_dist_0: (Seq.seq (option Int32.t))) (val_dist_1: (nat->prop)).
    ((array_pts_to var_dist 1.0R val_dist_0 val_dist_1))
  ensures
    exists* (val_visited_0: (Seq.seq (option Int32.t))) (val_visited_1: (nat->prop)).
    ((array_pts_to var_visited 1.0R val_visited_0 val_visited_1))
  ensures
    (with_pure
      (((reveal (length_of var_dist)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_visited)) = (SizeT.v var_n))))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==>
          ((0 <= (id #int (Int32.v ((array_read var_dist var_v))))) &&
            ((id #int (Int32.v ((array_read var_dist var_v)))) <= 1000000)))))
  ensures (with_pure ((id #int (Int32.v ((array_read var_dist var_source)))) = 0))
  ensures (with_pure (return_1 `SizeT.lt` var_n))
{
  let mut var_dist = var_dist;
  let mut var_visited = var_visited;
  let mut var_n = var_n;
  let mut var_source = var_source;
  let mut var_u : SizeT.t;
  var_u := 0sz;
  let mut var_min_d : Int32.t;
  var_min_d := ((Int32.int_to_t 1000000) `Int32.add` (Int32.int_to_t 1));
  let mut var_j : SizeT.t;
  var_j := 0sz;
  while (((!var_j) `SizeT.lt` (!var_n)))
    invariant (((live var_j) ** (live var_u)) ** (live var_min_d))
    invariant ((Pulse.Lib.C.Array.live_array (!var_dist)) **
        (Pulse.Lib.C.Array.live_array (!var_visited)))
    invariant (with_pure
        (((reveal (length_of (!var_dist))) = (SizeT.v (!var_n))) &&
          ((reveal (length_of (!var_visited))) = (SizeT.v (!var_n)))))
    invariant (with_pure (((!var_j) `SizeT.lte` (!var_n)) && ((!var_u) `SizeT.lt` (!var_n))))
    invariant (with_pure
        ((0 <= (id #int (Int32.v (!var_min_d)))) &&
          ((id #int (Int32.v (!var_min_d))) <= (1000000 + 1))))
    invariant (with_pure
        (forall
          (var_v: SizeT.t).
          ((var_v `SizeT.lt` (!var_n)) ==>
            ((0 <= (id #int (Int32.v ((array_read (!var_dist) var_v))))) &&
              ((id #int (Int32.v ((array_read (!var_dist) var_v)))) <= 1000000)))))
    invariant (with_pure ((id #int (Int32.v ((array_read (!var_dist) (!var_source))))) = 0))
  {
    let mut var_vj : Int32.t;
    var_vj := ((array_read (!var_visited) (!var_j)));
    let mut var_dj : Int32.t;
    var_dj := ((array_read (!var_dist) (!var_j)));
    if (((!var_vj) = (Int32.int_to_t 0))) {
      if (((!var_dj) `Int32.lt` (!var_min_d))) {
        var_u := (!var_j);
        var_min_d := (!var_dj);
      } else {};
    } else {};
    var_j := ((!var_j) `SizeT.add` 1sz);
  };
  (array_write (!var_visited) (!var_u) (Int32.int_to_t 1));
  return (!var_u);
}

#restart-solver

fn func_dijkstra_relax_one
    (var_weights: (array Int32.t))
    (var_dist: (array Int32.t))
    (var_pred: (array SizeT.t))
    (var_n: SizeT.t)
    (var_source: SizeT.t)
    (var_u: SizeT.t)
    (var_v: SizeT.t)
    (var_d_u: Int32.t)
    (var_un: SizeT.t)
  requires
    exists* (val_weights_0: (Seq.seq (option Int32.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  requires
    exists* (val_dist_0: (Seq.seq (option Int32.t))) (val_dist_1: (nat->prop)).
    ((array_pts_to var_dist 1.0R val_dist_0 val_dist_1))
  requires
    exists* (val_pred_0: (Seq.seq (option SizeT.t))) (val_pred_1: (nat->prop)).
    ((array_pts_to var_pred 1.0R val_pred_0 val_pred_1))
  requires
    (with_pure
      ((((0 < (SizeT.v var_n)) && (var_source `SizeT.lt` var_n)) && (var_u `SizeT.lt` var_n)) &&
        (var_v `SizeT.lt` var_n)))
  requires (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  requires
    (with_pure
      ((((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))) &&
          ((reveal (length_of var_dist)) = (SizeT.v var_n)))
        &&
        ((reveal (length_of var_pred)) = (SizeT.v var_n))))
  requires (with_pure (SizeT.v var_un = SizeT.v var_u * SizeT.v var_n))
  requires
    (with_pure ((0 <= (id #int (Int32.v var_d_u))) && ((id #int (Int32.v var_d_u)) <= 1000000)))
  requires (with_pure ((id #int (Int32.v ((array_read var_dist var_source)))) = 0))
  requires (with_pure (((array_read var_pred var_source)) = var_source))
  requires
    (with_pure
      (forall
        (var_j: SizeT.t).
        ((var_j `SizeT.lt` var_n) ==>
          ((0 <= (id #int (Int32.v ((array_read var_dist var_j))))) &&
            ((id #int (Int32.v ((array_read var_dist var_j)))) <= 1000000)))))
  requires
    (with_pure
      (forall
        (var_j: SizeT.t).
        ((var_j `SizeT.lt` var_n) ==> (((array_read var_pred var_j)) `SizeT.lt` var_n))))
  requires (with_pure ((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))))
  requires (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  requires
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((var_k `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          ((0 <= (id #int (Int32.v ((array_read var_weights var_k))))) &&
            ((id #int (Int32.v ((array_read var_weights var_k)))) <= 1000000)))))
  returns return_1 : unit
  ensures
    exists* (val_weights_0: (Seq.seq (option Int32.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  ensures
    exists* (val_dist_0: (Seq.seq (option Int32.t))) (val_dist_1: (nat->prop)).
    ((array_pts_to var_dist 1.0R val_dist_0 val_dist_1))
  ensures
    exists* (val_pred_0: (Seq.seq (option SizeT.t))) (val_pred_1: (nat->prop)).
    ((array_pts_to var_pred 1.0R val_pred_0 val_pred_1))
  ensures (with_pure ((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))))
  ensures (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  ensures
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((var_k `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          ((0 <= (id #int (Int32.v ((array_read var_weights var_k))))) &&
            ((id #int (Int32.v ((array_read var_weights var_k)))) <= 1000000)))))
  ensures
    (with_pure
      (((reveal (length_of var_dist)) = (SizeT.v var_n)) &&
        ((reveal (length_of var_pred)) = (SizeT.v var_n))))
  ensures (with_pure ((id #int (Int32.v ((array_read var_dist var_source)))) = 0))
  ensures (with_pure (((array_read var_pred var_source)) = var_source))
  ensures
    (with_pure
      (forall
        (var_j: SizeT.t).
        ((var_j `SizeT.lt` var_n) ==>
          ((0 <= (id #int (Int32.v ((array_read var_dist var_j))))) &&
            ((id #int (Int32.v ((array_read var_dist var_j)))) <= 1000000)))))
  ensures
    (with_pure
      (forall
        (var_j: SizeT.t).
        ((var_j `SizeT.lt` var_n) ==> (((array_read var_pred var_j)) `SizeT.lt` var_n))))
{
  let mut var_weights = var_weights;
  let mut var_dist = var_dist;
  let mut var_pred = var_pred;
  let mut var_n = var_n;
  let mut var_source = var_source;
  let mut var_u = var_u;
  let mut var_v = var_v;
  let mut var_d_u = var_d_u;
  let mut var_un = var_un;
  let mut var_w : Int32.t;
  var_w := ((array_read (!var_weights) ((!var_un) `SizeT.add` (!var_v))));
  let mut var_d_v : Int32.t;
  var_d_v := ((array_read (!var_dist) (!var_v)));
  if (((((((Int32.int_to_t 0) `Int32.lte` (!var_w)) &&
              ((!var_w) `Int32.lt` (Int32.int_to_t 1000000)))
            &&
            ((!var_d_u) `Int32.lt` (Int32.int_to_t 1000000)))
          &&
          (((!var_d_u) `Int32.add` (!var_w)) `Int32.lt` (!var_d_v)))
        &&
        (not ((!var_v) = (!var_source))))) {
    (array_write (!var_dist) (!var_v) ((!var_d_u) `Int32.add` (!var_w)));
    (array_write (!var_pred) (!var_v) (!var_u));
  } else {};
}

#restart-solver

fn func_dijkstra_relax
    (var_weights: (array Int32.t))
    (var_dist: (array Int32.t))
    (var_pred: (array SizeT.t))
    (var_n: SizeT.t)
    (var_source: SizeT.t)
    (var_u: SizeT.t)
  requires
    exists* (val_weights_0: (Seq.seq (option Int32.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  requires
    exists* (val_dist_0: (Seq.seq (option Int32.t))) (val_dist_1: (nat->prop)).
    ((array_pts_to var_dist 1.0R val_dist_0 val_dist_1))
  requires
    exists* (val_pred_0: (Seq.seq (option SizeT.t))) (val_pred_1: (nat->prop)).
    ((array_pts_to var_pred 1.0R val_pred_0 val_pred_1))
  requires
    (with_pure
      (((0 < (SizeT.v var_n)) && (var_source `SizeT.lt` var_n)) && (var_u `SizeT.lt` var_n)))
  requires (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  requires
    (with_pure
      ((((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))) &&
          ((reveal (length_of var_dist)) = (SizeT.v var_n)))
        &&
        ((reveal (length_of var_pred)) = (SizeT.v var_n))))
  requires (with_pure ((id #int (Int32.v ((array_read var_dist var_source)))) = 0))
  requires (with_pure (((array_read var_pred var_source)) = var_source))
  requires
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==>
          ((0 <= (id #int (Int32.v ((array_read var_dist var_v))))) &&
            ((id #int (Int32.v ((array_read var_dist var_v)))) <= 1000000)))))
  requires
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==> (((array_read var_pred var_v)) `SizeT.lt` var_n))))
  requires
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((var_k `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          ((0 <= (id #int (Int32.v ((array_read var_weights var_k))))) &&
            ((id #int (Int32.v ((array_read var_weights var_k)))) <= 1000000)))))
  returns return_1 : unit
  ensures
    exists* (val_weights_0: (Seq.seq (option Int32.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  ensures
    exists* (val_dist_0: (Seq.seq (option Int32.t))) (val_dist_1: (nat->prop)).
    ((array_pts_to var_dist 1.0R val_dist_0 val_dist_1))
  ensures
    exists* (val_pred_0: (Seq.seq (option SizeT.t))) (val_pred_1: (nat->prop)).
    ((array_pts_to var_pred 1.0R val_pred_0 val_pred_1))
  ensures
    (with_pure
      ((((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))) &&
          ((reveal (length_of var_dist)) = (SizeT.v var_n)))
        &&
        ((reveal (length_of var_pred)) = (SizeT.v var_n))))
  ensures (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  ensures (with_pure ((id #int (Int32.v ((array_read var_dist var_source)))) = 0))
  ensures (with_pure (((array_read var_pred var_source)) = var_source))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==>
          ((0 <= (id #int (Int32.v ((array_read var_dist var_v))))) &&
            ((id #int (Int32.v ((array_read var_dist var_v)))) <= 1000000)))))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==> (((array_read var_pred var_v)) `SizeT.lt` var_n))))
  ensures
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((var_k `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          ((0 <= (id #int (Int32.v ((array_read var_weights var_k))))) &&
            ((id #int (Int32.v ((array_read var_weights var_k)))) <= 1000000)))))
{
  let mut var_weights = var_weights;
  let mut var_dist = var_dist;
  let mut var_pred = var_pred;
  let mut var_n = var_n;
  let mut var_source = var_source;
  let mut var_u = var_u;
  let mut var_d_u : Int32.t;
  var_d_u := ((array_read (!var_dist) (!var_u)));
  assert (with_pure (SizeT.fits (SizeT.v (!var_u) * SizeT.v (!var_n))));
  let mut var_un : SizeT.t;
  var_un := ((!var_u) `SizeT.mul` (!var_n));
  let mut var_v : SizeT.t;
  var_v := 0sz;
  while (((!var_v) `SizeT.lt` (!var_n)))
    invariant ((live var_v) ** (live var_un))
    invariant (((Pulse.Lib.C.Array.live_array (!var_dist)) **
          (Pulse.Lib.C.Array.live_array (!var_weights)))
        **
        (Pulse.Lib.C.Array.live_array (!var_pred)))
    invariant (with_pure
        ((((reveal (length_of (!var_weights))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n)))) &&
            ((reveal (length_of (!var_dist))) = (SizeT.v (!var_n))))
          &&
          ((reveal (length_of (!var_pred))) = (SizeT.v (!var_n)))))
    invariant (with_pure (SizeT.fits (SizeT.v (!var_n) * SizeT.v (!var_n))))
    invariant (with_pure (((!var_v) `SizeT.lte` (!var_n)) && ((!var_u) `SizeT.lt` (!var_n))))
    invariant (with_pure (SizeT.v (!var_un) = SizeT.v (!var_u) * SizeT.v (!var_n)))
    invariant (with_pure
        ((0 <= (id #int (Int32.v (!var_d_u)))) && ((id #int (Int32.v (!var_d_u))) <= 1000000)))
    invariant (with_pure ((id #int (Int32.v ((array_read (!var_dist) (!var_source))))) = 0))
    invariant (with_pure (((array_read (!var_pred) (!var_source))) = (!var_source)))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_n)) ==>
            ((0 <= (id #int (Int32.v ((array_read (!var_dist) var_j))))) &&
              ((id #int (Int32.v ((array_read (!var_dist) var_j)))) <= 1000000)))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_n)) ==> (((array_read (!var_pred) var_j)) `SizeT.lt` (!var_n)))))
    invariant (with_pure
        (forall
          (var_k: SizeT.t).
          ((var_k `SizeT.lt` ((!var_n) `SizeT.mul` (!var_n))) ==>
            ((0 <= (id #int (Int32.v ((array_read (!var_weights) var_k))))) &&
              ((id #int (Int32.v ((array_read (!var_weights) var_k)))) <= 1000000)))))
  {
    (func_dijkstra_relax_one
        (!var_weights)
        (!var_dist)
        (!var_pred)
        (!var_n)
        (!var_source)
        (!var_u)
        (!var_v)
        (!var_d_u)
        (!var_un));
    var_v := ((!var_v) `SizeT.add` 1sz);
  };
}

#restart-solver

fn func_dijkstra_check_vertex
    (var_weights: (array Int32.t))
    (var_dist: (array Int32.t))
    (var_n: SizeT.t)
    (var_source: SizeT.t)
    (var_u: SizeT.t)
    (var_result: (ref Int32.t))
  requires
    exists* (val_weights_0: (Seq.seq (option Int32.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  requires
    exists* (val_dist_0: (Seq.seq (option Int32.t))) (val_dist_1: (nat->prop)).
    ((array_pts_to var_dist 1.0R val_dist_0 val_dist_1))
  requires exists* (val_result_0: Int32.t). ((pts_to var_result #1.0R val_result_0))
  requires
    (with_pure
      (((0 < (SizeT.v var_n)) && (var_source `SizeT.lt` var_n)) && (var_u `SizeT.lt` var_n)))
  requires (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  requires
    (with_pure
      (((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))) &&
        ((reveal (length_of var_dist)) = (SizeT.v var_n))))
  requires
    (with_pure (((id #int (Int32.v (!var_result))) = 0) || ((id #int (Int32.v (!var_result))) = 1)))
  requires (with_pure ((id #int (Int32.v ((array_read var_dist var_source)))) = 0))
  requires
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==>
          (((id #int (Int32.v ((array_read var_dist var_v)))) < 1000000) ||
            ((id #int (Int32.v ((array_read var_dist var_v)))) = 1000000)))))
  requires
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==>
          (((op_Minus 2) `op_Multiply` 1000000) <
            (id #int (Int32.v ((array_read var_dist var_v))))))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          (((op_Minus 1000000) <= (id #int (Int32.v ((array_read var_weights var_i))))) &&
            ((id #int (Int32.v ((array_read var_weights var_i)))) <= 1000000)))))
  requires
    (with_pure
      (((id #int (Int32.v (!var_result))) = 1) ==>
        (forall
          (var_u2: SizeT.t).
          ((var_u2 `SizeT.lt` var_u) ==>
            (forall
              (var_v2: SizeT.t).
              ((var_v2 `SizeT.lt` var_n) ==>
                ((((((id
                            #int
                            (Int32.v
                              ((array_read
                                  var_weights
                                  ((var_u2 `SizeT.mul` var_n) `SizeT.add` var_v2)))))
                          <
                          1000000)
                        &&
                        ((op_Minus 1000000) <
                          (id
                            #int
                            (Int32.v
                              ((array_read
                                  var_weights
                                  ((var_u2 `SizeT.mul` var_n) `SizeT.add` var_v2)))))))
                      &&
                      ((id #int (Int32.v ((array_read var_dist var_u2)))) < 1000000))
                    &&
                    ((op_Minus 1000000) < (id #int (Int32.v ((array_read var_dist var_u2))))))
                  ==>
                  (((array_read var_dist var_v2)) `Int32.lte`
                    (((array_read var_dist var_u2)) `Int32.add`
                      ((array_read
                          var_weights
                          ((var_u2 `SizeT.mul` var_n) `SizeT.add` var_v2))))))))))))
  returns return_1 : unit
  ensures
    exists* (val_weights_0: (Seq.seq (option Int32.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  ensures
    exists* (val_dist_0: (Seq.seq (option Int32.t))) (val_dist_1: (nat->prop)).
    ((array_pts_to var_dist 1.0R val_dist_0 val_dist_1))
  ensures exists* (val_result_0: Int32.t). ((pts_to var_result #1.0R val_result_0))
  ensures
    (with_pure
      (((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))) &&
        ((reveal (length_of var_dist)) = (SizeT.v var_n))))
  ensures (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  ensures
    (with_pure (((id #int (Int32.v (!var_result))) = 0) || ((id #int (Int32.v (!var_result))) = 1)))
  ensures (with_pure ((id #int (Int32.v ((array_read var_dist var_source)))) = 0))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==>
          (((id #int (Int32.v ((array_read var_dist var_v)))) < 1000000) ||
            ((id #int (Int32.v ((array_read var_dist var_v)))) = 1000000)))))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==>
          (((op_Minus 2) `op_Multiply` 1000000) <
            (id #int (Int32.v ((array_read var_dist var_v))))))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          (((op_Minus 1000000) <= (id #int (Int32.v ((array_read var_weights var_i))))) &&
            ((id #int (Int32.v ((array_read var_weights var_i)))) <= 1000000)))))
  ensures
    (with_pure
      (((id #int (Int32.v (!var_result))) = 1) ==>
        (forall
          (var_u2: SizeT.t).
          ((var_u2 `SizeT.lte` var_u) ==>
            (forall
              (var_v2: SizeT.t).
              ((var_v2 `SizeT.lt` var_n) ==>
                ((((((id
                            #int
                            (Int32.v
                              ((array_read
                                  var_weights
                                  ((var_u2 `SizeT.mul` var_n) `SizeT.add` var_v2)))))
                          <
                          1000000)
                        &&
                        ((op_Minus 1000000) <
                          (id
                            #int
                            (Int32.v
                              ((array_read
                                  var_weights
                                  ((var_u2 `SizeT.mul` var_n) `SizeT.add` var_v2)))))))
                      &&
                      ((id #int (Int32.v ((array_read var_dist var_u2)))) < 1000000))
                    &&
                    ((op_Minus 1000000) < (id #int (Int32.v ((array_read var_dist var_u2))))))
                  ==>
                  (((array_read var_dist var_v2)) `Int32.lte`
                    (((array_read var_dist var_u2)) `Int32.add`
                      ((array_read
                          var_weights
                          ((var_u2 `SizeT.mul` var_n) `SizeT.add` var_v2))))))))))))
{
  let mut var_weights = var_weights;
  let mut var_dist = var_dist;
  let mut var_n = var_n;
  let mut var_source = var_source;
  let mut var_u = var_u;
  let mut var_result = var_result;
  let mut var_v : SizeT.t;
  var_v := 0sz;
  while (((!var_v) `SizeT.lt` (!var_n)))
    invariant (live var_v)
    invariant (((Pulse.Lib.C.Array.live_array (!var_dist)) **
          (Pulse.Lib.C.Array.live_array (!var_weights)))
        **
        (live (!var_result)))
    invariant (with_pure
        (((reveal (length_of (!var_weights))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n)))) &&
          ((reveal (length_of (!var_dist))) = (SizeT.v (!var_n)))))
    invariant (with_pure (SizeT.fits (SizeT.v (!var_n) * SizeT.v (!var_n))))
    invariant (with_pure (((!var_v) `SizeT.lte` (!var_n)) && ((!var_u) `SizeT.lt` (!var_n))))
    invariant (with_pure
        (((id #int (Int32.v (!(!var_result)))) = 0) || ((id #int (Int32.v (!(!var_result)))) = 1)))
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
    invariant (with_pure
        (forall
          (var_i: SizeT.t).
          ((var_i `SizeT.lt` ((!var_n) `SizeT.mul` (!var_n))) ==>
            (((op_Minus 1000000) <= (id #int (Int32.v ((array_read (!var_weights) var_i))))) &&
              ((id #int (Int32.v ((array_read (!var_weights) var_i)))) <= 1000000)))))
    invariant (with_pure
        (((id #int (Int32.v (!(!var_result)))) = 1) ==>
          (forall
            (var_u2: SizeT.t).
            ((var_u2 `SizeT.lt` (!var_u)) ==>
              (forall
                (var_v2: SizeT.t).
                ((var_v2 `SizeT.lt` (!var_n)) ==>
                  ((((((id
                              #int
                              (Int32.v
                                ((array_read
                                    (!var_weights)
                                    ((var_u2 `SizeT.mul` (!var_n)) `SizeT.add` var_v2)))))
                            <
                            1000000)
                          &&
                          ((op_Minus 1000000) <
                            (id
                              #int
                              (Int32.v
                                ((array_read
                                    (!var_weights)
                                    ((var_u2 `SizeT.mul` (!var_n)) `SizeT.add` var_v2)))))))
                        &&
                        ((id #int (Int32.v ((array_read (!var_dist) var_u2)))) < 1000000))
                      &&
                      ((op_Minus 1000000) < (id #int (Int32.v ((array_read (!var_dist) var_u2))))))
                    ==>
                    (((array_read (!var_dist) var_v2)) `Int32.lte`
                      (((array_read (!var_dist) var_u2)) `Int32.add`
                        ((array_read
                            (!var_weights)
                            ((var_u2 `SizeT.mul` (!var_n)) `SizeT.add` var_v2))))))))))))
    invariant (with_pure
        (((id #int (Int32.v (!(!var_result)))) = 1) ==>
          (forall
            (var_v2: SizeT.t).
            ((var_v2 `SizeT.lt` (!var_v)) ==>
              ((((((id
                          #int
                          (Int32.v
                            ((array_read
                                (!var_weights)
                                (((!var_u) `SizeT.mul` (!var_n)) `SizeT.add` var_v2)))))
                        <
                        1000000)
                      &&
                      ((op_Minus 1000000) <
                        (id
                          #int
                          (Int32.v
                            ((array_read
                                (!var_weights)
                                (((!var_u) `SizeT.mul` (!var_n)) `SizeT.add` var_v2)))))))
                    &&
                    ((id #int (Int32.v ((array_read (!var_dist) (!var_u))))) < 1000000))
                  &&
                  ((op_Minus 1000000) < (id #int (Int32.v ((array_read (!var_dist) (!var_u)))))))
                ==>
                (((array_read (!var_dist) var_v2)) `Int32.lte`
                  (((array_read (!var_dist) (!var_u))) `Int32.add`
                    ((array_read
                        (!var_weights)
                        (((!var_u) `SizeT.mul` (!var_n)) `SizeT.add` var_v2))))))))))
  {
    let mut var_w : Int32.t;
    var_w := ((array_read (!var_weights) (((!var_u) `SizeT.mul` (!var_n)) `SizeT.add` (!var_v))));
    let mut var_d_u : Int32.t;
    var_d_u := ((array_read (!var_dist) (!var_u)));
    let mut var_d_v : Int32.t;
    var_d_v := ((array_read (!var_dist) (!var_v)));
    if ((((((!var_w) `Int32.lt` (Int32.int_to_t 1000000)) &&
              ((Int32.sub Int32.zero (Int32.int_to_t 1000000)) `Int32.lt` (!var_w)))
            &&
            ((!var_d_u) `Int32.lt` (Int32.int_to_t 1000000)))
          &&
          ((Int32.sub Int32.zero (Int32.int_to_t 1000000)) `Int32.lt` (!var_d_u)))) {
      if ((((!var_d_u) `Int32.add` (!var_w)) `Int32.lt` (!var_d_v))) {
        (!var_result) := (Int32.int_to_t 0);
      } else {};
    } else {};
    var_v := ((!var_v) `SizeT.add` 1sz);
  };
}

#restart-solver

fn rec func_dijkstra_check_all
    (var_weights: (array Int32.t))
    (var_dist: (array Int32.t))
    (var_n: SizeT.t)
    (var_source: SizeT.t)
    (var_bound: SizeT.t)
    (var_result_in: Int32.t)
  requires
    exists* (val_weights_0: (Seq.seq (option Int32.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  requires
    exists* (val_dist_0: (Seq.seq (option Int32.t))) (val_dist_1: (nat->prop)).
    ((array_pts_to var_dist 1.0R val_dist_0 val_dist_1))
  requires
    (with_pure
      (((0 < (SizeT.v var_n)) && (var_source `SizeT.lt` var_n)) && (var_bound `SizeT.lte` var_n)))
  requires (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  requires
    (with_pure
      (((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))) &&
        ((reveal (length_of var_dist)) = (SizeT.v var_n))))
  requires
    (with_pure (((id #int (Int32.v var_result_in)) = 0) || ((id #int (Int32.v var_result_in)) = 1)))
  requires (with_pure ((id #int (Int32.v ((array_read var_dist var_source)))) = 0))
  requires
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==>
          (((id #int (Int32.v ((array_read var_dist var_v)))) < 1000000) ||
            ((id #int (Int32.v ((array_read var_dist var_v)))) = 1000000)))))
  requires
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==>
          (((op_Minus 2) `op_Multiply` 1000000) <
            (id #int (Int32.v ((array_read var_dist var_v))))))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          (((op_Minus 1000000) <= (id #int (Int32.v ((array_read var_weights var_i))))) &&
            ((id #int (Int32.v ((array_read var_weights var_i)))) <= 1000000)))))
  requires
    (with_pure
      (((id #int (Int32.v var_result_in)) = 1) ==>
        (forall
          (var_u2: SizeT.t).
          ((var_u2 `SizeT.lt` var_bound) ==>
            (forall
              (var_v2: SizeT.t).
              ((var_v2 `SizeT.lt` var_n) ==>
                ((((((id
                            #int
                            (Int32.v
                              ((array_read
                                  var_weights
                                  ((var_u2 `SizeT.mul` var_n) `SizeT.add` var_v2)))))
                          <
                          1000000)
                        &&
                        ((op_Minus 1000000) <
                          (id
                            #int
                            (Int32.v
                              ((array_read
                                  var_weights
                                  ((var_u2 `SizeT.mul` var_n) `SizeT.add` var_v2)))))))
                      &&
                      ((id #int (Int32.v ((array_read var_dist var_u2)))) < 1000000))
                    &&
                    ((op_Minus 1000000) < (id #int (Int32.v ((array_read var_dist var_u2))))))
                  ==>
                  (((array_read var_dist var_v2)) `Int32.lte`
                    (((array_read var_dist var_u2)) `Int32.add`
                      ((array_read
                          var_weights
                          ((var_u2 `SizeT.mul` var_n) `SizeT.add` var_v2))))))))))))
  returns return_1 : Int32.t
  ensures
    exists* (val_weights_0: (Seq.seq (option Int32.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  ensures
    exists* (val_dist_0: (Seq.seq (option Int32.t))) (val_dist_1: (nat->prop)).
    ((array_pts_to var_dist 1.0R val_dist_0 val_dist_1))
  ensures
    (with_pure
      (((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))) &&
        ((reveal (length_of var_dist)) = (SizeT.v var_n))))
  ensures (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  ensures (with_pure (((id #int (Int32.v return_1)) = 0) || ((id #int (Int32.v return_1)) = 1)))
  ensures (with_pure ((id #int (Int32.v ((array_read var_dist var_source)))) = 0))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==>
          (((id #int (Int32.v ((array_read var_dist var_v)))) < 1000000) ||
            ((id #int (Int32.v ((array_read var_dist var_v)))) = 1000000)))))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==>
          (((op_Minus 2) `op_Multiply` 1000000) <
            (id #int (Int32.v ((array_read var_dist var_v))))))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          (((op_Minus 1000000) <= (id #int (Int32.v ((array_read var_weights var_i))))) &&
            ((id #int (Int32.v ((array_read var_weights var_i)))) <= 1000000)))))
  ensures
    (with_pure
      (((id #int (Int32.v return_1)) = 1) ==>
        (forall
          (var_u: SizeT.t).
          ((var_u `SizeT.lt` var_n) ==>
            (forall
              (var_v: SizeT.t).
              ((var_v `SizeT.lt` var_n) ==>
                ((((((id
                            #int
                            (Int32.v
                              ((array_read
                                  var_weights
                                  ((var_u `SizeT.mul` var_n) `SizeT.add` var_v)))))
                          <
                          1000000)
                        &&
                        ((op_Minus 1000000) <
                          (id
                            #int
                            (Int32.v
                              ((array_read
                                  var_weights
                                  ((var_u `SizeT.mul` var_n) `SizeT.add` var_v)))))))
                      &&
                      ((id #int (Int32.v ((array_read var_dist var_u)))) < 1000000))
                    &&
                    ((op_Minus 1000000) < (id #int (Int32.v ((array_read var_dist var_u))))))
                  ==>
                  (((array_read var_dist var_v)) `Int32.lte`
                    (((array_read var_dist var_u)) `Int32.add`
                      ((array_read
                          var_weights
                          ((var_u `SizeT.mul` var_n) `SizeT.add` var_v))))))))))))
  decreases (var_n `SizeT.sub` var_bound)
{
  let mut var_weights = var_weights;
  let mut var_dist = var_dist;
  let mut var_n = var_n;
  let mut var_source = var_source;
  let mut var_bound = var_bound;
  let mut var_result_in = var_result_in;
  if (((!var_n) `SizeT.lte` (!var_bound))) {
    return (!var_result_in);
  } else {};
  let mut var_r : Int32.t;
  var_r := (!var_result_in);
  (func_dijkstra_check_vertex (!var_weights) (!var_dist) (!var_n) (!var_source) (!var_bound) var_r);
  return
    (func_dijkstra_check_all
      (!var_weights)
      (!var_dist)
      (!var_n)
      (!var_source)
      ((!var_bound) `SizeT.add` 1sz)
      (!var_r));
}

#restart-solver

fn func_dijkstra
    (var_weights: (array Int32.t))
    (var_n: SizeT.t)
    (var_source: SizeT.t)
    (var_dist: (array Int32.t))
    (var_pred: (array SizeT.t))
    (var_result: (ref Int32.t))
  requires
    exists* (val_weights_0: (Seq.seq (option Int32.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  requires
    exists* (val_dist_0: (Seq.seq (option Int32.t))) (val_dist_1: (nat->prop)).
    ((array_pts_to var_dist 1.0R val_dist_0 val_dist_1))
  requires
    exists* (val_pred_0: (Seq.seq (option SizeT.t))) (val_pred_1: (nat->prop)).
    ((array_pts_to var_pred 1.0R val_pred_0 val_pred_1))
  requires exists* (val_result_0: Int32.t). ((pts_to var_result #1.0R val_result_0))
  requires (with_pure ((0 < (SizeT.v var_n)) && (var_source `SizeT.lt` var_n)))
  requires (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  requires (with_pure ((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))))
  requires (with_pure ((reveal (length_of var_dist)) = (SizeT.v var_n)))
  requires (with_pure ((reveal (length_of var_pred)) = (SizeT.v var_n)))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          ((0 <= (id #int (Int32.v ((array_read var_weights var_i))))) &&
            ((id #int (Int32.v ((array_read var_weights var_i)))) <= 1000000)))))
  requires (with_pure ((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))))
  requires (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  returns return_1 : unit
  ensures
    exists* (val_weights_0: (Seq.seq (option Int32.t))) (val_weights_1: (nat->prop)).
    ((array_pts_to var_weights 1.0R val_weights_0 val_weights_1))
  ensures
    exists* (val_dist_0: (Seq.seq (option Int32.t))) (val_dist_1: (nat->prop)).
    ((array_pts_to var_dist 1.0R val_dist_0 val_dist_1))
  ensures
    exists* (val_pred_0: (Seq.seq (option SizeT.t))) (val_pred_1: (nat->prop)).
    ((array_pts_to var_pred 1.0R val_pred_0 val_pred_1))
  ensures exists* (val_result_0: Int32.t). ((pts_to var_result #1.0R val_result_0))
  ensures (with_pure ((reveal (length_of var_weights)) = (SizeT.v (var_n `SizeT.mul` var_n))))
  ensures (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  ensures (with_pure ((reveal (length_of var_dist)) = (SizeT.v var_n)))
  ensures (with_pure ((reveal (length_of var_pred)) = (SizeT.v var_n)))
  ensures (with_pure ((id #int (Int32.v ((array_read var_dist var_source)))) = 0))
  ensures (with_pure (((array_read var_pred var_source)) = var_source))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==>
          (((id #int (Int32.v ((array_read var_dist var_v)))) < 1000000) ||
            ((id #int (Int32.v ((array_read var_dist var_v)))) = 1000000)))))
  ensures
    (with_pure
      (forall
        (var_v: SizeT.t).
        ((var_v `SizeT.lt` var_n) ==> (((array_read var_pred var_v)) `SizeT.lt` var_n))))
  ensures
    (with_pure (((id #int (Int32.v (!var_result))) = 0) || ((id #int (Int32.v (!var_result))) = 1)))
  ensures
    (with_pure
      (((id #int (Int32.v (!var_result))) = 1) ==>
        (forall
          (var_u: SizeT.t).
          ((var_u `SizeT.lt` var_n) ==>
            (forall
              (var_v: SizeT.t).
              ((var_v `SizeT.lt` var_n) ==>
                ((((((id
                            #int
                            (Int32.v
                              ((array_read
                                  var_weights
                                  ((var_u `SizeT.mul` var_n) `SizeT.add` var_v)))))
                          <
                          1000000)
                        &&
                        ((op_Minus 1000000) <
                          (id
                            #int
                            (Int32.v
                              ((array_read
                                  var_weights
                                  ((var_u `SizeT.mul` var_n) `SizeT.add` var_v)))))))
                      &&
                      ((id #int (Int32.v ((array_read var_dist var_u)))) < 1000000))
                    &&
                    ((op_Minus 1000000) < (id #int (Int32.v ((array_read var_dist var_u))))))
                  ==>
                  (((array_read var_dist var_v)) `Int32.lte`
                    (((array_read var_dist var_u)) `Int32.add`
                      ((array_read
                          var_weights
                          ((var_u `SizeT.mul` var_n) `SizeT.add` var_v))))))))))))
{
  let mut var_weights = var_weights;
  let mut var_n = var_n;
  let mut var_source = var_source;
  let mut var_dist = var_dist;
  let mut var_pred = var_pred;
  let mut var_result = var_result;
  let mut var_i : SizeT.t;
  var_i := 0sz;
  while (((!var_i) `SizeT.lt` (!var_n)))
    invariant (live var_i)
    invariant (((Pulse.Lib.C.Array.live_array (!var_dist)) **
          (Pulse.Lib.C.Array.live_array (!var_weights)))
        **
        (Pulse.Lib.C.Array.live_array (!var_pred)))
    invariant (with_pure
        ((((reveal (length_of (!var_dist))) = (SizeT.v (!var_n))) &&
            ((reveal (length_of (!var_weights))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n)))))
          &&
          ((reveal (length_of (!var_pred))) = (SizeT.v (!var_n)))))
    invariant (with_pure ((!var_i) `SizeT.lte` (!var_n)))
    invariant (with_pure
        (((!var_source) `SizeT.lt` (!var_i)) ==>
          ((id #int (Int32.v ((array_read (!var_dist) (!var_source))))) = 0)))
    invariant (with_pure
        (((!var_source) `SizeT.lt` (!var_i)) ==>
          (((array_read (!var_pred) (!var_source))) = (!var_source))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_i)) ==>
            ((0 <= (id #int (Int32.v ((array_read (!var_dist) var_j))))) &&
              ((id #int (Int32.v ((array_read (!var_dist) var_j)))) <= 1000000)))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_i)) ==> (((array_read (!var_pred) var_j)) `SizeT.lt` (!var_n)))))
    invariant (with_pure
        (forall
          (var_k: SizeT.t).
          ((var_k `SizeT.lt` ((!var_n) `SizeT.mul` (!var_n))) ==>
            ((0 <= (id #int (Int32.v ((array_read (!var_weights) var_k))))) &&
              ((id #int (Int32.v ((array_read (!var_weights) var_k)))) <= 1000000)))))
  {
    if (((!var_i) = (!var_source))) {
      (array_write (!var_dist) (!var_i) (Int32.int_to_t 0));
      (array_write (!var_pred) (!var_i) (!var_source));
    } else {
      (array_write (!var_dist) (!var_i) (Int32.int_to_t 1000000));
      (array_write (!var_pred) (!var_i) (!var_source));
    };
    var_i := ((!var_i) `SizeT.add` 1sz);
  };
  let mut var_visited : (array Int32.t);
  var_visited := (Pulse.Lib.C.Array.calloc_array_mask #Int32.t (!var_n));
  assert (with_pure ((reveal (length_of (!var_visited))) = (SizeT.v (!var_n))));
  let mut var_iter : SizeT.t;
  var_iter := 0sz;
  while (((!var_iter) `SizeT.lt` (!var_n)))
    invariant (live var_iter)
    invariant ((((Pulse.Lib.C.Array.live_array (!var_dist)) **
            (Pulse.Lib.C.Array.live_array (!var_weights)))
          **
          (Pulse.Lib.C.Array.live_array (!var_pred)))
        **
        (Pulse.Lib.C.Array.live_array (!var_visited)))
    invariant (with_pure
        (((((reveal (length_of (!var_dist))) = (SizeT.v (!var_n))) &&
              ((reveal (length_of (!var_weights))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n)))))
            &&
            ((reveal (length_of (!var_pred))) = (SizeT.v (!var_n))))
          &&
          ((reveal (length_of (!var_visited))) = (SizeT.v (!var_n)))))
    invariant (with_pure (SizeT.fits (SizeT.v (!var_n) * SizeT.v (!var_n))))
    invariant (with_pure ((!var_iter) `SizeT.lte` (!var_n)))
    invariant (with_pure ((id #int (Int32.v ((array_read (!var_dist) (!var_source))))) = 0))
    invariant (with_pure (((array_read (!var_pred) (!var_source))) = (!var_source)))
    invariant (with_pure
        (forall
          (var_v: SizeT.t).
          ((var_v `SizeT.lt` (!var_n)) ==>
            ((0 <= (id #int (Int32.v ((array_read (!var_dist) var_v))))) &&
              ((id #int (Int32.v ((array_read (!var_dist) var_v)))) <= 1000000)))))
    invariant (with_pure
        (forall
          (var_v: SizeT.t).
          ((var_v `SizeT.lt` (!var_n)) ==> (((array_read (!var_pred) var_v)) `SizeT.lt` (!var_n)))))
    invariant (with_pure
        (forall
          (var_k: SizeT.t).
          ((var_k `SizeT.lt` ((!var_n) `SizeT.mul` (!var_n))) ==>
            ((0 <= (id #int (Int32.v ((array_read (!var_weights) var_k))))) &&
              ((id #int (Int32.v ((array_read (!var_weights) var_k)))) <= 1000000)))))
  {
    let mut var_u : SizeT.t;
    var_u := (func_dijkstra_find_min (!var_dist) (!var_visited) (!var_n) (!var_source));
    (func_dijkstra_relax (!var_weights) (!var_dist) (!var_pred) (!var_n) (!var_source) (!var_u));
    var_iter := ((!var_iter) `SizeT.add` 1sz);
  };
  (Pulse.Lib.C.Array.free_array (!var_visited));
  (!var_result) :=
    (func_dijkstra_check_all
      (!var_weights)
      (!var_dist)
      (!var_n)
      (!var_source)
      0sz
      (Int32.int_to_t 1));
}