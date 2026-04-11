module RodCutting
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

open Pulse.Lib.C.Array

#restart-solver

open CLRS.Ch15.RodCutting.Spec

#restart-solver

open CLRS.Ch15.RodCutting.C.BridgeLemmas

#restart-solver

fn func_rod_cutting (var_prices: (array Int32.t)) (var_n: SizeT.t) (var_r: (array Int32.t))
  requires
    exists* (val_prices_0: (Seq.seq (option Int32.t))) (val_prices_1: (nat->prop)).
    ((array_pts_to var_prices 1.0R val_prices_0 val_prices_1))
  requires
    exists* (val_r_0: (Seq.seq (option Int32.t))) (val_r_1: (nat->prop)).
    ((array_pts_to var_r 1.0R val_r_0 val_r_1))
  requires (with_pure ((reveal (length_of var_prices)) = (SizeT.v var_n)))
  requires (with_pure ((reveal (length_of var_r)) = ((SizeT.v var_n) + 1)))
  requires (with_pure ((SizeT.v var_n) <= 1000))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_n `SizeT.lte` var_i) ||
          ((0 <= (id #int (Int32.v ((array_read var_prices var_i))))) &&
            ((id #int (Int32.v ((array_read var_prices var_i)))) <= 1000000)))))
  returns return_1 : unit
  ensures
    exists* (val_prices_0: (Seq.seq (option Int32.t))) (val_prices_1: (nat->prop)).
    ((array_pts_to var_prices 1.0R val_prices_0 val_prices_1))
  ensures
    exists* (val_r_0: (Seq.seq (option Int32.t))) (val_r_1: (nat->prop)).
    ((array_pts_to var_r 1.0R val_r_0 val_r_1))
  ensures (with_pure ((reveal (length_of var_prices)) = (SizeT.v var_n)))
  ensures (with_pure ((reveal (length_of var_r)) = ((SizeT.v var_n) + 1)))
  ensures (with_pure (Int32.v (array_read var_r 0sz) = 0))
  ensures
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((var_n `SizeT.lt` var_k) || (0 <= (id #int (Int32.v ((array_read var_r var_k))))))))
  ensures
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((var_n `SizeT.lt` var_k) ||
          (Int32.v (array_read var_r var_k) <= 1000000 * SizeT.v var_k))))
  ensures
    (with_pure (
id #int (Int32.v (Some?.v (Seq.index (array_value_of var_r) (SizeT.v var_n)))) =
optimal_revenue (to_nat_seq (array_value_of var_prices)) (SizeT.v var_n)))
{
  let mut var_prices = var_prices;
  let mut var_n = var_n;
  let mut var_r = var_r;
  (array_write (!var_r) 0sz (Int32.int_to_t 0));
  dp_correct_init
(to_nat_seq (array_value_of (!var_prices)))
(to_nat_seq (array_value_of (!var_r)));
  let mut var_j : SizeT.t;
  var_j := 1sz;
  while (((!var_j) `SizeT.lte` (!var_n)))
    invariant (live var_j)
    invariant ((Pulse.Lib.C.Array.live_array (!var_r)) **
        (Pulse.Lib.C.Array.live_array (!var_prices)))
    invariant (with_pure
        (((reveal (length_of (!var_r))) = ((SizeT.v (!var_n)) + 1)) &&
          ((reveal (length_of (!var_prices))) = (SizeT.v (!var_n)))))
    invariant (with_pure
        ((1 <= (SizeT.v (!var_j))) && ((SizeT.v (!var_j)) <= ((SizeT.v (!var_n)) + 1))))
    invariant (with_pure ((SizeT.v (!var_n)) <= 1000))
    invariant (with_pure
        (forall
          (var_ii: SizeT.t).
          (((!var_n) `SizeT.lte` var_ii) ||
            ((0 <= (id #int (Int32.v ((array_read (!var_prices) var_ii))))) &&
              ((id #int (Int32.v ((array_read (!var_prices) var_ii)))) <= 1000000)))))
    invariant (with_pure (Int32.v (array_read (!var_r) 0sz) = 0))
    invariant (with_pure
        (forall
          (var_k: SizeT.t).
          (((!var_j) `SizeT.lte` var_k) ||
            (0 <= (id #int (Int32.v ((array_read (!var_r) var_k))))))))
    invariant (with_pure
        (forall
          (var_k: SizeT.t).
          (((!var_j) `SizeT.lte` var_k) ||
            (Int32.v (array_read (!var_r) var_k) <= 1000000 * SizeT.v var_k))))
    invariant (with_pure (
dp_correct
(to_nat_seq (array_value_of (!var_prices)))
(to_nat_seq (array_value_of (!var_r)))
(SizeT.v (!var_j) - 1)))
  {
    let mut var_q : Int32.t;
    var_q := (Int32.int_to_t 0);
    let mut var_i : SizeT.t;
    var_i := 1sz;
    while (((!var_i) `SizeT.lte` (!var_j)))
      invariant (((live var_i) ** (live var_q)) ** (live var_j))
      invariant ((Pulse.Lib.C.Array.live_array (!var_r)) **
          (Pulse.Lib.C.Array.live_array (!var_prices)))
      invariant (with_pure
          (((reveal (length_of (!var_r))) = ((SizeT.v (!var_n)) + 1)) &&
            ((reveal (length_of (!var_prices))) = (SizeT.v (!var_n)))))
      invariant (with_pure ((1 <= (SizeT.v (!var_j))) && ((!var_j) `SizeT.lte` (!var_n))))
      invariant (with_pure
          ((1 <= (SizeT.v (!var_i))) && ((SizeT.v (!var_i)) <= ((SizeT.v (!var_j)) + 1))))
      invariant (with_pure ((SizeT.v (!var_n)) <= 1000))
      invariant (with_pure
          (forall
            (var_ii: SizeT.t).
            (((!var_n) `SizeT.lte` var_ii) ||
              ((0 <= (id #int (Int32.v ((array_read (!var_prices) var_ii))))) &&
                ((id #int (Int32.v ((array_read (!var_prices) var_ii)))) <= 1000000)))))
      invariant (with_pure (Int32.v (array_read (!var_r) 0sz) = 0))
      invariant (with_pure
          (forall
            (var_k: SizeT.t).
            (((!var_j) `SizeT.lte` var_k) ||
              (0 <= (id #int (Int32.v ((array_read (!var_r) var_k))))))))
      invariant (with_pure
          (forall
            (var_k: SizeT.t).
            (((!var_j) `SizeT.lte` var_k) ||
              (Int32.v (array_read (!var_r) var_k) <= 1000000 * SizeT.v var_k))))
      invariant (with_pure (0 <= (id #int (Int32.v (!var_q)))))
      invariant (with_pure (Int32.v (!var_q) <= 1000000 * SizeT.v (!var_j)))
      invariant (with_pure (
dp_correct
(to_nat_seq (array_value_of (!var_prices)))
(to_nat_seq (array_value_of (!var_r)))
(SizeT.v (!var_j) - 1)))
      invariant (with_pure (
id #int (Int32.v (!var_q)) ==
accum_max
(to_nat_seq (array_value_of (!var_prices)))
(to_nat_seq (array_value_of (!var_r)))
(SizeT.v (!var_j))
(SizeT.v (!var_i) - 1)))
    {
      let mut var_p_val : Int32.t;
      var_p_val := ((array_read (!var_prices) ((!var_i) `SizeT.sub` 1sz)));
      let mut var_r_val : Int32.t;
      var_r_val := ((array_read (!var_r) ((!var_j) `SizeT.sub` (!var_i))));
      assert (with_pure (0 <= (id #int (Int32.v (!var_p_val)))));
      assert (with_pure ((id #int (Int32.v (!var_p_val))) <= 1000000));
      assert (with_pure (0 <= (id #int (Int32.v (!var_r_val)))));
      assert (with_pure ((id #int (Int32.v (!var_r_val))) <= 999000000));
      let mut var_candidate : Int32.t;
      var_candidate := ((!var_p_val) `Int32.add` (!var_r_val));
      if (((!var_q) `Int32.lt` (!var_candidate))) {
        var_q := (!var_candidate);
      } else {};
      var_i := ((!var_i) `SizeT.add` 1sz);
    };
    accum_max_dp_correct
(to_nat_seq (array_value_of (!var_prices)))
(to_nat_seq (array_value_of (!var_r)))
(SizeT.v (!var_j));
    (array_write (!var_r) (!var_j) (!var_q));
    var_j := ((!var_j) `SizeT.add` 1sz);
  };
}