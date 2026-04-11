module Lcs
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

open Pulse.Lib.C.Array

#restart-solver

open CLRS.Ch15.LCS.Spec

#restart-solver

open CLRS.Ch15.LCS.C.BridgeLemmas

#restart-solver

fn func_lcs
    (var_x: (array Int32.t))
    (var_m: SizeT.t)
    (var_y: (array Int32.t))
    (var_n: SizeT.t)
    (var_tbl: (array Int32.t))
  requires
    exists* (val_x_0: (Seq.seq (option Int32.t))) (val_x_1: (nat->prop)).
    ((array_pts_to var_x 1.0R val_x_0 val_x_1))
  requires
    exists* (val_y_0: (Seq.seq (option Int32.t))) (val_y_1: (nat->prop)).
    ((array_pts_to var_y 1.0R val_y_0 val_y_1))
  requires
    exists* (val_tbl_0: (Seq.seq (option Int32.t))) (val_tbl_1: (nat->prop)).
    ((array_pts_to var_tbl 1.0R val_tbl_0 val_tbl_1))
  requires (with_pure ((reveal (length_of var_x)) = (SizeT.v var_m)))
  requires (with_pure ((reveal (length_of var_y)) = (SizeT.v var_n)))
  requires (with_pure ((1 <= (SizeT.v var_m)) && ((SizeT.v var_m) <= 1000)))
  requires (with_pure ((1 <= (SizeT.v var_n)) && ((SizeT.v var_n) <= 1000)))
  requires (with_pure (SizeT.fits ((SizeT.v var_m + 1) * (SizeT.v var_n + 1))))
  requires (with_pure (reveal (length_of var_tbl) = (SizeT.v var_m + 1) * (SizeT.v var_n + 1)))
  returns return_1 : Int32.t
  ensures
    exists* (val_x_0: (Seq.seq (option Int32.t))) (val_x_1: (nat->prop)).
    ((array_pts_to var_x 1.0R val_x_0 val_x_1))
  ensures
    exists* (val_y_0: (Seq.seq (option Int32.t))) (val_y_1: (nat->prop)).
    ((array_pts_to var_y 1.0R val_y_0 val_y_1))
  ensures
    exists* (val_tbl_0: (Seq.seq (option Int32.t))) (val_tbl_1: (nat->prop)).
    ((array_pts_to var_tbl 1.0R val_tbl_0 val_tbl_1))
  ensures (with_pure ((reveal (length_of var_x)) = (SizeT.v var_m)))
  ensures (with_pure ((reveal (length_of var_y)) = (SizeT.v var_n)))
  ensures (with_pure (reveal (length_of var_tbl) = (SizeT.v var_m + 1) * (SizeT.v var_n + 1)))
  ensures (with_pure (0 <= (id #int (Int32.v return_1))))
  ensures (with_pure ((id #int (Int32.v return_1)) <= 1000))
  ensures
    (with_pure
      (forall
        (var_k: SizeT.t).
        ((SizeT.v var_k >= (SizeT.v var_m + 1) * (SizeT.v var_n + 1)) ||
          (0 <= (id #int (Int32.v ((array_read var_tbl var_k))))))))
  ensures
    (with_pure (
id #int (Int32.v return_1) =
lcs_length
(to_int_seq (array_value_of var_x))
(to_int_seq (array_value_of var_y))
(SizeT.v var_m) (SizeT.v var_n)))
{
  let var_n1 = (var_n `SizeT.add` 1sz);
  let mut var_i : SizeT.t;
  var_i := 0sz;
  while (((!var_i) `SizeT.lte` var_m))
    invariant (live var_i)
    invariant (((Pulse.Lib.C.Array.live_array var_tbl) **
          (Pulse.Lib.C.Array.live_array var_x))
        **
        (Pulse.Lib.C.Array.live_array var_y))
    invariant (with_pure ((SizeT.v (!var_i)) <= ((SizeT.v var_m) + 1)))
    invariant (with_pure ((1 <= (SizeT.v var_m)) && ((SizeT.v var_m) <= 1000)))
    invariant (with_pure ((1 <= (SizeT.v var_n)) && ((SizeT.v var_n) <= 1000)))
    invariant (with_pure
        (((reveal (length_of var_x)) = (SizeT.v var_m)) &&
          ((reveal (length_of var_y)) = (SizeT.v var_n))))
    invariant (with_pure (SizeT.fits ((SizeT.v var_m + 1) * (SizeT.v var_n + 1))))
    invariant (with_pure
        (reveal (length_of var_tbl) = (SizeT.v var_m + 1) * (SizeT.v var_n + 1)))
    invariant (with_pure
        (forall
          (var_k: SizeT.t).
          ((SizeT.v var_k >= SizeT.v (!var_i) * (SizeT.v var_n + 1)) ||
            (0 <= (id #int (Int32.v ((array_read var_tbl var_k))))))))
    invariant (with_pure
        (forall
          (var_k: SizeT.t).
          ((SizeT.v var_k >= SizeT.v (!var_i) * (SizeT.v var_n + 1)) ||
            ((id #int (Int32.v ((array_read var_tbl var_k)))) <= 1000))))
    invariant (with_pure (
lcs_table_correct
(to_int_seq (array_value_of var_x))
(to_int_seq (array_value_of var_y))
(to_int_seq (array_value_of var_tbl))
(SizeT.v var_m) (SizeT.v var_n)
(SizeT.v (!var_i)) 0))
  {
    let mut var_j : SizeT.t;
    var_j := 0sz;
    while (((!var_j) `SizeT.lte` var_n))
      invariant ((live var_j) ** (live var_i))
      invariant (((Pulse.Lib.C.Array.live_array var_tbl) **
            (Pulse.Lib.C.Array.live_array var_x))
          **
          (Pulse.Lib.C.Array.live_array var_y))
      invariant (with_pure ((!var_i) `SizeT.lte` var_m))
      invariant (with_pure ((SizeT.v (!var_j)) <= ((SizeT.v var_n) + 1)))
      invariant (with_pure ((1 <= (SizeT.v var_m)) && ((SizeT.v var_m) <= 1000)))
      invariant (with_pure ((1 <= (SizeT.v var_n)) && ((SizeT.v var_n) <= 1000)))
      invariant (with_pure
          (((reveal (length_of var_x)) = (SizeT.v var_m)) &&
            ((reveal (length_of var_y)) = (SizeT.v var_n))))
      invariant (with_pure (SizeT.fits ((SizeT.v var_m + 1) * (SizeT.v var_n + 1))))
      invariant (with_pure
          (reveal (length_of var_tbl) = (SizeT.v var_m + 1) * (SizeT.v var_n + 1)))
      invariant (with_pure
          (forall
            (var_k: SizeT.t).
            ((SizeT.v var_k >= SizeT.v (!var_i) * (SizeT.v var_n + 1) + SizeT.v (!var_j)) ||
              (0 <= (id #int (Int32.v ((array_read var_tbl var_k))))))))
      invariant (with_pure
          (forall
            (var_k: SizeT.t).
            ((SizeT.v var_k >= SizeT.v (!var_i) * (SizeT.v var_n + 1) + SizeT.v (!var_j)) ||
              ((id #int (Int32.v ((array_read var_tbl var_k)))) <= 1000))))
      invariant (with_pure (
lcs_table_correct
(to_int_seq (array_value_of var_x))
(to_int_seq (array_value_of var_y))
(to_int_seq (array_value_of var_tbl))
(SizeT.v var_m) (SizeT.v var_n)
(SizeT.v (!var_i)) (SizeT.v (!var_j))))
    {
      let var_idx = (((!var_i) `SizeT.mul` var_n1) `SizeT.add` (!var_j));
      lcs_table_diag_bound_opt
(to_int_seq (array_value_of var_x))
(to_int_seq (array_value_of var_y))
(to_int_seq (array_value_of var_tbl))
(SizeT.v var_m) (SizeT.v var_n)
(SizeT.v (!var_i)) (SizeT.v (!var_j));
      let mut var_diag_val : Int32.t;
      var_diag_val := (Int32.int_to_t 0);
      let mut var_up_val : Int32.t;
      var_up_val := (Int32.int_to_t 0);
      let mut var_left_val : Int32.t;
      var_left_val := (Int32.int_to_t 0);
      let mut var_xi_val : Int32.t;
      var_xi_val := (Int32.int_to_t 0);
      let mut var_yj_val : Int32.t;
      var_yj_val := (Int32.int_to_t 0);
      let mut var_value : Int32.t;
      var_value := (Int32.int_to_t 0);
      if (((0sz `SizeT.lt` (!var_i)) && (0sz `SizeT.lt` (!var_j)))) {
        var_diag_val :=
          ((array_read var_tbl ((var_idx `SizeT.sub` var_n1) `SizeT.sub` 1sz)));
        var_up_val := ((array_read var_tbl (var_idx `SizeT.sub` var_n1)));
        var_left_val := ((array_read var_tbl (var_idx `SizeT.sub` 1sz)));
        assert (with_pure (0 <= (id #int (Int32.v (!var_diag_val)))));
        assert (with_pure ((id #int (Int32.v (!var_diag_val))) <= 999));
        assert (with_pure (0 <= (id #int (Int32.v (!var_up_val)))));
        assert (with_pure ((id #int (Int32.v (!var_up_val))) <= 1000));
        assert (with_pure (0 <= (id #int (Int32.v (!var_left_val)))));
        assert (with_pure ((id #int (Int32.v (!var_left_val))) <= 1000));
        var_xi_val := ((array_read var_x ((!var_i) `SizeT.sub` 1sz)));
        var_yj_val := ((array_read var_y ((!var_j) `SizeT.sub` 1sz)));
        if (((!var_xi_val) = (!var_yj_val))) {
          var_value := ((!var_diag_val) `Int32.add` (Int32.int_to_t 1));
        } else {
          if (((!var_left_val) `Int32.lte` (!var_up_val))) {
            var_value := (!var_up_val);
          } else {
            var_value := (!var_left_val);
          };
        };
      } else {};
      lcs_step_correct
(to_int_seq (array_value_of var_x))
(to_int_seq (array_value_of var_y))
(to_int_seq (array_value_of var_tbl))
(SizeT.v var_m) (SizeT.v var_n)
(SizeT.v (!var_i)) (SizeT.v (!var_j))
(Int32.v (!var_value));
      lcs_table_update_preserves
(to_int_seq (array_value_of var_x))
(to_int_seq (array_value_of var_y))
(to_int_seq (array_value_of var_tbl))
(SizeT.v var_m) (SizeT.v var_n)
(SizeT.v (!var_i)) (SizeT.v (!var_j))
(Int32.v (!var_value));
      (array_write var_tbl var_idx (!var_value));
      var_j := ((!var_j) `SizeT.add` 1sz);
    };
    lcs_table_next_row
(to_int_seq (array_value_of var_x))
(to_int_seq (array_value_of var_y))
(to_int_seq (array_value_of var_tbl))
(SizeT.v var_m) (SizeT.v var_n)
(SizeT.v (!var_i));
    var_i := ((!var_i) `SizeT.add` 1sz);
  };
  lcs_table_result
(to_int_seq (array_value_of var_x))
(to_int_seq (array_value_of var_y))
(to_int_seq (array_value_of var_tbl))
(SizeT.v var_m) (SizeT.v var_n);
  let var_last_idx = ((var_m `SizeT.mul` var_n1) `SizeT.add` var_n);
  let var_result = ((array_read var_tbl var_last_idx));
  assert (with_pure (0 <= (id #int (Int32.v var_result))));
  assert (with_pure ((id #int (Int32.v var_result)) <= 1000));
  return var_result;
}