module BstDelete
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

open CLRS.Ch12.BST.C.BridgeLemmas

#restart-solver

fn rec func_bst_minimum_idx
    (var_keys: (array Int32.t))
    (var_valid: (array Int32.t))
    (var_cap: SizeT.t)
    (var_i: SizeT.t)
  requires
    exists* (val_keys_0: (Seq.seq (option Int32.t))) (val_keys_1: (nat->prop)).
    ((array_pts_to var_keys 1.0R val_keys_0 val_keys_1))
  requires
    exists* (val_valid_0: (Seq.seq (option Int32.t))) (val_valid_1: (nat->prop)).
    ((array_pts_to var_valid 1.0R val_valid_0 val_valid_1))
  requires
    (with_pure
      (((reveal (length_of var_keys)) = (SizeT.v var_cap)) &&
        ((reveal (length_of var_valid)) = (SizeT.v var_cap))))
  requires (with_pure ((0 < (SizeT.v var_cap)) && ((SizeT.v var_cap) < 32768)))
  requires
    (with_pure
      ((var_i `SizeT.lt` var_cap) &&
        (not ((id #int (Int32.v ((array_read var_valid var_i)))) = 0))))
  returns return_1 : SizeT.t
  ensures
    exists* (val_keys_0: (Seq.seq (option Int32.t))) (val_keys_1: (nat->prop)).
    ((array_pts_to var_keys 1.0R val_keys_0 val_keys_1))
  ensures
    exists* (val_valid_0: (Seq.seq (option Int32.t))) (val_valid_1: (nat->prop)).
    ((array_pts_to var_valid 1.0R val_valid_0 val_valid_1))
  ensures (with_pure ((reveal (length_of var_keys)) = (old (reveal (length_of var_keys)))))
  ensures (with_pure ((reveal (length_of var_valid)) = (old (reveal (length_of var_valid)))))
  ensures
    (with_pure
      (forall
        (var_j: SizeT.t).
        ((var_j `SizeT.lt` var_cap) ==>
          (((array_read var_keys var_j)) = (old ((array_read var_keys var_j)))))))
  ensures
    (with_pure
      (forall
        (var_j: SizeT.t).
        ((var_j `SizeT.lt` var_cap) ==>
          (((array_read var_valid var_j)) = (old ((array_read var_valid var_j)))))))
  ensures
    (with_pure
      ((return_1 `SizeT.lt` var_cap) &&
        (not ((id #int (Int32.v ((array_read var_valid return_1)))) = 0))))
  decreases (var_cap `SizeT.sub` var_i)
{ assume pure False; unreachable () }

#restart-solver

fn func_bst_delete
    (var_keys: (array Int32.t))
    (var_valid: (array Int32.t))
    (var_cap: SizeT.t)
    (var_del_idx: SizeT.t)
  requires
    exists* (val_keys_0: (Seq.seq (option Int32.t))) (val_keys_1: (nat->prop)).
    ((array_pts_to var_keys 1.0R val_keys_0 val_keys_1))
  requires
    exists* (val_valid_0: (Seq.seq (option Int32.t))) (val_valid_1: (nat->prop)).
    ((array_pts_to var_valid 1.0R val_valid_0 val_valid_1))
  requires
    (with_pure
      (((reveal (length_of var_keys)) = (SizeT.v var_cap)) &&
        ((reveal (length_of var_valid)) = (SizeT.v var_cap))))
  requires (with_pure ((0 < (SizeT.v var_cap)) && ((SizeT.v var_cap) < 32768)))
  requires
    (with_pure
      ((var_del_idx `SizeT.lt` var_cap) &&
        (not ((id #int (Int32.v ((array_read var_valid var_del_idx)))) = 0))))
  requires
    (with_pure (c_valid_bst (array_value_of var_keys) (array_value_of var_valid) (SizeT.v var_cap)))
  returns return_1 : Int32.t
  ensures
    exists* (val_keys_0: (Seq.seq (option Int32.t))) (val_keys_1: (nat->prop)).
    ((array_pts_to var_keys 1.0R val_keys_0 val_keys_1))
  ensures
    exists* (val_valid_0: (Seq.seq (option Int32.t))) (val_valid_1: (nat->prop)).
    ((array_pts_to var_valid 1.0R val_valid_0 val_valid_1))
  ensures (with_pure ((reveal (length_of var_keys)) = (old (reveal (length_of var_keys)))))
  ensures (with_pure ((reveal (length_of var_valid)) = (old (reveal (length_of var_valid)))))
  ensures
    (with_pure
      (((id #int (Int32.v return_1)) = 0) ==>
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` var_cap) ==>
            (((array_read var_keys var_j)) = (old ((array_read var_keys var_j))))))))
  ensures
    (with_pure
      (((id #int (Int32.v return_1)) = 0) ==>
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` var_cap) ==>
            (((array_read var_valid var_j)) = (old ((array_read var_valid var_j))))))))
{
  let mut var_keys = var_keys;
  let mut var_valid = var_valid;
  let mut var_cap = var_cap;
  let mut var_del_idx = var_del_idx;
  let mut var_left : SizeT.t;
  var_left := ((2sz `SizeT.mul` (!var_del_idx)) `SizeT.add` 1sz);
  let mut var_right : SizeT.t;
  var_right := ((2sz `SizeT.mul` (!var_del_idx)) `SizeT.add` 2sz);
  let mut var_has_left : Int32.t;
  var_has_left := (Int32.int_to_t 0);
  if (((!var_left) `SizeT.lt` (!var_cap))) {
    if ((not (((array_read (!var_valid) (!var_left))) = (Int32.int_to_t 0)))) {
      var_has_left := (Int32.int_to_t 1);
    } else {};
  } else {};
  let mut var_has_right : Int32.t;
  var_has_right := (Int32.int_to_t 0);
  if (((!var_right) `SizeT.lt` (!var_cap))) {
    if ((not (((array_read (!var_valid) (!var_right))) = (Int32.int_to_t 0)))) {
      var_has_right := (Int32.int_to_t 1);
    } else {};
  } else {};
  if (((!var_has_left) = (Int32.int_to_t 0))) {
    if (((!var_has_right) = (Int32.int_to_t 0))) {
      (array_write (!var_valid) (!var_del_idx) (Int32.int_to_t 0));
      return (Int32.int_to_t 1);
    } else {};
  } else {};
  if (((!var_has_right) = (Int32.int_to_t 0))) {
    return (Int32.int_to_t 0);
  } else {};
  let mut var_succ_idx : SizeT.t;
  var_succ_idx := (func_bst_minimum_idx (!var_keys) (!var_valid) (!var_cap) (!var_right));
  let mut var_succ_right : SizeT.t;
  var_succ_right := ((2sz `SizeT.mul` (!var_succ_idx)) `SizeT.add` 2sz);
  let mut var_succ_has_right : Int32.t;
  var_succ_has_right := (Int32.int_to_t 0);
  if (((!var_succ_right) `SizeT.lt` (!var_cap))) {
    if ((not (((array_read (!var_valid) (!var_succ_right))) = (Int32.int_to_t 0)))) {
      var_succ_has_right := (Int32.int_to_t 1);
    } else {};
  } else {};
  if ((not ((!var_succ_has_right) = (Int32.int_to_t 0)))) {
    return (Int32.int_to_t 0);
  } else {};
  let mut var_succ_key : Int32.t;
  var_succ_key := ((array_read (!var_keys) (!var_succ_idx)));
  (array_write (!var_keys) (!var_del_idx) (!var_succ_key));
  (array_write (!var_valid) (!var_succ_idx) (Int32.int_to_t 0));
  return (Int32.int_to_t 1);
}