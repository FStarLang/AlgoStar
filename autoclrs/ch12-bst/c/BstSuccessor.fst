module BstSuccessor
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
{
  let mut var_keys = var_keys;
  let mut var_valid = var_valid;
  let mut var_cap = var_cap;
  let mut var_i = var_i;
  let mut var_left : SizeT.t;
  var_left := ((2sz `SizeT.mul` (!var_i)) `SizeT.add` 1sz);
  if (((!var_cap) `SizeT.lte` (!var_left))) {
    return (!var_i);
  } else {};
  if ((((array_read (!var_valid) (!var_left))) = (Int32.int_to_t 0))) {
    return (!var_i);
  } else {};
  return (func_bst_minimum_idx (!var_keys) (!var_valid) (!var_cap) (!var_left));
}

#restart-solver

fn rec func_walk_up_right
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
  requires (with_pure (var_i `SizeT.lt` var_cap))
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
  ensures (with_pure (return_1 `SizeT.lte` var_cap))
  ensures
    (with_pure
      ((return_1 `SizeT.lt` var_cap) ==>
        (not ((id #int (Int32.v ((array_read var_valid return_1)))) = 0))))
  decreases var_i
{
  let mut var_keys = var_keys;
  let mut var_valid = var_valid;
  let mut var_cap = var_cap;
  let mut var_i = var_i;
  if (((!var_i) = 0sz)) {
    return (!var_cap);
  } else {};
  let mut var_parent : SizeT.t;
  var_parent := (((!var_i) `SizeT.sub` 1sz) `SizeT.div` 2sz);
  if ((((!var_i) `SizeT.rem` 2sz) = 1sz)) {
    if (((!var_parent) `SizeT.lt` (!var_cap))) {
      if ((not (((array_read (!var_valid) (!var_parent))) = (Int32.int_to_t 0)))) {
        return (!var_parent);
      } else {};
    } else {};
    return (!var_cap);
  } else {};
  return (func_walk_up_right (!var_keys) (!var_valid) (!var_cap) (!var_parent));
}

#restart-solver

fn func_bst_successor
    (var_keys: (array Int32.t))
    (var_valid: (array Int32.t))
    (var_cap: SizeT.t)
    (var_idx: SizeT.t)
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
      ((var_idx `SizeT.lt` var_cap) &&
        (not ((id #int (Int32.v ((array_read var_valid var_idx)))) = 0))))
  requires
    (with_pure (c_valid_bst (array_value_of var_keys) (array_value_of var_valid) (SizeT.v var_cap)))
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
  ensures (with_pure (return_1 `SizeT.lte` var_cap))
  ensures
    (with_pure
      ((return_1 `SizeT.lt` var_cap) ==>
        (not ((id #int (Int32.v ((array_read var_valid return_1)))) = 0))))
{
  let mut var_keys = var_keys;
  let mut var_valid = var_valid;
  let mut var_cap = var_cap;
  let mut var_idx = var_idx;
  let mut var_right : SizeT.t;
  var_right := ((2sz `SizeT.mul` (!var_idx)) `SizeT.add` 2sz);
  if (((!var_right) `SizeT.lt` (!var_cap))) {
    if ((not (((array_read (!var_valid) (!var_right))) = (Int32.int_to_t 0)))) {
      return (func_bst_minimum_idx (!var_keys) (!var_valid) (!var_cap) (!var_right));
    } else {};
  } else {};
  return (func_walk_up_right (!var_keys) (!var_valid) (!var_cap) (!var_idx));
}