module BstSearch
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

open CLRS.Ch12.BST.C.BridgeLemmas

#restart-solver

fn rec func_bst_search
    (var_keys: (array Int32.t))
    (var_valid: (array Int32.t))
    (var_cap: SizeT.t)
    (var_key: Int32.t)
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
  requires (with_pure (var_i `SizeT.lte` var_cap))
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
  ensures (with_pure (return_1 `SizeT.lte` var_cap))
  ensures
    (with_pure
      ((return_1 `SizeT.lt` var_cap) ==>
        ((((array_read var_keys return_1)) = var_key) &&
          (not ((id #int (Int32.v ((array_read var_valid return_1)))) = 0)))))
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
  decreases (var_cap `SizeT.sub` var_i)
{
  let mut var_keys = var_keys;
  let mut var_valid = var_valid;
  let mut var_cap = var_cap;
  let mut var_key = var_key;
  let mut var_i = var_i;
  if (((!var_cap) `SizeT.lte` (!var_i))) {
    return (!var_cap);
  } else {};
  if ((((array_read (!var_valid) (!var_i))) = (Int32.int_to_t 0))) {
    return (!var_cap);
  } else {};
  if ((((array_read (!var_keys) (!var_i))) = (!var_key))) {
    return (!var_i);
  } else {};
  if (((!var_key) `Int32.lt` ((array_read (!var_keys) (!var_i))))) {
    let mut var_left : SizeT.t;
    var_left := ((2sz `SizeT.mul` (!var_i)) `SizeT.add` 1sz);
    if (((!var_cap) `SizeT.lte` (!var_left))) {
      return (!var_cap);
    } else {};
    return (func_bst_search (!var_keys) (!var_valid) (!var_cap) (!var_key) (!var_left));
  } else {
    let mut var_right : SizeT.t;
    var_right := ((2sz `SizeT.mul` (!var_i)) `SizeT.add` 2sz);
    if (((!var_cap) `SizeT.lte` (!var_right))) {
      return (!var_cap);
    } else {};
    return (func_bst_search (!var_keys) (!var_valid) (!var_cap) (!var_key) (!var_right));
  };
}