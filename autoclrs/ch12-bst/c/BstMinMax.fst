module BstMinMax
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

fn rec func_bst_minimum
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
  requires
    (with_pure
      (forall
        (var_j: SizeT.t).
        (((((var_j `SizeT.lt` var_cap) &&
                (not ((id #int (Int32.v ((array_read var_valid var_j)))) = 0)))
              &&
              (((2 `op_Multiply` (SizeT.v var_j)) + 1) < (SizeT.v var_cap)))
            &&
            (not
              ((id
                  #int
                  (Int32.v
                    ((array_read
                        var_valid
                        (SizeT.uint_to_t ((2 `op_Multiply` (SizeT.v var_j)) + 1))))))
                =
                0)))
          ==>
          (((array_read var_keys (SizeT.uint_to_t ((2 `op_Multiply` (SizeT.v var_j)) + 1))))
            `Int32.lt`
            ((array_read var_keys var_j))))))
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
  ensures (with_pure (return_1 `Int32.lte` ((array_read var_keys var_i))))
  decreases (var_cap `SizeT.sub` var_i)
{
  let mut var_keys = var_keys;
  let mut var_valid = var_valid;
  let mut var_cap = var_cap;
  let mut var_i = var_i;
  let mut var_left : SizeT.t;
  var_left := ((2sz `SizeT.mul` (!var_i)) `SizeT.add` 1sz);
  if (((!var_cap) `SizeT.lte` (!var_left))) {
    return ((array_read (!var_keys) (!var_i)));
  } else {};
  if ((((array_read (!var_valid) (!var_left))) = (Int32.int_to_t 0))) {
    return ((array_read (!var_keys) (!var_i)));
  } else {};
  return (func_bst_minimum (!var_keys) (!var_valid) (!var_cap) (!var_left));
}

#restart-solver

fn rec func_bst_maximum
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
  requires
    (with_pure
      (forall
        (var_j: SizeT.t).
        (((((var_j `SizeT.lt` var_cap) &&
                (not ((id #int (Int32.v ((array_read var_valid var_j)))) = 0)))
              &&
              (((2 `op_Multiply` (SizeT.v var_j)) + 2) < (SizeT.v var_cap)))
            &&
            (not
              ((id
                  #int
                  (Int32.v
                    ((array_read
                        var_valid
                        (SizeT.uint_to_t ((2 `op_Multiply` (SizeT.v var_j)) + 2))))))
                =
                0)))
          ==>
          (((array_read var_keys var_j)) `Int32.lt`
            ((array_read var_keys (SizeT.uint_to_t ((2 `op_Multiply` (SizeT.v var_j)) + 2))))))))
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
  ensures (with_pure (((array_read var_keys var_i)) `Int32.lte` return_1))
  decreases (var_cap `SizeT.sub` var_i)
{
  let mut var_keys = var_keys;
  let mut var_valid = var_valid;
  let mut var_cap = var_cap;
  let mut var_i = var_i;
  let mut var_right : SizeT.t;
  var_right := ((2sz `SizeT.mul` (!var_i)) `SizeT.add` 2sz);
  if (((!var_cap) `SizeT.lte` (!var_right))) {
    return ((array_read (!var_keys) (!var_i)));
  } else {};
  if ((((array_read (!var_valid) (!var_right))) = (Int32.int_to_t 0))) {
    return ((array_read (!var_keys) (!var_i)));
  } else {};
  return (func_bst_maximum (!var_keys) (!var_valid) (!var_cap) (!var_right));
}