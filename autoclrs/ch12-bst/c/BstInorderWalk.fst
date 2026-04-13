module BstInorderWalk
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

open CLRS.Ch12.BST.C.BridgeLemmas

#restart-solver

fn rec func_bst_inorder_walk
    (var_keys: (array Int32.t))
    (var_valid: (array Int32.t))
    (var_cap: SizeT.t)
    (var_i: SizeT.t)
    (var_output: (array Int32.t))
    (var_write_pos: (ref SizeT.t))
    (var_out_len: SizeT.t)
  requires
    exists* (val_keys_0: (Seq.seq (option Int32.t))) (val_keys_1: (nat->prop)).
    ((array_pts_to var_keys 1.0R val_keys_0 val_keys_1))
  requires
    exists* (val_valid_0: (Seq.seq (option Int32.t))) (val_valid_1: (nat->prop)).
    ((array_pts_to var_valid 1.0R val_valid_0 val_valid_1))
  requires
    exists* (val_output_0: (Seq.seq (option Int32.t))) (val_output_1: (nat->prop)).
    ((array_pts_to var_output 1.0R val_output_0 val_output_1))
  requires exists* (val_write_pos_0: SizeT.t). ((pts_to var_write_pos #1.0R val_write_pos_0))
  requires
    (with_pure
      (((reveal (length_of var_keys)) = (SizeT.v var_cap)) &&
        ((reveal (length_of var_valid)) = (SizeT.v var_cap))))
  requires (with_pure ((reveal (length_of var_output)) = (SizeT.v var_out_len)))
  requires (with_pure ((0 < (SizeT.v var_cap)) && ((SizeT.v var_cap) < 32768)))
  requires (with_pure ((SizeT.v var_i) <= (2 `op_Multiply` (SizeT.v var_cap))))
  requires (with_pure ((!var_write_pos) `SizeT.lte` var_out_len))
  returns return_1 : unit
  ensures
    exists* (val_keys_0: (Seq.seq (option Int32.t))) (val_keys_1: (nat->prop)).
    ((array_pts_to var_keys 1.0R val_keys_0 val_keys_1))
  ensures
    exists* (val_valid_0: (Seq.seq (option Int32.t))) (val_valid_1: (nat->prop)).
    ((array_pts_to var_valid 1.0R val_valid_0 val_valid_1))
  ensures
    exists* (val_output_0: (Seq.seq (option Int32.t))) (val_output_1: (nat->prop)).
    ((array_pts_to var_output 1.0R val_output_0 val_output_1))
  ensures exists* (val_write_pos_0: SizeT.t). ((pts_to var_write_pos #1.0R val_write_pos_0))
  ensures (with_pure ((reveal (length_of var_keys)) = (old (reveal (length_of var_keys)))))
  ensures (with_pure ((reveal (length_of var_valid)) = (old (reveal (length_of var_valid)))))
  ensures (with_pure ((reveal (length_of var_output)) = (old (reveal (length_of var_output)))))
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
  ensures (with_pure ((!var_write_pos) `SizeT.lte` var_out_len))
  decreases ((2 `op_Multiply` (SizeT.v var_cap)) - (SizeT.v var_i))
{
  let mut var_keys = var_keys;
  let mut var_valid = var_valid;
  let mut var_cap = var_cap;
  let mut var_i = var_i;
  let mut var_output = var_output;
  let mut var_write_pos = var_write_pos;
  let mut var_out_len = var_out_len;
  if (((!var_cap) `SizeT.lte` (!var_i))) {
    return;
  } else {};
  if ((((array_read (!var_valid) (!var_i))) = (Int32.int_to_t 0))) {
    return;
  } else {};
  let mut var_left : SizeT.t;
  var_left := ((2sz `SizeT.mul` (!var_i)) `SizeT.add` 1sz);
  (func_bst_inorder_walk
      (!var_keys)
      (!var_valid)
      (!var_cap)
      (!var_left)
      (!var_output)
      (!var_write_pos)
      (!var_out_len));
  let mut var_wp : SizeT.t;
  var_wp := (!(!var_write_pos));
  if (((!var_wp) `SizeT.lt` (!var_out_len))) {
    (array_write (!var_output) (!var_wp) ((array_read (!var_keys) (!var_i))));
    (!var_write_pos) := ((!var_wp) `SizeT.add` 1sz);
  } else {};
  let mut var_right : SizeT.t;
  var_right := ((2sz `SizeT.mul` (!var_i)) `SizeT.add` 2sz);
  (func_bst_inorder_walk
      (!var_keys)
      (!var_valid)
      (!var_cap)
      (!var_right)
      (!var_output)
      (!var_write_pos)
      (!var_out_len));
}