module RadixSort
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

fn func_counting_sort (var_a: (array Int32.t)) (var_len: SizeT.t) (var_k_val: Int32.t)
  requires
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  requires (with_pure (0 <= (id #int (Int32.v var_k_val))))
  requires (with_pure (((id #int (Int32.v var_k_val)) + 2) <= 2147483647))
  requires (with_pure ((SizeT.v var_len) <= 2147483647))
  requires (with_pure (SizeT.fits (Int32.v var_k_val + 2)))
  requires (with_pure ((reveal (length_of var_a)) = (SizeT.v var_len)))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_len) ==>
          ((0 <= (id #int (Int32.v ((array_read var_a var_i))))) &&
            (((array_read var_a var_i)) `Int32.lte` var_k_val)))))
  returns return_1 : unit
  ensures
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  ensures (with_pure ((reveal (length_of var_a)) = (SizeT.v var_len)))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((((SizeT.v var_i) + 1) < (SizeT.v var_len)) ==>
          (((array_read var_a var_i)) `Int32.lte`
            ((array_read var_a (SizeT.uint_to_t ((SizeT.v var_i) + 1))))))))
{ assume pure False; unreachable () }

#restart-solver

fn func_radix_sort (var_a: (array Int32.t)) (var_len: SizeT.t) (var_k_val: Int32.t)
  requires
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  requires (with_pure (0 <= (id #int (Int32.v var_k_val))))
  requires (with_pure (((id #int (Int32.v var_k_val)) + 2) <= 2147483647))
  requires (with_pure ((SizeT.v var_len) <= 2147483647))
  requires (with_pure (SizeT.fits (Int32.v var_k_val + 2)))
  requires (with_pure ((reveal (length_of var_a)) = (SizeT.v var_len)))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_len) ==>
          ((0 <= (id #int (Int32.v ((array_read var_a var_i))))) &&
            (((array_read var_a var_i)) `Int32.lte` var_k_val)))))
  returns return_1 : unit
  ensures
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  ensures (with_pure ((reveal (length_of var_a)) = (SizeT.v var_len)))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((((SizeT.v var_i) + 1) < (SizeT.v var_len)) ==>
          (((array_read var_a var_i)) `Int32.lte`
            ((array_read var_a (SizeT.uint_to_t ((SizeT.v var_i) + 1))))))))
{
  let mut var_a = var_a;
  let mut var_len = var_len;
  let mut var_k_val = var_k_val;
  (func_counting_sort (!var_a) (!var_len) (!var_k_val));
}