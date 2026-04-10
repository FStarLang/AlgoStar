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
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_len) ==>
          ((0 <= (id #int (Int32.v ((array_read var_a var_i))))) &&
            (((array_read var_a var_i)) `Int32.lte` var_k_val)))))
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
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_len) ==>
          ((0 <= (id #int (Int32.v ((array_read var_a var_i))))) &&
            (((array_read var_a var_i)) `Int32.lte` var_k_val)))))
{
  let mut var_a = var_a;
  let mut var_len = var_len;
  let mut var_k_val = var_k_val;
  (func_counting_sort (!var_a) (!var_len) (!var_k_val));
}

#restart-solver

fn func_counting_sort_by_digit
    (var_a: (array Int32.t))
    (var_b: (array Int32.t))
    (var_len: SizeT.t)
    (var_base_val: SizeT.t)
    (var_d: SizeT.t)
  requires
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  requires
    exists* (val_b_0: (Seq.seq (option Int32.t))) (val_b_1: (nat->prop)).
    ((array_pts_to var_b 1.0R val_b_0 val_b_1))
  requires (with_pure (2 <= (SizeT.v var_base_val)))
  requires (with_pure (((SizeT.v var_base_val) + 2) <= 2147483647))
  requires (with_pure ((SizeT.v var_len) <= 2147483647))
  requires (with_pure (SizeT.fits (SizeT.v var_base_val + 2)))
  requires (with_pure (SizeT.fits (SizeT.v var_len + SizeT.v var_base_val + 2)))
  requires
    (with_pure
      (((reveal (length_of var_a)) = (SizeT.v var_len)) &&
        ((reveal (length_of var_b)) = (SizeT.v var_len))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_len) ==> (0 <= (id #int (Int32.v ((array_read var_a var_i))))))))
  returns return_1 : unit
  ensures
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  ensures
    exists* (val_b_0: (Seq.seq (option Int32.t))) (val_b_1: (nat->prop)).
    ((array_pts_to var_b 1.0R val_b_0 val_b_1))
  ensures
    (with_pure
      (((reveal (length_of var_a)) = (SizeT.v var_len)) &&
        ((reveal (length_of var_b)) = (SizeT.v var_len))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_len) ==>
          (((array_read var_a var_i)) = (old ((array_read var_a var_i)))))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_len) ==> (0 <= (id #int (Int32.v ((array_read var_b var_i))))))))
{ assume pure False; unreachable () }

#restart-solver

fn func_array_copy (var_a: (array Int32.t)) (var_b: (array Int32.t)) (var_len: SizeT.t)
  requires
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  requires
    exists* (val_b_0: (Seq.seq (option Int32.t))) (val_b_1: (nat->prop)).
    ((array_pts_to var_b 1.0R val_b_0 val_b_1))
  requires (with_pure ((SizeT.v var_len) <= 2147483647))
  requires
    (with_pure
      (((reveal (length_of var_a)) = (SizeT.v var_len)) &&
        ((reveal (length_of var_b)) = (SizeT.v var_len))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_len) ==> (0 <= (id #int (Int32.v ((array_read var_b var_i))))))))
  returns return_1 : unit
  ensures
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  ensures
    exists* (val_b_0: (Seq.seq (option Int32.t))) (val_b_1: (nat->prop)).
    ((array_pts_to var_b 1.0R val_b_0 val_b_1))
  ensures
    (with_pure
      (((reveal (length_of var_a)) = (SizeT.v var_len)) &&
        ((reveal (length_of var_b)) = (SizeT.v var_len))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_len) ==> (((array_read var_a var_i)) = ((array_read var_b var_i))))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_len) ==>
          (((array_read var_b var_i)) = (old ((array_read var_b var_i)))))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_len) ==> (0 <= (id #int (Int32.v ((array_read var_a var_i))))))))
{
  let mut var_a = var_a;
  let mut var_b = var_b;
  let mut var_len = var_len;
  let mut var_j : SizeT.t;
  var_j := 0sz;
  while (((!var_j) `SizeT.lt` (!var_len)))
    invariant (live var_j)
    invariant ((Pulse.Lib.C.Array.live_array (!var_a)) ** (Pulse.Lib.C.Array.live_array (!var_b)))
    invariant (with_pure
        (((reveal (length_of (!var_a))) = (SizeT.v (!var_len))) &&
          ((reveal (length_of (!var_b))) = (SizeT.v (!var_len)))))
    invariant (with_pure ((!var_j) `SizeT.lte` (!var_len)))
    invariant (with_pure ((SizeT.v (!var_len)) <= 2147483647))
    invariant (with_pure
        (forall
          (var_i: SizeT.t).
          ((var_i `SizeT.lt` (!var_len)) ==>
            (0 <= (id #int (Int32.v ((array_read (!var_b) var_i))))))))
    invariant (with_pure
        (forall
          (var_i: SizeT.t).
          ((var_i `SizeT.lt` (!var_j)) ==>
            (((array_read (!var_a) var_i)) = ((array_read (!var_b) var_i))))))
    invariant (with_pure
        (forall
          (var_i: SizeT.t).
          ((var_i `SizeT.lt` (!var_len)) ==>
            (((array_read (!var_b) var_i)) = (old ((array_read (!var_b) var_i)))))))
  {
    (array_write (!var_a) (!var_j) ((array_read (!var_b) (!var_j))));
    var_j := ((!var_j) `SizeT.add` 1sz);
  };
}

#restart-solver

fn func_radix_sort_multidigit
    (var_a: (array Int32.t))
    (var_len: SizeT.t)
    (var_base_val: SizeT.t)
    (var_bigd: SizeT.t)
  requires
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  requires (with_pure (2 <= (SizeT.v var_base_val)))
  requires (with_pure (1 <= (SizeT.v var_bigd)))
  requires (with_pure (((SizeT.v var_base_val) + 2) <= 2147483647))
  requires (with_pure ((SizeT.v var_len) <= 2147483647))
  requires (with_pure (SizeT.fits (SizeT.v var_base_val + 2)))
  requires (with_pure (SizeT.fits (SizeT.v var_len + SizeT.v var_base_val + 2)))
  requires (with_pure ((reveal (length_of var_a)) = (SizeT.v var_len)))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_len) ==> (0 <= (id #int (Int32.v ((array_read var_a var_i))))))))
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
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_len) ==> (0 <= (id #int (Int32.v ((array_read var_a var_i))))))))
{
  let mut var_a = var_a;
  let mut var_len = var_len;
  let mut var_base_val = var_base_val;
  let mut var_bigd = var_bigd;
  if (((!var_len) `SizeT.lte` 1sz)) {
    assume_ (pure false);
    return;
  } else {};
  let mut var_b : (array Int32.t);
  var_b := (Pulse.Lib.C.Array.calloc_array_mask #Int32.t (!var_len));
  assert (with_pure ((reveal (length_of (!var_b))) = (SizeT.v (!var_len))));
  let mut var_d : SizeT.t;
  var_d := 0sz;
  while (((!var_d) `SizeT.lt` (!var_bigd)))
    invariant (live var_d)
    invariant ((Pulse.Lib.C.Array.live_array (!var_a)) ** (Pulse.Lib.C.Array.live_array (!var_b)))
    invariant (with_pure
        (((reveal (length_of (!var_a))) = (SizeT.v (!var_len))) &&
          ((reveal (length_of (!var_b))) = (SizeT.v (!var_len)))))
    invariant (with_pure ((!var_d) `SizeT.lte` (!var_bigd)))
    invariant (with_pure (2 <= (SizeT.v (!var_base_val))))
    invariant (with_pure (1 <= (SizeT.v (!var_bigd))))
    invariant (with_pure (((SizeT.v (!var_base_val)) + 2) <= 2147483647))
    invariant (with_pure ((SizeT.v (!var_len)) <= 2147483647))
    invariant (with_pure (SizeT.fits (SizeT.v (!var_base_val) + 2)))
    invariant (with_pure (SizeT.fits (SizeT.v (!var_len) + SizeT.v (!var_base_val) + 2)))
    invariant (with_pure
        (forall
          (var_i: SizeT.t).
          ((var_i `SizeT.lt` (!var_len)) ==>
            (0 <= (id #int (Int32.v ((array_read (!var_a) var_i))))))))
  {
    (func_counting_sort_by_digit (!var_a) (!var_b) (!var_len) (!var_base_val) (!var_d));
    (func_array_copy (!var_a) (!var_b) (!var_len));
    var_d := ((!var_d) `SizeT.add` 1sz);
  };
  assume_ (pure false);
  (Pulse.Lib.C.Array.free_array (!var_b));
}