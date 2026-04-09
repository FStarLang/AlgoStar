module CountingSort
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

fn func_count_occurrences
    (var_c: (array Int32.t))
    (var_a: (array Int32.t))
    (var_len: SizeT.t)
    (var_k_plus_1: SizeT.t)
    (var_k_val: Int32.t)
  requires
    exists* (val_c_0: (Seq.seq (option Int32.t))) (val_c_1: (nat->prop)).
    ((array_pts_to var_c 1.0R val_c_0 val_c_1))
  requires
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  requires (with_pure (0 <= (id #int (Int32.v var_k_val))))
  requires (with_pure (((id #int (Int32.v var_k_val)) + 2) <= 2147483647))
  requires (with_pure ((SizeT.v var_len) <= 2147483647))
  requires (with_pure ((SizeT.v var_k_plus_1) = ((id #int (Int32.v var_k_val)) + 1)))
  requires (with_pure (SizeT.fits (Int32.v var_k_val + 2)))
  requires
    (with_pure
      (((reveal (length_of var_c)) = (SizeT.v var_k_plus_1)) &&
        ((reveal (length_of var_a)) = (SizeT.v var_len))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_len) ==>
          ((0 <= (id #int (Int32.v ((array_read var_a var_i))))) &&
            (((array_read var_a var_i)) `Int32.lte` var_k_val)))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_k_plus_1) ==> ((id #int (Int32.v ((array_read var_c var_i)))) = 0))))
  returns return_1 : unit
  ensures
    exists* (val_c_0: (Seq.seq (option Int32.t))) (val_c_1: (nat->prop)).
    ((array_pts_to var_c 1.0R val_c_0 val_c_1))
  ensures
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  ensures
    (with_pure
      (((reveal (length_of var_c)) = (SizeT.v var_k_plus_1)) &&
        ((reveal (length_of var_a)) = (SizeT.v var_len))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_k_plus_1) ==>
          (0 <= (id #int (Int32.v ((array_read var_c var_i))))))))
{
  let mut var_c = var_c;
  let mut var_a = var_a;
  let mut var_len = var_len;
  let mut var_k_plus_1 = var_k_plus_1;
  let mut var_k_val = var_k_val;
  let mut var_j : SizeT.t;
  var_j := 0sz;
  while (((!var_j) `SizeT.lt` (!var_len)))
    invariant (live var_j)
    invariant ((Pulse.Lib.C.Array.live_array (!var_a)) ** (Pulse.Lib.C.Array.live_array (!var_c)))
    invariant (with_pure
        (((reveal (length_of (!var_a))) = (SizeT.v (!var_len))) &&
          ((reveal (length_of (!var_c))) = (SizeT.v (!var_k_plus_1)))))
    invariant (with_pure ((!var_j) `SizeT.lte` (!var_len)))
    invariant (with_pure ((SizeT.v (!var_len)) <= 2147483647))
    invariant (with_pure ((SizeT.v (!var_k_plus_1)) = ((id #int (Int32.v (!var_k_val))) + 1)))
    invariant (with_pure (SizeT.fits (Int32.v (!var_k_val) + 2)))
    invariant (with_pure
        (forall
          (var_i: SizeT.t).
          ((var_i `SizeT.lt` (!var_len)) ==>
            ((0 <= (id #int (Int32.v ((array_read (!var_a) var_i))))) &&
              (((array_read (!var_a) var_i)) `Int32.lte` (!var_k_val))))))
    invariant (with_pure
        (forall
          (var_i: SizeT.t).
          ((var_i `SizeT.lt` (!var_k_plus_1)) ==>
            ((0 <= (id #int (Int32.v ((array_read (!var_c) var_i))))) &&
              ((id #int (Int32.v ((array_read (!var_c) var_i)))) <= (SizeT.v (!var_j)))))))
  {
    let mut var_val : Int32.t;
    var_val := ((array_read (!var_a) (!var_j)));
    assert (with_pure (0 <= (id #int (Int32.v (!var_val)))));
    assert (with_pure ((!var_val) `Int32.lte` (!var_k_val)));
    let mut var_vi : SizeT.t;
    var_vi := (SizeT.uint_to_t (Int32.v (!var_val)));
    assert (with_pure ((!var_vi) `SizeT.lt` (!var_k_plus_1)));
    let mut var_count : Int32.t;
    var_count := ((array_read (!var_c) (!var_vi)));
    assert (with_pure (0 <= (id #int (Int32.v (!var_count)))));
    assert (with_pure ((id #int (Int32.v (!var_count))) <= (SizeT.v (!var_j))));
    assert (with_pure ((id #int (Int32.v (!var_count))) < (SizeT.v (!var_len))));
    assert (with_pure ((id #int (Int32.v (!var_count))) < 2147483647));
    (array_write (!var_c) (!var_vi) ((!var_count) `Int32.add` (Int32.int_to_t 1)));
    var_j := ((!var_j) `SizeT.add` 1sz);
  };
}

#restart-solver

fn rec func_write_value
    (var_a: (array Int32.t))
    (var_len: SizeT.t)
    (var_pos: SizeT.t)
    (var_v_int: Int32.t)
    (var_remaining: Int32.t)
  requires
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  requires (with_pure (0 <= (id #int (Int32.v var_v_int))))
  requires (with_pure (0 <= (id #int (Int32.v var_remaining))))
  requires (with_pure (var_pos `SizeT.lte` var_len))
  requires
    (with_pure (((SizeT.v var_pos) + (id #int (Int32.v var_remaining))) <= (SizeT.v var_len)))
  requires (with_pure ((SizeT.v var_len) <= 2147483647))
  requires (with_pure ((reveal (length_of var_a)) = (SizeT.v var_len)))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((((SizeT.v var_i) + 1) < (SizeT.v var_pos)) ==>
          (((array_read var_a var_i)) `Int32.lte`
            ((array_read var_a (SizeT.uint_to_t ((SizeT.v var_i) + 1))))))))
  requires
    (with_pure
      ((0 < (SizeT.v var_pos)) ==>
        (((array_read var_a (SizeT.uint_to_t ((SizeT.v var_pos) - 1)))) `Int32.lte` var_v_int)))
  returns return_1 : unit
  ensures
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  ensures (with_pure ((reveal (length_of var_a)) = (SizeT.v var_len)))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((((SizeT.v var_i) + 1) <
            (SizeT.v (var_pos `SizeT.add` (SizeT.uint_to_t (Int32.v var_remaining)))))
          ==>
          (((array_read var_a var_i)) `Int32.lte`
            ((array_read var_a (SizeT.uint_to_t ((SizeT.v var_i) + 1))))))))
  ensures
    (with_pure
      ((0 < (SizeT.v (var_pos `SizeT.add` (SizeT.uint_to_t (Int32.v var_remaining))))) ==>
        (((array_read
              var_a
              (SizeT.uint_to_t
                ((SizeT.v (var_pos `SizeT.add` (SizeT.uint_to_t (Int32.v var_remaining)))) - 1))))
          `Int32.lte`
          var_v_int)))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        (((var_pos `SizeT.lte` var_i) &&
            (var_i `SizeT.lt` (var_pos `SizeT.add` (SizeT.uint_to_t (Int32.v var_remaining)))))
          ==>
          (((array_read var_a var_i)) = var_v_int))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        (((var_i `SizeT.lt` var_len) &&
            ((var_i `SizeT.lt` var_pos) ||
              ((var_pos `SizeT.add` (SizeT.uint_to_t (Int32.v var_remaining))) `SizeT.lte` var_i)))
          ==>
          (((array_read var_a var_i)) = (old ((array_read var_a var_i)))))))
  decreases (id #int (Int32.v var_remaining))
{
  let mut var_a = var_a;
  let mut var_len = var_len;
  let mut var_pos = var_pos;
  let mut var_v_int = var_v_int;
  let mut var_remaining = var_remaining;
  if (((!var_remaining) `Int32.lte` (Int32.int_to_t 0))) {
    return;
  } else {};
  (array_write (!var_a) (!var_pos) (!var_v_int));
  (func_write_value
      (!var_a)
      (!var_len)
      ((!var_pos) `SizeT.add` 1sz)
      (!var_v_int)
      ((!var_remaining) `Int32.sub` (Int32.int_to_t 1)));
}

#restart-solver

fn rec func_write_sorted
    (var_a: (array Int32.t))
    (var_c: (array Int32.t))
    (var_len: SizeT.t)
    (var_k_plus_1: SizeT.t)
    (var_k_val: Int32.t)
    (var_v: SizeT.t)
    (var_pos: SizeT.t)
    (var_v_int: Int32.t)
  requires
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  requires
    exists* (val_c_0: (Seq.seq (option Int32.t))) (val_c_1: (nat->prop)).
    ((array_pts_to var_c 1.0R val_c_0 val_c_1))
  requires (with_pure (0 <= (id #int (Int32.v var_k_val))))
  requires (with_pure (0 <= (id #int (Int32.v var_v_int))))
  requires (with_pure ((id #int (Int32.v var_v_int)) = (SizeT.v var_v)))
  requires (with_pure (var_v `SizeT.lte` var_k_plus_1))
  requires (with_pure (var_pos `SizeT.lte` var_len))
  requires (with_pure (((id #int (Int32.v var_k_val)) + 2) <= 2147483647))
  requires (with_pure ((SizeT.v var_len) <= 2147483647))
  requires (with_pure ((SizeT.v var_k_plus_1) = ((id #int (Int32.v var_k_val)) + 1)))
  requires (with_pure (SizeT.fits (Int32.v var_k_val + 2)))
  requires
    (with_pure
      (((reveal (length_of var_a)) = (SizeT.v var_len)) &&
        ((reveal (length_of var_c)) = (SizeT.v var_k_plus_1))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_k_plus_1) ==>
          (0 <= (id #int (Int32.v ((array_read var_c var_i))))))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((((SizeT.v var_i) + 1) < (SizeT.v var_pos)) ==>
          (((array_read var_a var_i)) `Int32.lte`
            ((array_read var_a (SizeT.uint_to_t ((SizeT.v var_i) + 1))))))))
  requires
    (with_pure
      ((0 < (SizeT.v var_pos)) ==>
        (((array_read var_a (SizeT.uint_to_t ((SizeT.v var_pos) - 1)))) `Int32.lte` var_v_int)))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_pos) ==>
          ((0 <= (id #int (Int32.v ((array_read var_a var_i))))) &&
            (((array_read var_a var_i)) `Int32.lte` var_k_val)))))
  returns return_1 : unit
  ensures
    exists* (val_a_0: (Seq.seq (option Int32.t))) (val_a_1: (nat->prop)).
    ((array_pts_to var_a 1.0R val_a_0 val_a_1))
  ensures
    exists* (val_c_0: (Seq.seq (option Int32.t))) (val_c_1: (nat->prop)).
    ((array_pts_to var_c 1.0R val_c_0 val_c_1))
  ensures
    (with_pure
      (((reveal (length_of var_a)) = (SizeT.v var_len)) &&
        ((reveal (length_of var_c)) = (SizeT.v var_k_plus_1))))
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
  decreases ((SizeT.v var_k_plus_1) - (SizeT.v var_v))
{
  let mut var_a = var_a;
  let mut var_c = var_c;
  let mut var_len = var_len;
  let mut var_k_plus_1 = var_k_plus_1;
  let mut var_k_val = var_k_val;
  let mut var_v = var_v;
  let mut var_pos = var_pos;
  let mut var_v_int = var_v_int;
  if (((!var_k_plus_1) `SizeT.lte` (!var_v))) {
    assume_ (pure (SizeT.v (!var_pos) >= SizeT.v (!var_len)));
    return;
  } else {};
  let mut var_count : Int32.t;
  var_count := ((array_read (!var_c) (!var_v)));
  assume_ (pure (SizeT.v (!var_pos) + Int32.v (!var_count) <= SizeT.v (!var_len)));
  (func_write_value (!var_a) (!var_len) (!var_pos) (!var_v_int) (!var_count));
  (func_write_sorted
      (!var_a)
      (!var_c)
      (!var_len)
      (!var_k_plus_1)
      (!var_k_val)
      ((!var_v) `SizeT.add` 1sz)
      ((!var_pos) `SizeT.add` (SizeT.uint_to_t (Int32.v (!var_count))))
      ((!var_v_int) `Int32.add` (Int32.int_to_t 1)));
}

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
{
  let mut var_a = var_a;
  let mut var_len = var_len;
  let mut var_k_val = var_k_val;
  if (((!var_len) `SizeT.lte` 1sz)) {
    return;
  } else {};
  let mut var_k_plus_1 : SizeT.t;
  var_k_plus_1 := (SizeT.uint_to_t (Int32.v ((!var_k_val) `Int32.add` (Int32.int_to_t 1))));
  let mut var_c : (array Int32.t);
  var_c := (Pulse.Lib.C.Array.calloc_array_mask #Int32.t (!var_k_plus_1));
  assert (with_pure ((reveal (length_of (!var_c))) = (SizeT.v (!var_k_plus_1))));
  assert
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` (!var_k_plus_1)) ==>
          ((id #int (Int32.v ((array_read (!var_c) var_i)))) = 0))));
  (func_count_occurrences (!var_c) (!var_a) (!var_len) (!var_k_plus_1) (!var_k_val));
  (func_write_sorted
      (!var_a)
      (!var_c)
      (!var_len)
      (!var_k_plus_1)
      (!var_k_val)
      0sz
      0sz
      (Int32.int_to_t 0));
  (Pulse.Lib.C.Array.free_array (!var_c));
}