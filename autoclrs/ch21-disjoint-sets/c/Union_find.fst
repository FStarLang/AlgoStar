module Union_find
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

open CLRS.Ch21.UnionFind.Spec

#restart-solver

open CLRS.Ch21.UnionFind.C.BridgeLemmas

#restart-solver

fn func_make_set (var_parent: (array SizeT.t)) (var_rank: (array SizeT.t)) (var_n: SizeT.t)
  requires
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  requires
    exists* (val_rank_0: (Seq.seq (option SizeT.t))) (val_rank_1: (nat->prop)).
    ((array_pts_to var_rank 1.0R val_rank_0 val_rank_1))
  requires
    (with_pure
      ((((SizeT.v var_n) <= (reveal (length_of var_parent))) &&
          ((SizeT.v var_n) <= (reveal (length_of var_rank))))
        &&
        (0 < (SizeT.v var_n))))
  returns return_1 : unit
  ensures
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  ensures
    exists* (val_rank_0: (Seq.seq (option SizeT.t))) (val_rank_1: (nat->prop)).
    ((array_pts_to var_rank 1.0R val_rank_0 val_rank_1))
  ensures
    (with_pure
      (((SizeT.v var_n) <= (reveal (length_of var_parent))) &&
        ((SizeT.v var_n) <= (reveal (length_of var_rank)))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) = var_i))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> ((SizeT.v ((array_read var_rank var_i))) = 0))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_rank var_i)) `SizeT.lt` var_n))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        (((var_i `SizeT.lt` var_n) && (not (((array_read var_parent var_i)) = var_i))) ==>
          (((array_read var_rank var_i)) `SizeT.lt`
            ((array_read var_rank ((array_read var_parent var_i))))))))
{
  let mut var_parent = var_parent;
  let mut var_rank = var_rank;
  let mut var_n = var_n;
  let mut var_i : SizeT.t;
  var_i := 0sz;
  while (((!var_i) `SizeT.lt` (!var_n)))
    invariant (live var_i)
    invariant ((Pulse.Lib.C.Array.live_array (!var_parent)) **
        (Pulse.Lib.C.Array.live_array (!var_rank)))
    invariant (with_pure
        (((SizeT.v (!var_n)) <= (reveal (length_of (!var_parent)))) &&
          ((SizeT.v (!var_n)) <= (reveal (length_of (!var_rank))))))
    invariant (with_pure ((!var_i) `SizeT.lte` (!var_n)))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_i)) ==> (((array_read (!var_parent) var_j)) = var_j))))
    invariant (with_pure
        (forall
          (var_j: SizeT.t).
          ((var_j `SizeT.lt` (!var_i)) ==> ((SizeT.v ((array_read (!var_rank) var_j))) = 0))))
  {
    (array_write (!var_parent) (!var_i) (!var_i));
    (array_write (!var_rank) (!var_i) 0sz);
    var_i := ((!var_i) `SizeT.add` 1sz);
  };
}

#restart-solver

fn rec func_find_root
    (var_parent: (array SizeT.t))
    (var_rank: (array SizeT.t))
    (var_x: SizeT.t)
    (var_n: SizeT.t)
  requires
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  requires
    exists* (val_rank_0: (Seq.seq (option SizeT.t))) (val_rank_1: (nat->prop)).
    ((array_pts_to var_rank 1.0R val_rank_0 val_rank_1))
  requires
    (with_pure
      (((((SizeT.v var_n) <= (reveal (length_of var_parent))) &&
            ((SizeT.v var_n) <= (reveal (length_of var_rank))))
          &&
          (0 < (SizeT.v var_n)))
        &&
        (var_x `SizeT.lt` var_n)))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_rank var_i)) `SizeT.lt` var_n))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        (((var_i `SizeT.lt` var_n) && (not (((array_read var_parent var_i)) = var_i))) ==>
          (((array_read var_rank var_i)) `SizeT.lt`
            ((array_read var_rank ((array_read var_parent var_i))))))))
  requires
    (with_pure (
uf_inv (c_to_uf (array_value_of var_parent) (array_value_of var_rank) (SizeT.v var_n))))
  returns return_1 : SizeT.t
  ensures
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  ensures
    exists* (val_rank_0: (Seq.seq (option SizeT.t))) (val_rank_1: (nat->prop)).
    ((array_pts_to var_rank 1.0R val_rank_0 val_rank_1))
  ensures (with_pure ((reveal (length_of var_parent)) = (old (reveal (length_of var_parent)))))
  ensures (with_pure ((reveal (length_of var_rank)) = (old (reveal (length_of var_rank)))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==>
          (((array_read var_parent var_i)) = (old ((array_read var_parent var_i)))))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==>
          (((array_read var_rank var_i)) = (old ((array_read var_rank var_i)))))))
  ensures
    (with_pure ((return_1 `SizeT.lt` var_n) && (((array_read var_parent return_1)) = return_1)))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        (((var_i `SizeT.lt` var_n) && (not (((array_read var_parent var_i)) = var_i))) ==>
          (((array_read var_rank var_i)) `SizeT.lt`
            ((array_read var_rank ((array_read var_parent var_i))))))))
  ensures
    (with_pure (
uf_inv (c_to_uf (array_value_of var_parent) (array_value_of var_rank) (SizeT.v var_n))))
  ensures
    (with_pure (
SizeT.v return_1 ==
pure_find (c_to_uf (array_value_of var_parent) (array_value_of var_rank) (SizeT.v var_n))
(SizeT.v var_x)))
  decreases ((SizeT.v var_n) - (SizeT.v ((array_read var_rank var_x))))
{
  let mut var_parent = var_parent;
  let mut var_rank = var_rank;
  let mut var_x = var_x;
  let mut var_n = var_n;
  if ((((array_read (!var_parent) (!var_x))) = (!var_x))) {
    return (!var_x);
  } else {};
  return (func_find_root (!var_parent) (!var_rank) ((array_read (!var_parent) (!var_x))) (!var_n));
}

#restart-solver

fn rec func_find_set
    (var_parent: (array SizeT.t))
    (var_rank: (array SizeT.t))
    (var_x: SizeT.t)
    (var_n: SizeT.t)
  requires
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  requires
    exists* (val_rank_0: (Seq.seq (option SizeT.t))) (val_rank_1: (nat->prop)).
    ((array_pts_to var_rank 1.0R val_rank_0 val_rank_1))
  requires
    (with_pure
      (((((SizeT.v var_n) <= (reveal (length_of var_parent))) &&
            ((SizeT.v var_n) <= (reveal (length_of var_rank))))
          &&
          (var_x `SizeT.lt` var_n))
        &&
        (0 < (SizeT.v var_n))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_rank var_i)) `SizeT.lt` var_n))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        (((var_i `SizeT.lt` var_n) && (not (((array_read var_parent var_i)) = var_i))) ==>
          (((array_read var_rank var_i)) `SizeT.lt`
            ((array_read var_rank ((array_read var_parent var_i))))))))
  requires
    (with_pure (
uf_inv (c_to_uf (array_value_of var_parent) (array_value_of var_rank) (SizeT.v var_n))))
  returns return_1 : SizeT.t
  ensures
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  ensures
    exists* (val_rank_0: (Seq.seq (option SizeT.t))) (val_rank_1: (nat->prop)).
    ((array_pts_to var_rank 1.0R val_rank_0 val_rank_1))
  ensures
    (with_pure
      (((SizeT.v var_n) <= (reveal (length_of var_parent))) &&
        ((SizeT.v var_n) <= (reveal (length_of var_rank)))))
  ensures (with_pure (return_1 `SizeT.lt` var_n))
  ensures (with_pure (((array_read var_parent return_1)) = return_1))
  ensures (with_pure (((array_read var_parent var_x)) = return_1))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==>
          (((array_read var_rank var_i)) = (old ((array_read var_rank var_i)))))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        (((var_i `SizeT.lt` var_n) && (not (((array_read var_parent var_i)) = var_i))) ==>
          (((array_read var_rank var_i)) `SizeT.lt`
            ((array_read var_rank ((array_read var_parent var_i))))))))
  ensures
    (with_pure (
uf_inv (c_to_uf (array_value_of var_parent) (array_value_of var_rank) (SizeT.v var_n))))
  ensures
    (with_pure (
SizeT.v return_1 ==
pure_find (c_to_uf (array_value_of var_parent) (array_value_of var_rank) (SizeT.v var_n))
(SizeT.v var_x)))
  decreases ((SizeT.v var_n) - (SizeT.v ((array_read var_rank var_x))))
{
  let mut var_parent = var_parent;
  let mut var_rank = var_rank;
  let mut var_x = var_x;
  let mut var_n = var_n;
  if ((((array_read (!var_parent) (!var_x))) = (!var_x))) {
    return (!var_x);
  } else {};
  let mut var_root : SizeT.t;
  var_root :=
    (func_find_set (!var_parent) (!var_rank) ((array_read (!var_parent) (!var_x))) (!var_n));
  (array_write (!var_parent) (!var_x) (!var_root));
  return (!var_root);
}

#restart-solver

fn func_link
    (var_parent: (array SizeT.t))
    (var_rank: (array SizeT.t))
    (var_root_x: SizeT.t)
    (var_root_y: SizeT.t)
    (var_n: SizeT.t)
  requires
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  requires
    exists* (val_rank_0: (Seq.seq (option SizeT.t))) (val_rank_1: (nat->prop)).
    ((array_pts_to var_rank 1.0R val_rank_0 val_rank_1))
  requires
    (with_pure
      ((((SizeT.v var_n) <= (reveal (length_of var_parent))) &&
          ((SizeT.v var_n) <= (reveal (length_of var_rank))))
        &&
        (0 < (SizeT.v var_n))))
  requires
    (with_pure
      (((var_root_x `SizeT.lt` var_n) && (var_root_y `SizeT.lt` var_n)) &&
        (not (var_root_x = var_root_y))))
  requires
    (with_pure
      ((((array_read var_parent var_root_x)) = var_root_x) &&
        (((array_read var_parent var_root_y)) = var_root_y)))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_rank var_i)) `SizeT.lt` var_n))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        (((var_i `SizeT.lt` var_n) && (not (((array_read var_parent var_i)) = var_i))) ==>
          (((array_read var_rank var_i)) `SizeT.lt`
            ((array_read var_rank ((array_read var_parent var_i))))))))
  requires
    (with_pure (
uf_inv (c_to_uf (array_value_of var_parent) (array_value_of var_rank) (SizeT.v var_n))))
  returns return_1 : unit
  ensures
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  ensures
    exists* (val_rank_0: (Seq.seq (option SizeT.t))) (val_rank_1: (nat->prop)).
    ((array_pts_to var_rank 1.0R val_rank_0 val_rank_1))
  ensures
    (with_pure
      (((SizeT.v var_n) <= (reveal (length_of var_parent))) &&
        ((SizeT.v var_n) <= (reveal (length_of var_rank)))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==>
          ((old ((array_read var_rank var_i))) `SizeT.lte` ((array_read var_rank var_i))))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        (((var_i `SizeT.lt` var_n) && (not (((array_read var_parent var_i)) = var_i))) ==>
          (((array_read var_rank var_i)) `SizeT.lt`
            ((array_read var_rank ((array_read var_parent var_i))))))))
  ensures
    (with_pure (
uf_inv (c_to_uf (array_value_of var_parent) (array_value_of var_rank) (SizeT.v var_n))))
  ensures
    (with_pure (
pure_find (c_to_uf (array_value_of var_parent) (array_value_of var_rank) (SizeT.v var_n))
(SizeT.v var_root_x) ==
pure_find (c_to_uf (array_value_of var_parent) (array_value_of var_rank) (SizeT.v var_n))
(SizeT.v var_root_y)))
{
  let mut var_parent = var_parent;
  let mut var_rank = var_rank;
  let mut var_root_x = var_root_x;
  let mut var_root_y = var_root_y;
  let mut var_n = var_n;
  if ((((array_read (!var_rank) (!var_root_x))) `SizeT.lt`
        ((array_read (!var_rank) (!var_root_y))))) {
    (array_write (!var_parent) (!var_root_x) (!var_root_y));
  } else {
    if ((((array_read (!var_rank) (!var_root_y))) `SizeT.lt`
          ((array_read (!var_rank) (!var_root_x))))) {
      (array_write (!var_parent) (!var_root_y) (!var_root_x));
    } else {
      (array_write (!var_parent) (!var_root_y) (!var_root_x));
      (array_write
          (!var_rank)
          (!var_root_x)
          (((array_read (!var_rank) (!var_root_x))) `SizeT.add` 1sz));
    };
  };
}

#restart-solver

fn func_union_sets
    (var_parent: (array SizeT.t))
    (var_rank: (array SizeT.t))
    (var_x: SizeT.t)
    (var_y: SizeT.t)
    (var_n: SizeT.t)
  requires
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  requires
    exists* (val_rank_0: (Seq.seq (option SizeT.t))) (val_rank_1: (nat->prop)).
    ((array_pts_to var_rank 1.0R val_rank_0 val_rank_1))
  requires
    (with_pure
      ((((SizeT.v var_n) <= (reveal (length_of var_parent))) &&
          ((SizeT.v var_n) <= (reveal (length_of var_rank))))
        &&
        (0 < (SizeT.v var_n))))
  requires (with_pure ((var_x `SizeT.lt` var_n) && (var_y `SizeT.lt` var_n)))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_rank var_i)) `SizeT.lt` var_n))))
  requires
    (with_pure
      (forall
        (var_i: SizeT.t).
        (((var_i `SizeT.lt` var_n) && (not (((array_read var_parent var_i)) = var_i))) ==>
          (((array_read var_rank var_i)) `SizeT.lt`
            ((array_read var_rank ((array_read var_parent var_i))))))))
  requires
    (with_pure (
uf_inv (c_to_uf (array_value_of var_parent) (array_value_of var_rank) (SizeT.v var_n))))
  returns return_1 : unit
  ensures
    exists* (val_parent_0: (Seq.seq (option SizeT.t))) (val_parent_1: (nat->prop)).
    ((array_pts_to var_parent 1.0R val_parent_0 val_parent_1))
  ensures
    exists* (val_rank_0: (Seq.seq (option SizeT.t))) (val_rank_1: (nat->prop)).
    ((array_pts_to var_rank 1.0R val_rank_0 val_rank_1))
  ensures
    (with_pure
      (((SizeT.v var_n) <= (reveal (length_of var_parent))) &&
        ((SizeT.v var_n) <= (reveal (length_of var_rank)))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==> (((array_read var_parent var_i)) `SizeT.lt` var_n))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        (((var_i `SizeT.lt` var_n) && (not (((array_read var_parent var_i)) = var_i))) ==>
          (((array_read var_rank var_i)) `SizeT.lt`
            ((array_read var_rank ((array_read var_parent var_i))))))))
  ensures
    (with_pure
      (forall
        (var_i: SizeT.t).
        ((var_i `SizeT.lt` var_n) ==>
          ((old ((array_read var_rank var_i))) `SizeT.lte` ((array_read var_rank var_i))))))
  ensures
    (with_pure (
uf_inv (c_to_uf (array_value_of var_parent) (array_value_of var_rank) (SizeT.v var_n))))
{
  let mut var_parent = var_parent;
  let mut var_rank = var_rank;
  let mut var_x = var_x;
  let mut var_y = var_y;
  let mut var_n = var_n;
  let mut var_root_x : SizeT.t;
  var_root_x := (func_find_root (!var_parent) (!var_rank) (!var_x) (!var_n));
  let mut var_root_y : SizeT.t;
  var_root_y := (func_find_root (!var_parent) (!var_rank) (!var_y) (!var_n));
  if ((not ((!var_root_x) = (!var_root_y)))) {
    (func_link (!var_parent) (!var_rank) (!var_root_x) (!var_root_y) (!var_n));
  } else {};
}