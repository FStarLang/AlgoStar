module MatrixChain
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver

open Pulse.Lib.C.Array

#restart-solver

open CLRS.Ch15.MatrixChain.Spec

#restart-solver

open CLRS.Ch15.MatrixChain.C.BridgeLemmas

#restart-solver

fn func_compute_index (var_a: SizeT.t) (var_b: SizeT.t) (var_n: SizeT.t)
  requires (with_pure (var_a `SizeT.lt` var_n))
  requires (with_pure (var_b `SizeT.lt` var_n))
  requires (with_pure (1 <= (SizeT.v var_n)))
  requires (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  returns return_1 : SizeT.t
  ensures (with_pure (return_1 `SizeT.lt` (var_n `SizeT.mul` var_n)))
  ensures (with_pure (return_1 = ((var_a `SizeT.mul` var_n) `SizeT.add` var_b)))
{
  let mut var_a = var_a;
  let mut var_b = var_b;
  let mut var_n = var_n;
  return (((!var_a) `SizeT.mul` (!var_n)) `SizeT.add` (!var_b));
}

#restart-solver

fn func_init_table (var_m: (array Int32.t)) (var_n: SizeT.t)
  requires
    exists* (val_m_0: (Seq.seq (option Int32.t))) (val_m_1: (nat->prop)).
    ((array_pts_to var_m 1.0R val_m_0 val_m_1))
  requires (with_pure ((1 <= (SizeT.v var_n)) && ((SizeT.v var_n) <= 1000)))
  requires (with_pure (reveal (length_of var_m) = SizeT.v var_n * SizeT.v var_n))
  requires (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  returns return_1 : unit
  ensures
    exists* (val_m_0: (Seq.seq (option Int32.t))) (val_m_1: (nat->prop)).
    ((array_pts_to var_m 1.0R val_m_0 val_m_1))
  ensures (with_pure (reveal (length_of var_m) = SizeT.v var_n * SizeT.v var_n))
  ensures (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  ensures
    (with_pure
      (forall
        (var_w: SizeT.t).
        ((SizeT.v var_w >= SizeT.v var_n * SizeT.v var_n) ||
          ((0 <= (id #int (Int32.v ((array_read var_m var_w))))) &&
            ((id #int (Int32.v ((array_read var_m var_w)))) <= 1000000000)))))
  ensures
    (with_pure (forall (i: nat). i < SizeT.v var_n * SizeT.v var_n ==>
Seq.index (to_int_seq (array_value_of var_m)) i == 0))
{
  let mut var_m = var_m;
  let mut var_n = var_n;
  let mut var_idx : SizeT.t;
  var_idx := 0sz;
  while (((!var_idx) `SizeT.lt` ((!var_n) `SizeT.mul` (!var_n))))
    invariant (live var_idx)
    invariant (Pulse.Lib.C.Array.live_array (!var_m))
    invariant (with_pure ((1 <= (SizeT.v (!var_n))) && ((SizeT.v (!var_n)) <= 1000)))
    invariant (with_pure (reveal (length_of (!var_m)) = SizeT.v (!var_n) * SizeT.v (!var_n)))
    invariant (with_pure (SizeT.fits (SizeT.v (!var_n) * SizeT.v (!var_n))))
    invariant (with_pure (SizeT.v (!var_idx) <= SizeT.v (!var_n) * SizeT.v (!var_n)))
    invariant (with_pure
        (forall
          (var_w: SizeT.t).
          ((SizeT.v var_w >= SizeT.v (!var_idx)) ||
            ((0 <= (id #int (Int32.v ((array_read (!var_m) var_w))))) &&
              ((id #int (Int32.v ((array_read (!var_m) var_w)))) <= 1000000000)))))
    invariant (with_pure (forall (i: nat). i < SizeT.v (!var_idx) ==>
Seq.index (to_int_seq (array_value_of (!var_m))) i == 0))
  {
    (array_write (!var_m) (!var_idx) (Int32.int_to_t 0));
    var_idx := ((!var_idx) `SizeT.add` 1sz);
  };
}

#restart-solver

#push-options "--fuel 0 --ifuel 0"
fn func_matrix_chain (var_dims: (array Int32.t)) (var_n: SizeT.t) (var_m: (array Int32.t))
  requires
    exists* (val_dims_0: (Seq.seq (option Int32.t))) (val_dims_1: (nat->prop)).
    ((array_pts_to var_dims 1.0R val_dims_0 val_dims_1))
  requires
    exists* (val_m_0: (Seq.seq (option Int32.t))) (val_m_1: (nat->prop)).
    ((array_pts_to var_m 1.0R val_m_0 val_m_1))
  requires (with_pure ((reveal (length_of var_dims)) = ((SizeT.v var_n) + 1)))
  requires (with_pure ((1 <= (SizeT.v var_n)) && ((SizeT.v var_n) <= 1000)))
  requires (with_pure (reveal (length_of var_m) = SizeT.v var_n * SizeT.v var_n))
  requires (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
  requires
    (with_pure
      (forall
        (var_w: SizeT.t).
        ((var_n `SizeT.lt` var_w) ||
          ((0 <= (id #int (Int32.v ((array_read var_dims var_w))))) &&
            ((id #int (Int32.v ((array_read var_dims var_w)))) <= 200)))))
  returns return_1 : Int32.t
  ensures
    exists* (val_dims_0: (Seq.seq (option Int32.t))) (val_dims_1: (nat->prop)).
    ((array_pts_to var_dims 1.0R val_dims_0 val_dims_1))
  ensures
    exists* (val_m_0: (Seq.seq (option Int32.t))) (val_m_1: (nat->prop)).
    ((array_pts_to var_m 1.0R val_m_0 val_m_1))
  ensures (with_pure ((reveal (length_of var_dims)) = ((SizeT.v var_n) + 1)))
  ensures (with_pure (reveal (length_of var_m) = SizeT.v var_n * SizeT.v var_n))
  ensures (with_pure (0 <= (id #int (Int32.v return_1))))
  ensures
    (with_pure
      (forall
        (var_w: SizeT.t).
        ((SizeT.v var_w >= SizeT.v var_n * SizeT.v var_n) ||
          (0 <= (id #int (Int32.v ((array_read var_m var_w))))))))
  ensures
    (with_pure (
id #int (Int32.v return_1) =
mc_result
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n)))
{
  (func_init_table var_m var_n);
  to_int_seq_create_zero
(array_value_of var_m)
(SizeT.v var_n * SizeT.v var_n);
  let mut var_l : SizeT.t;
  var_l := 2sz;
  while (((!var_l) `SizeT.lte` var_n))
    invariant (live var_l)
    invariant ((Pulse.Lib.C.Array.live_array var_m) **
        (Pulse.Lib.C.Array.live_array var_dims))
    invariant (with_pure
        ((2 <= (SizeT.v (!var_l))) && ((SizeT.v (!var_l)) <= ((SizeT.v var_n) + 1))))
    invariant (with_pure ((1 <= (SizeT.v var_n)) && ((SizeT.v var_n) <= 1000)))
    invariant (with_pure ((reveal (length_of var_dims)) = ((SizeT.v var_n) + 1)))
    invariant (with_pure (reveal (length_of var_m) = SizeT.v var_n * SizeT.v var_n))
    invariant (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
    invariant (with_pure
        (forall
          (var_w: SizeT.t).
          ((var_n `SizeT.lt` var_w) ||
            ((0 <= (id #int (Int32.v ((array_read var_dims var_w))))) &&
              ((id #int (Int32.v ((array_read var_dims var_w)))) <= 200)))))
    invariant (with_pure
        (forall
          (var_w: SizeT.t).
          ((SizeT.v var_w >= SizeT.v var_n * SizeT.v var_n) ||
            ((0 <= (id #int (Int32.v ((array_read var_m var_w))))) &&
              ((id #int (Int32.v ((array_read var_m var_w)))) <= 1000000000)))))
    invariant (with_pure (
mc_outer
(to_int_seq (array_value_of var_m))
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) (SizeT.v (!var_l))
==
mc_outer
(Seq.create (SizeT.v var_n * SizeT.v var_n) 0)
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) 2))
  {
    mc_outer_unfold
(to_int_seq (array_value_of var_m))
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) (SizeT.v (!var_l));
    let mut var_i : SizeT.t;
    var_i := 0sz;
    while ((((!var_i) `SizeT.add` (!var_l)) `SizeT.lte` var_n))
      invariant ((live var_i) ** (live var_l))
      invariant ((Pulse.Lib.C.Array.live_array var_m) **
          (Pulse.Lib.C.Array.live_array var_dims))
      invariant (with_pure ((2 <= (SizeT.v (!var_l))) && ((!var_l) `SizeT.lte` var_n)))
      invariant (with_pure ((1 <= (SizeT.v var_n)) && ((SizeT.v var_n) <= 1000)))
      invariant (with_pure ((reveal (length_of var_dims)) = ((SizeT.v var_n) + 1)))
      invariant (with_pure (reveal (length_of var_m) = SizeT.v var_n * SizeT.v var_n))
      invariant (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
      invariant (with_pure
          (forall
            (var_w: SizeT.t).
            ((var_n `SizeT.lt` var_w) ||
              ((0 <= (id #int (Int32.v ((array_read var_dims var_w))))) &&
                ((id #int (Int32.v ((array_read var_dims var_w)))) <= 200)))))
      invariant (with_pure
          (forall
            (var_w: SizeT.t).
            ((SizeT.v var_w >= SizeT.v var_n * SizeT.v var_n) ||
              ((0 <= (id #int (Int32.v ((array_read var_m var_w))))) &&
                ((id #int (Int32.v ((array_read var_m var_w)))) <= 1000000000)))))
      invariant (with_pure (SizeT.v (!var_i) + SizeT.v (!var_l) <= SizeT.v var_n + 1))
      invariant (with_pure (
mc_outer
(mc_inner_i
(to_int_seq (array_value_of var_m))
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) (SizeT.v (!var_l)) (SizeT.v (!var_i)))
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) (SizeT.v (!var_l) + 1)
==
mc_outer
(Seq.create (SizeT.v var_n * SizeT.v var_n) 0)
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) 2))
    {
      let var_vi = (!var_i);
      let var_vl = (!var_l);
      let var_j_val = ((var_vi `SizeT.add` var_vl) `SizeT.sub` 1sz);
      let mut var_min_cost : Int32.t;
      var_min_cost := (Int32.int_to_t 1000000000);
      let mut var_k : SizeT.t;
      var_k := var_vi;
      while (((!var_k) `SizeT.lt` var_j_val))
        invariant ((((live var_k) **
                (live var_min_cost))
              **
              (live var_i))
            **
            (live var_l))
        invariant ((Pulse.Lib.C.Array.live_array var_m) **
            (Pulse.Lib.C.Array.live_array var_dims))
        invariant (with_pure (SizeT.v var_vl >= 2 && SizeT.v var_vl <= SizeT.v var_n))
        invariant (with_pure ((1 <= (SizeT.v var_n)) && ((SizeT.v var_n) <= 1000)))
        invariant (with_pure ((reveal (length_of var_dims)) = ((SizeT.v var_n) + 1)))
        invariant (with_pure (reveal (length_of var_m) = SizeT.v var_n * SizeT.v var_n))
        invariant (with_pure (SizeT.fits (SizeT.v var_n * SizeT.v var_n)))
        invariant (with_pure
            (forall
              (var_w: SizeT.t).
              ((var_n `SizeT.lt` var_w) ||
                ((0 <= (id #int (Int32.v ((array_read var_dims var_w))))) &&
                  ((id #int (Int32.v ((array_read var_dims var_w)))) <= 200)))))
        invariant (with_pure
            (forall
              (var_w: SizeT.t).
              ((SizeT.v var_w >= SizeT.v var_n * SizeT.v var_n) ||
                ((0 <= (id #int (Int32.v ((array_read var_m var_w))))) &&
                  ((id #int (Int32.v ((array_read var_m var_w)))) <= 1000000000)))))
        invariant (with_pure (SizeT.v var_vi + SizeT.v var_vl <= SizeT.v var_n))
        invariant (with_pure (SizeT.v var_j_val = SizeT.v var_vi + SizeT.v var_vl - 1))
        invariant (with_pure
            (SizeT.v (!var_k) >= SizeT.v var_vi &&
SizeT.v (!var_k) <= SizeT.v var_j_val))
        invariant (with_pure
            ((0 <= (id #int (Int32.v (!var_min_cost)))) &&
              ((id #int (Int32.v (!var_min_cost))) <= 1000000000)))
        invariant (with_pure
            (SizeT.v (!var_i) = SizeT.v var_vi && SizeT.v (!var_l) = SizeT.v var_vl))
        invariant (with_pure (
mc_inner_k
(to_int_seq (array_value_of var_m))
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) (SizeT.v var_vi)
(SizeT.v var_j_val)
(SizeT.v (!var_k)) (Int32.v (!var_min_cost))
==
mc_inner_k
(to_int_seq (array_value_of var_m))
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) (SizeT.v var_vi)
(SizeT.v var_j_val)
(SizeT.v var_vi) 1000000000))
        invariant (with_pure (
mc_outer
(mc_inner_i
(to_int_seq (array_value_of var_m))
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) (SizeT.v var_vl) (SizeT.v var_vi))
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) (SizeT.v var_vl + 1)
==
mc_outer
(Seq.create (SizeT.v var_n * SizeT.v var_n) 0)
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) 2))
      {
        let var_ci = (func_compute_index var_vi (!var_k) var_n);
        let var_ci2 = (func_compute_index ((!var_k) `SizeT.add` 1sz) var_j_val var_n);
        let var_cost_ik = ((array_read var_m var_ci));
        let var_cost_kj = ((array_read var_m var_ci2));
        let var_dim_i = ((array_read var_dims var_vi));
        let var_dim_k1 = ((array_read var_dims ((!var_k) `SizeT.add` 1sz)));
        let var_dim_j1 = ((array_read var_dims (var_j_val `SizeT.add` 1sz)));
        let var_mult_cost = ((var_dim_i `Int32.mul` var_dim_k1) `Int32.mul` var_dim_j1);
        let var_q = ((var_cost_ik `Int32.add` var_cost_kj) `Int32.add` var_mult_cost);
        mc_inner_k_step
(to_int_seq (array_value_of var_m))
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) (SizeT.v var_vi) (SizeT.v var_j_val)
(SizeT.v (!var_k)) (Int32.v (!var_min_cost));
        if ((var_q `Int32.lt` (!var_min_cost))) {
          var_min_cost := var_q;
        } else {};
        var_k := ((!var_k) `SizeT.add` 1sz);
      };
      mc_inner_k_base
(to_int_seq (array_value_of var_m))
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) (SizeT.v var_vi) (SizeT.v var_j_val)
(SizeT.v (!var_k)) (Int32.v (!var_min_cost));
      assert
        (with_pure (
id #int (Int32.v (!var_min_cost)) ==
mc_inner_k
(to_int_seq (array_value_of var_m))
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) (SizeT.v var_vi)
(SizeT.v var_j_val)
(SizeT.v var_vi) 1000000000));
      let var_ci_ij = (func_compute_index var_vi var_j_val var_n);
      mc_i_step_full
(array_value_of var_m)
(array_value_of var_dims)
(SizeT.v var_n) (SizeT.v var_vl) (SizeT.v var_vi)
(!var_min_cost)
(SizeT.v var_ci_ij);
      (array_write var_m var_ci_ij (!var_min_cost));
      var_i := ((!var_i) `SizeT.add` 1sz);
    };
    mc_inner_i_base
(to_int_seq (array_value_of var_m))
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n) (SizeT.v (!var_l)) (SizeT.v (!var_i));
    var_l := ((!var_l) `SizeT.add` 1sz);
  };
  mc_outer_identity
(to_int_seq (array_value_of var_m))
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n)
(SizeT.v (!var_l));
  mc_result_from_table
(to_int_seq (array_value_of var_dims))
(SizeT.v var_n)
(to_int_seq (array_value_of var_m));
  assert (with_pure (0 < SizeT.v var_n));
  return ((array_read var_m (var_n `SizeT.sub` 1sz)));
}