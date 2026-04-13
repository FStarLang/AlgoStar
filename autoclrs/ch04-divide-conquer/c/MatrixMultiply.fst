module MatrixMultiply
open Pulse
open Pulse.Lib.C
#lang-pulse


#restart-solver


open CLRS.Ch04.MatrixMultiply.C.BridgeLemmas
open CLRS.Ch04.MatrixMultiply.Spec

// Helper: like live_array but pins the ghost sequence to a known value.
// This avoids re-existentializing the sequence in loop invariants,
// so array_read results connect to the captured sequence.
[@@pulse_eager_unfold]
let pinned_array (#t: Type) (a: Pulse.Lib.Array.array t) (s: Seq.seq (option t)) : slprop =
  exists* (mask: nat -> prop). Pulse.Lib.C.Array.array_pts_to a 1.0R s mask

#restart-solver
#push-options "--split_queries always"

fn func_dot_product
    (var_a: (array Int32.t))
    (var_b: (array Int32.t))
    (var_n: SizeT.t)
    (var_i: SizeT.t)
    (var_j: SizeT.t)
    (var_max_val: Int32.t)
    (#sa: Ghost.erased (Seq.seq (option Int32.t)))
    (#sb: Ghost.erased (Seq.seq (option Int32.t)))
  requires (pinned_array var_a sa)
  requires (pinned_array var_b sb)
  requires
    (with_pure
      ((((0 < (SizeT.v var_n)) && ((SizeT.v var_n) <= 46)) && (var_i `SizeT.lt` var_n)) &&
        (var_j `SizeT.lt` var_n)))
  requires
    (with_pure ((0 < (id #int (Int32.v var_max_val))) && ((id #int (Int32.v var_max_val)) <= 46)))
  requires (with_pure (SizeT.fits (SizeT.v var_n `op_Multiply` SizeT.v var_n)))
  requires
    (with_pure
      (((reveal (length_of var_a)) = (SizeT.v (var_n `SizeT.mul` var_n))) &&
        ((reveal (length_of var_b)) = (SizeT.v (var_n `SizeT.mul` var_n)))))
  requires
    (with_pure
      (forall
        (var_idx: SizeT.t).
        ((var_idx `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          (((Int32.sub Int32.zero var_max_val) `Int32.lte` ((array_read var_a var_idx))) &&
            (((array_read var_a var_idx)) `Int32.lte` var_max_val)))))
  requires
    (with_pure
      (forall
        (var_idx: SizeT.t).
        ((var_idx `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          (((Int32.sub Int32.zero var_max_val) `Int32.lte` ((array_read var_b var_idx))) &&
            (((array_read var_b var_idx)) `Int32.lte` var_max_val)))))
  returns return_1 : Int32.t
  ensures (pinned_array var_a sa)
  ensures (pinned_array var_b sb)
  ensures
    (pure
      ((id #int (Int32.v return_1)) =
        (dot_product_spec_c sa sb
          (SizeT.v var_n) (SizeT.v var_i) (SizeT.v var_j) (SizeT.v var_n))))
  ensures
    (with_pure
      (((reveal (length_of var_a)) = (SizeT.v (var_n `SizeT.mul` var_n))) &&
        ((reveal (length_of var_b)) = (SizeT.v (var_n `SizeT.mul` var_n)))))
  ensures
    (with_pure
      (forall
        (var_idx: SizeT.t).
        ((var_idx `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          (((Int32.sub Int32.zero var_max_val) `Int32.lte` ((array_read var_a var_idx))) &&
            (((array_read var_a var_idx)) `Int32.lte` var_max_val)))))
  ensures
    (with_pure
      (forall
        (var_idx: SizeT.t).
        ((var_idx `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          (((Int32.sub Int32.zero var_max_val) `Int32.lte` ((array_read var_b var_idx))) &&
            (((array_read var_b var_idx)) `Int32.lte` var_max_val)))))
{
  let mut var_a = var_a;
  let mut var_b = var_b;
  let mut var_n = var_n;
  let mut var_i = var_i;
  let mut var_j = var_j;
  let mut var_max_val = var_max_val;
  let _va = array_value_of (!var_a);
  let _vb = array_value_of (!var_b);
  let mut var_sum : Int32.t;
  var_sum := (Int32.int_to_t 0);
  let mut var_mv2 : Int32.t;
  var_mv2 := ((!var_max_val) `Int32.mul` (!var_max_val));
  let mut var_bound : Int32.t;
  var_bound := (Int32.int_to_t 0);
  let mut var_k : SizeT.t;
  var_k := 0sz;
  while (((!var_k) `SizeT.lt` (!var_n)))
    invariant ((((((live var_k) ** (live var_sum)) ** (live var_bound)) ** (live var_mv2)) **
          (pinned_array (!var_a) _va))
        **
        (pinned_array (!var_b) _vb))
    invariant (with_pure
        (((reveal (length_of (!var_a))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n)))) &&
          ((reveal (length_of (!var_b))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n))))))
    invariant (with_pure
        ((((((!var_i) `SizeT.lt` (!var_n)) && ((!var_j) `SizeT.lt` (!var_n))) &&
              ((!var_k) `SizeT.lte` (!var_n)))
            &&
            ((SizeT.v (!var_n)) <= 46))
          &&
          ((id #int (Int32.v (!var_max_val))) <= 46)))
    invariant (with_pure (SizeT.fits (SizeT.v (!var_n) `op_Multiply` SizeT.v (!var_n))))
    invariant (with_pure
        ((((!var_mv2) = ((!var_max_val) `Int32.mul` (!var_max_val))) &&
            (1 <= (id #int (Int32.v (!var_mv2)))))
          &&
          ((id #int (Int32.v (!var_mv2))) <= 2116)))
    invariant (with_pure
        ((id #int (Int32.v (!var_bound))) =
          ((SizeT.v (!var_k)) `op_Multiply` (id #int (Int32.v (!var_mv2))))))
    invariant (with_pure
        (((Int32.sub Int32.zero (!var_bound)) `Int32.lte` (!var_sum)) &&
          ((!var_sum) `Int32.lte` (!var_bound))))
    invariant (with_pure
        (forall
          (var_idx: SizeT.t).
          ((var_idx `SizeT.lt` ((!var_n) `SizeT.mul` (!var_n))) ==>
            (((Int32.sub Int32.zero (!var_max_val)) `Int32.lte` ((array_read (!var_a) var_idx))) &&
              (((array_read (!var_a) var_idx)) `Int32.lte` (!var_max_val))))))
    invariant (with_pure
        (forall
          (var_idx: SizeT.t).
          ((var_idx `SizeT.lt` ((!var_n) `SizeT.mul` (!var_n))) ==>
            (((Int32.sub Int32.zero (!var_max_val)) `Int32.lte` ((array_read (!var_b) var_idx))) &&
              (((array_read (!var_b) var_idx)) `Int32.lte` (!var_max_val))))))
    invariant (pure
        ((id #int (Int32.v (!var_sum))) = (dot_product_spec_c _va _vb
          (SizeT.v (!var_n)) (SizeT.v (!var_i)) (SizeT.v (!var_j)) (SizeT.v (!var_k)))))
    invariant (pure
        ((Seq.length _va = (SizeT.v ((!var_n) `SizeT.mul` (!var_n)))) &&
          (Seq.length _vb = (SizeT.v ((!var_n) `SizeT.mul` (!var_n))))))
    invariant (pure
        (Pulse.Lib.C.Array.array_initialized _va /\
          Pulse.Lib.C.Array.array_initialized _vb))
  {
    let mut var_av : Int32.t;
    var_av := ((array_read (!var_a) (((!var_i) `SizeT.mul` (!var_n)) `SizeT.add` (!var_k))));
    let mut var_bv : Int32.t;
    var_bv := ((array_read (!var_b) (((!var_k) `SizeT.mul` (!var_n)) `SizeT.add` (!var_j))));
    assert
      (with_pure
        (((Int32.sub Int32.zero (!var_max_val)) `Int32.lte` (!var_av)) &&
          ((!var_av) `Int32.lte` (!var_max_val))));
    assert
      (with_pure
        (((Int32.sub Int32.zero (!var_max_val)) `Int32.lte` (!var_bv)) &&
          ((!var_bv) `Int32.lte` (!var_max_val))));
    let mut var_prod : Int32.t;
    var_prod := ((!var_av) `Int32.mul` (!var_bv));
    assert
      (with_pure
        (((Int32.sub Int32.zero (!var_mv2)) `Int32.lte` (!var_prod)) &&
          ((!var_prod) `Int32.lte` (!var_mv2))));
    var_sum := ((!var_sum) `Int32.add` (!var_prod));
    var_bound := ((!var_bound) `Int32.add` (!var_mv2));
    var_k := ((!var_k) `SizeT.add` 1sz);
  };
  return (!var_sum);
}
#pop-options

#restart-solver
#push-options "--split_queries always"

fn func_matrix_multiply
    (var_a: (array Int32.t))
    (var_b: (array Int32.t))
    (var_c: (array Int32.t))
    (var_n: SizeT.t)
    (var_max_val: Int32.t)
    (#sa: Ghost.erased (Seq.seq (option Int32.t)))
    (#sb: Ghost.erased (Seq.seq (option Int32.t)))
  requires (pinned_array var_a sa)
  requires (pinned_array var_b sb)
  requires
    exists* (val_c_0: (Seq.seq (option Int32.t))) (val_c_1: (nat->prop)).
    ((array_pts_to var_c 1.0R val_c_0 val_c_1))
  requires (with_pure ((0 < (SizeT.v var_n)) && ((SizeT.v var_n) <= 46)))
  requires
    (with_pure ((0 < (id #int (Int32.v var_max_val))) && ((id #int (Int32.v var_max_val)) <= 46)))
  requires (with_pure (SizeT.fits (SizeT.v var_n `op_Multiply` SizeT.v var_n)))
  requires
    (with_pure
      ((((reveal (length_of var_a)) = (SizeT.v (var_n `SizeT.mul` var_n))) &&
          ((reveal (length_of var_b)) = (SizeT.v (var_n `SizeT.mul` var_n))))
        &&
        ((reveal (length_of var_c)) = (SizeT.v (var_n `SizeT.mul` var_n)))))
  requires
    (with_pure
      (forall
        (var_idx: SizeT.t).
        ((var_idx `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          (((Int32.sub Int32.zero var_max_val) `Int32.lte` ((array_read var_a var_idx))) &&
            (((array_read var_a var_idx)) `Int32.lte` var_max_val)))))
  requires
    (with_pure
      (forall
        (var_idx: SizeT.t).
        ((var_idx `SizeT.lt` (var_n `SizeT.mul` var_n)) ==>
          (((Int32.sub Int32.zero var_max_val) `Int32.lte` ((array_read var_b var_idx))) &&
            (((array_read var_b var_idx)) `Int32.lte` var_max_val)))))
  returns return_1 : unit
  ensures (pinned_array var_a sa)
  ensures (pinned_array var_b sb)
  ensures
    exists* (val_c_0: (Seq.seq (option Int32.t))) (val_c_1: (nat->prop)).
    ((array_pts_to var_c 1.0R val_c_0 val_c_1) **
      pure (mat_mul_partial_ij_c sa sb val_c_0
              (SizeT.v var_n) (SizeT.v var_n) 0 /\
            Seq.length val_c_0 == SizeT.v var_n `op_Multiply` SizeT.v var_n))
  ensures
    (with_pure
      ((((reveal (length_of var_a)) = (SizeT.v (var_n `SizeT.mul` var_n))) &&
          ((reveal (length_of var_b)) = (SizeT.v (var_n `SizeT.mul` var_n))))
        &&
        ((reveal (length_of var_c)) = (SizeT.v (var_n `SizeT.mul` var_n)))))
{
  let mut var_a = var_a;
  let mut var_b = var_b;
  let mut var_c = var_c;
  let mut var_n = var_n;
  let mut var_max_val = var_max_val;
  let mut var_i : SizeT.t;
  var_i := 0sz;
  while (((!var_i) `SizeT.lt` (!var_n)))
    invariant exists* (_vci: Seq.seq (option Int32.t)).
      ((live var_i) ** (pinned_array (!var_a) sa) **
        (pinned_array (!var_b) sb) **
        (pinned_array (!var_c) _vci)) **
      pure (mat_mul_partial_ij_c sa sb _vci
              (SizeT.v (!var_n)) (SizeT.v (!var_i)) 0 /\
            Seq.length _vci == SizeT.v ((!var_n) `SizeT.mul` (!var_n)))
    invariant (with_pure
        ((((reveal (length_of (!var_a))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n)))) &&
            ((reveal (length_of (!var_b))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n)))))
          &&
          ((reveal (length_of (!var_c))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n))))))
    invariant (with_pure
        ((((0 < SizeT.v (!var_n)) && ((!var_i) `SizeT.lte` (!var_n))) && ((SizeT.v (!var_n)) <= 46)) &&
          ((id #int (Int32.v (!var_max_val))) <= 46)))
    invariant (with_pure (SizeT.fits (SizeT.v (!var_n) `op_Multiply` SizeT.v (!var_n))))
    invariant (with_pure
        (forall
          (var_idx: SizeT.t).
          ((var_idx `SizeT.lt` ((!var_n) `SizeT.mul` (!var_n))) ==>
            (((Int32.sub Int32.zero (!var_max_val)) `Int32.lte` ((array_read (!var_a) var_idx))) &&
              (((array_read (!var_a) var_idx)) `Int32.lte` (!var_max_val))))))
    invariant (with_pure
        (forall
          (var_idx: SizeT.t).
          ((var_idx `SizeT.lt` ((!var_n) `SizeT.mul` (!var_n))) ==>
            (((Int32.sub Int32.zero (!var_max_val)) `Int32.lte` ((array_read (!var_b) var_idx))) &&
              (((array_read (!var_b) var_idx)) `Int32.lte` (!var_max_val))))))
    invariant (pure
        ((Seq.length sa = (SizeT.v ((!var_n) `SizeT.mul` (!var_n)))) &&
          (Seq.length sb = (SizeT.v ((!var_n) `SizeT.mul` (!var_n))))))
    invariant (pure
        (Pulse.Lib.C.Array.array_initialized sa /\
          Pulse.Lib.C.Array.array_initialized sb))
  {
    let mut var_j : SizeT.t;
    var_j := 0sz;
    while (((!var_j) `SizeT.lt` (!var_n)))
      invariant exists* (_vcj: Seq.seq (option Int32.t)).
        (((live var_i) ** (live var_j)) ** (pinned_array (!var_a) sa) **
          (pinned_array (!var_b) sb) **
          (pinned_array (!var_c) _vcj)) **
        pure (mat_mul_partial_ij_c sa sb _vcj
                (SizeT.v (!var_n)) (SizeT.v (!var_i)) (SizeT.v (!var_j)) /\
              Seq.length _vcj == SizeT.v ((!var_n) `SizeT.mul` (!var_n)))
      invariant (with_pure
          ((((reveal (length_of (!var_a))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n)))) &&
              ((reveal (length_of (!var_b))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n)))))
            &&
            ((reveal (length_of (!var_c))) = (SizeT.v ((!var_n) `SizeT.mul` (!var_n))))))
      invariant (with_pure
          (((((!var_i) `SizeT.lt` (!var_n)) && ((!var_j) `SizeT.lte` (!var_n))) &&
              ((SizeT.v (!var_n)) <= 46))
            &&
            ((id #int (Int32.v (!var_max_val))) <= 46)))
      invariant (with_pure (SizeT.fits (SizeT.v (!var_n) `op_Multiply` SizeT.v (!var_n))))
      invariant (with_pure
          (forall
            (var_idx: SizeT.t).
            ((var_idx `SizeT.lt` ((!var_n) `SizeT.mul` (!var_n))) ==>
              (((Int32.sub Int32.zero (!var_max_val)) `Int32.lte` ((array_read (!var_a) var_idx)))
                &&
                (((array_read (!var_a) var_idx)) `Int32.lte` (!var_max_val))))))
      invariant (with_pure
          (forall
            (var_idx: SizeT.t).
            ((var_idx `SizeT.lt` ((!var_n) `SizeT.mul` (!var_n))) ==>
              (((Int32.sub Int32.zero (!var_max_val)) `Int32.lte` ((array_read (!var_b) var_idx)))
                &&
                (((array_read (!var_b) var_idx)) `Int32.lte` (!var_max_val))))))
      invariant (pure
          ((Seq.length sa = (SizeT.v ((!var_n) `SizeT.mul` (!var_n)))) &&
            (Seq.length sb = (SizeT.v ((!var_n) `SizeT.mul` (!var_n))))))
      invariant (pure
          (Pulse.Lib.C.Array.array_initialized sa /\
            Pulse.Lib.C.Array.array_initialized sb))
    {
      // Compute dot product
      let dot_result = func_dot_product (!var_a) (!var_b) (!var_n) (!var_i) (!var_j) (!var_max_val) #sa #sb;

      // Capture c's ghost seq before write, call update lemma
      let _vc = array_value_of (!var_c);
      mat_mul_partial_ij_c_update sa sb _vc (SizeT.v (!var_n)) (SizeT.v (!var_i)) (SizeT.v (!var_j)) dot_result;

      // Write C[i*n+j] = dot_result
      (array_write
          (!var_c)
          (((!var_i) `SizeT.mul` (!var_n)) `SizeT.add` (!var_j))
          dot_result);

      var_j := ((!var_j) `SizeT.add` 1sz);
    };
    // Row advance: mat_mul_partial_ij_c ... i n => ... (i+1) 0
    let _vc_row = array_value_of (!var_c);
    mat_mul_partial_ij_c_row_advance sa sb _vc_row (SizeT.v (!var_n)) (SizeT.v (!var_i));

    var_i := ((!var_i) `SizeT.add` 1sz);
  };
  // The i-loop invariant with i==n gives mat_mul_partial_ij_c sa sb _vci n n 0.
  // mat_mul_partial_ij_c_complete then gives mat_mul_correct_c.
  // For now, we rely on SMT — if needed, call the lemma explicitly.
}
#pop-options