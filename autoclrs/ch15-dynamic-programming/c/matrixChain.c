/*
 * Matrix Chain Multiplication — C implementation with c2pulse verification.
 *
 * Bottom-up dynamic programming approach from CLRS Chapter 15.
 * Split into init_table + matrix_chain to minimize let muts in main function.
 * Eliminates j variable (uses i+l-1 inline) for fewer mutable locals.
 * Post-process generated Pulse: remove let mut for never-reassigned params.
 *
 * Proves: result == mc_result(dims, n), NO admits.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(open Pulse.Lib.C.Array)
_include_pulse(open CLRS.Ch15.MatrixChain.Spec)
_include_pulse(open CLRS.Ch15.MatrixChain.C.BridgeLemmas)

/* Helper: compute flat 2D index a*n + b with proven bound and equality. */
size_t compute_index(size_t a, size_t b, size_t n)
  _requires(a < n)
  _requires(b < n)
  _requires(n >= 1)
  _requires((bool) _inline_pulse(SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _ensures(return < n * n)
  _ensures(return == a * n + b)
{
  return a * n + b;
}

/* Initialize DP table to all zeros.
   Postcondition is element-wise; caller calls to_int_seq_create_zero. */
void init_table(_array int *m, size_t n)
  _requires(n >= 1 && n <= 1000)
  _requires((bool) _inline_pulse(
    reveal (length_of $(m)) = SizeT.v $(n) * SizeT.v $(n)))
  _requires((bool) _inline_pulse(
    SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _ensures((bool) _inline_pulse(
    reveal (length_of $(m)) = SizeT.v $(n) * SizeT.v $(n)))
  _ensures((bool) _inline_pulse(
    SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _ensures(_forall(size_t w,
    (bool) _inline_pulse(SizeT.v var_w >= SizeT.v $(n) * SizeT.v $(n))
    || (m[w] >= 0 && m[w] <= 1000000000)))
  _ensures((_slprop) _inline_pulse(
    with_pure (forall (i: nat). i < SizeT.v $(n) * SizeT.v $(n) ==>
      Seq.index (to_int_seq (array_value_of $(m))) i == 0)))
{
  for (size_t idx = 0; idx < n * n; idx = idx + 1)
    _invariant(_live(idx))
    _invariant(_live(*m))
    _invariant(n >= 1 && n <= 1000)
    _invariant((bool) _inline_pulse(
      reveal (length_of $(m)) = SizeT.v $(n) * SizeT.v $(n)))
    _invariant((bool) _inline_pulse(
      SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
    _invariant((bool) _inline_pulse(
      SizeT.v $(idx) <= SizeT.v $(n) * SizeT.v $(n)))
    _invariant(_forall(size_t w,
      (bool) _inline_pulse(SizeT.v var_w >= SizeT.v $(idx))
      || (m[w] >= 0 && m[w] <= 1000000000)))
    _invariant((_slprop) _inline_pulse(
      with_pure (forall (i: nat). i < SizeT.v $(idx) ==>
        Seq.index (to_int_seq (array_value_of $(m))) i == 0)))
  {
    m[idx] = 0;
  }
}

int matrix_chain(_array int *dims, size_t n, _array int *m)
  _preserves(dims._length == n + 1)
  _requires(n >= 1 && n <= 1000)
  _requires((bool) _inline_pulse(
    reveal (length_of $(m)) = SizeT.v $(n) * SizeT.v $(n)))
  _ensures((bool) _inline_pulse(
    reveal (length_of $(m)) = SizeT.v $(n) * SizeT.v $(n)))
  _requires((bool) _inline_pulse(
    SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
  _requires(_forall(size_t w, w > n || (dims[w] >= 0 && dims[w] <= 200)))
  _ensures(return >= 0)
  _ensures(_forall(size_t w,
    (bool) _inline_pulse(SizeT.v var_w >= SizeT.v $(n) * SizeT.v $(n))
    || m[w] >= 0))
  _ensures((_slprop) _inline_pulse(
    with_pure (
      id #int (Int32.v return_1) =
        mc_result
          (to_int_seq (array_value_of $(dims)))
          (SizeT.v $(n)))))
{
  /* Initialize table to all zeros */
  init_table(m, n);

  /* Ghost: bridge from element-wise zeros to create equality */
  _ghost_stmt(
    to_int_seq_create_zero
      (array_value_of $(m))
      (SizeT.v $(n) * SizeT.v $(n)));

  /* Main DP: chain lengths l = 2..n */
  for (size_t l = 2; l <= n; l = l + 1)
    _invariant(_live(l))
    _invariant(_live(*m) && _live(*dims))
    _invariant(l >= 2 && l <= n + 1)
    _invariant(n >= 1 && n <= 1000)
    _invariant(dims._length == n + 1)
    _invariant((bool) _inline_pulse(
      reveal (length_of $(m)) = SizeT.v $(n) * SizeT.v $(n)))
    _invariant((bool) _inline_pulse(
      SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
    _invariant(_forall(size_t w, w > n || (dims[w] >= 0 && dims[w] <= 200)))
    _invariant(_forall(size_t w,
      (bool) _inline_pulse(SizeT.v var_w >= SizeT.v $(n) * SizeT.v $(n))
      || (m[w] >= 0 && m[w] <= 1000000000)))
    _invariant((_slprop) _inline_pulse(
      with_pure (
        mc_outer
          (to_int_seq (array_value_of $(m)))
          (to_int_seq (array_value_of $(dims)))
          (SizeT.v $(n)) (SizeT.v $(l))
        ==
        mc_outer
          (Seq.create (SizeT.v $(n) * SizeT.v $(n)) 0)
          (to_int_seq (array_value_of $(dims)))
          (SizeT.v $(n)) 2)))
  {
    /* Ghost: unfold mc_outer one step at the start of the i-loop */
    _ghost_stmt(
      mc_outer_unfold
        (to_int_seq (array_value_of $(m)))
        (to_int_seq (array_value_of $(dims)))
        (SizeT.v $(n)) (SizeT.v $(l)));

    for (size_t i = 0; i + l <= n; i = i + 1)
      _invariant(_live(i) && _live(l))
      _invariant(_live(*m) && _live(*dims))
      _invariant(l >= 2 && l <= n)
      _invariant(n >= 1 && n <= 1000)
      _invariant(dims._length == n + 1)
      _invariant((bool) _inline_pulse(
        reveal (length_of $(m)) = SizeT.v $(n) * SizeT.v $(n)))
      _invariant((bool) _inline_pulse(
        SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
      _invariant(_forall(size_t w, w > n || (dims[w] >= 0 && dims[w] <= 200)))
      _invariant(_forall(size_t w,
        (bool) _inline_pulse(SizeT.v var_w >= SizeT.v $(n) * SizeT.v $(n))
        || (m[w] >= 0 && m[w] <= 1000000000)))
      _invariant((bool) _inline_pulse(
        SizeT.v $(i) + SizeT.v $(l) <= SizeT.v $(n) + 1))
      _invariant((_slprop) _inline_pulse(
        with_pure (
          mc_outer
            (mc_inner_i
              (to_int_seq (array_value_of $(m)))
              (to_int_seq (array_value_of $(dims)))
              (SizeT.v $(n)) (SizeT.v $(l)) (SizeT.v $(i)))
            (to_int_seq (array_value_of $(dims)))
            (SizeT.v $(n)) (SizeT.v $(l) + 1)
          ==
          mc_outer
            (Seq.create (SizeT.v $(n) * SizeT.v $(n)) 0)
            (to_int_seq (array_value_of $(dims)))
            (SizeT.v $(n)) 2)))
    {
      /* Save loop vars to immutable copies (avoids mutable state disconnection after k-loop) */
      size_t vi = i;
      size_t vl = l;
      size_t j_val = vi + vl - 1;

      int min_cost = 1000000000;

      for (size_t k = vi; k < j_val; k = k + 1)
        _invariant(_live(vi) && _live(vl) && _live(j_val) && _live(k) && _live(min_cost) && _live(i) && _live(l))
        _invariant(_live(*m) && _live(*dims))
        _invariant((bool) _inline_pulse(SizeT.v $(vl) >= 2 && SizeT.v $(vl) <= SizeT.v $(n)))
        _invariant(n >= 1 && n <= 1000)
        _invariant(dims._length == n + 1)
        _invariant((bool) _inline_pulse(
          reveal (length_of $(m)) = SizeT.v $(n) * SizeT.v $(n)))
        _invariant((bool) _inline_pulse(
          SizeT.fits (SizeT.v $(n) * SizeT.v $(n))))
        _invariant(_forall(size_t w, w > n || (dims[w] >= 0 && dims[w] <= 200)))
        _invariant(_forall(size_t w,
          (bool) _inline_pulse(SizeT.v var_w >= SizeT.v $(n) * SizeT.v $(n))
          || (m[w] >= 0 && m[w] <= 1000000000)))
        _invariant((bool) _inline_pulse(
          SizeT.v $(vi) + SizeT.v $(vl) <= SizeT.v $(n)))
        _invariant((bool) _inline_pulse(
          SizeT.v $(j_val) = SizeT.v $(vi) + SizeT.v $(vl) - 1))
        _invariant((bool) _inline_pulse(
          SizeT.v $(k) >= SizeT.v $(vi) &&
          SizeT.v $(k) <= SizeT.v $(j_val)))
        _invariant(min_cost >= 0 && min_cost <= 1000000000)
        _invariant((bool) _inline_pulse(
          SizeT.v $(i) = SizeT.v $(vi) && SizeT.v $(l) = SizeT.v $(vl)))
        _invariant((_slprop) _inline_pulse(
          with_pure (
            mc_inner_k
              (to_int_seq (array_value_of $(m)))
              (to_int_seq (array_value_of $(dims)))
              (SizeT.v $(n)) (SizeT.v $(vi))
              (SizeT.v $(j_val))
              (SizeT.v $(k)) (Int32.v $(min_cost))
            ==
            mc_inner_k
              (to_int_seq (array_value_of $(m)))
              (to_int_seq (array_value_of $(dims)))
              (SizeT.v $(n)) (SizeT.v $(vi))
              (SizeT.v $(j_val))
              (SizeT.v $(vi)) 1000000000)))
        _invariant((_slprop) _inline_pulse(
          with_pure (
            mc_outer
              (mc_inner_i
                (to_int_seq (array_value_of $(m)))
                (to_int_seq (array_value_of $(dims)))
                (SizeT.v $(n)) (SizeT.v $(vl)) (SizeT.v $(vi)))
              (to_int_seq (array_value_of $(dims)))
              (SizeT.v $(n)) (SizeT.v $(vl) + 1)
            ==
            mc_outer
              (Seq.create (SizeT.v $(n) * SizeT.v $(n)) 0)
              (to_int_seq (array_value_of $(dims)))
              (SizeT.v $(n)) 2)))
      {
        size_t ci = compute_index(vi, k, n);
        size_t ci2 = compute_index(k + 1, j_val, n);
        int cost_ik = m[ci];
        int cost_kj = m[ci2];
        int dim_i = dims[vi];
        int dim_k1 = dims[k + 1];
        int dim_j1 = dims[j_val + 1];
        int mult_cost = dim_i * dim_k1 * dim_j1;
        int q = cost_ik + cost_kj + mult_cost;

        /* Ghost: explicit step lemma so Z3 doesn't need fuel to unfold mc_inner_k */
        _ghost_stmt(
          mc_inner_k_step
            (to_int_seq (array_value_of $(m)))
            (to_int_seq (array_value_of $(dims)))
            (SizeT.v $(n)) (SizeT.v $(vi)) (SizeT.v $(j_val))
            (SizeT.v $(k)) (Int32.v $(min_cost)));

        if (q < min_cost) {
          min_cost = q;
        }
      }

      /* Ghost: mc_inner_k base case when k >= j_val */
      _ghost_stmt(
        mc_inner_k_base
          (to_int_seq (array_value_of $(m)))
          (to_int_seq (array_value_of $(dims)))
          (SizeT.v $(n)) (SizeT.v $(vi)) (SizeT.v $(j_val))
          (SizeT.v $(k)) (Int32.v $(min_cost)));

      /* After k-loop: min_cost == mc_inner_k base case */
      _assert((_slprop) _inline_pulse(
        with_pure (
          id #int (Int32.v $(min_cost)) ==
            mc_inner_k
              (to_int_seq (array_value_of $(m)))
              (to_int_seq (array_value_of $(dims)))
              (SizeT.v $(n)) (SizeT.v $(vi))
              (SizeT.v $(j_val))
              (SizeT.v $(vi)) 1000000000)));

      /* Compute write index using immutable locals */
      size_t ci_ij = compute_index(vi, j_val, n);

      /* Ghost: establish full mc_outer invariant on updated table */
      _ghost_stmt(
        mc_i_step_full
          (array_value_of $(m))
          (array_value_of $(dims))
          (SizeT.v $(n)) (SizeT.v $(vl)) (SizeT.v $(vi))
          $(min_cost)
          (SizeT.v $(ci_ij)));

      /* Write m[i][j] = min_cost */
      m[ci_ij] = min_cost;
    }

    /* Ghost: mc_inner_i base case — when i + l > n, mc_inner_i is identity */
    _ghost_stmt(
      mc_inner_i_base
        (to_int_seq (array_value_of $(m)))
        (to_int_seq (array_value_of $(dims)))
        (SizeT.v $(n)) (SizeT.v $(l)) (SizeT.v $(i)));
  }

  /* Ghost: mc_outer at l > n is identity */
  _ghost_stmt(
    mc_outer_identity
      (to_int_seq (array_value_of $(m)))
      (to_int_seq (array_value_of $(dims)))
      (SizeT.v $(n))
      (SizeT.v $(l)));

  /* Ghost: mc_result from table */
  _ghost_stmt(
    mc_result_from_table
      (to_int_seq (array_value_of $(dims)))
      (SizeT.v $(n))
      (to_int_seq (array_value_of $(m))));

  _assert((bool) _inline_pulse(0 < SizeT.v $(n)));
  return m[n - 1];
}
