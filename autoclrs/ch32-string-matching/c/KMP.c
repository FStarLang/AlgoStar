/*
 * KMP String Matching — C implementation with c2pulse verification.
 * (CLRS §32.4)
 *
 * Two phases: compute_prefix fills the prefix (failure) function,
 * then kmp_count uses it for linear-time matching.
 *
 * Proves: memory safety, pi bounds (0 <= pi[j] <= j),
 *         functional correctness: count == count_matches_spec.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>

_include_pulse(open CLRS.Ch32.KMP.PureDefs)
_include_pulse(open CLRS.Ch32.KMP.Spec)
_include_pulse(open CLRS.Ch32.KMP.C.BridgeLemmas)
_include_pulse(open CLRS.Ch32.KMP.Bridge)

/* Compute the prefix (failure) function for pattern[0..m-1].
 * Stores pi[j] = length of longest proper prefix of pattern[0..j]
 * that is also a suffix, for each j in [0, m). */
void compute_prefix(_array int *pattern, size_t m, _array int *pi)
  _preserves(pattern._length == m)
  _requires(pi._length == m && m > 0)
  _requires((_specint) m < 2147483647)
  _ensures(pi._length == m)
  _ensures(_forall(size_t j, j < m ==> pi[j] >= 0))
  _ensures(_forall(size_t j, j < m ==> (_specint) pi[j] <= (_specint) j))
  _ensures(pattern._length == m)
  _ensures((_slprop) _inline_pulse(
    with_pure (
      pi_max_up_to_int
        (unwrap_int_seq (array_value_of var_pattern) (SizeT.v var_m))
        (unwrap_int_seq (array_value_of var_pi) (SizeT.v var_m))
        (SizeT.v var_m)
    )
  ))
{
  _ghost_stmt(let _vp = array_value_of (!var_pattern));

  pi[0] = 0;
  int k = 0;

  _ghost_stmt(
    maximality_base_int
      (unwrap_int_seq _vp (SizeT.v (!var_m)))
      (unwrap_int_seq (array_value_of (!var_pi)) (SizeT.v (!var_m)))
  );

  for (size_t q = 1; q < m; q = q + 1)
    _invariant(_live(q) && _live(k))
    _invariant((_slprop) _inline_pulse(
      exists* (val_pi: (Seq.seq (option Int32.t))) (mask_p: (nat -> prop)) (mask_pi: (nat -> prop)).
        (array_pts_to (!var_pattern) 1.0R _vp mask_p) **
        (array_pts_to (!var_pi) 1.0R val_pi mask_pi)
    ))
    _invariant(pattern._length == m && pi._length == m)
    _invariant(q <= m && m > 0)
    _invariant(k >= 0)
    _invariant((_specint) k < (_specint) q)
    _invariant((_specint) m < 2147483647)
    _invariant(_forall(size_t j, j < q ==> pi[j] >= 0))
    _invariant(_forall(size_t j, j < q ==> (_specint) pi[j] <= (_specint) j))
    _invariant((_slprop) _inline_pulse(
      with_pure (
        pi_max_up_to_int
          (unwrap_int_seq _vp (SizeT.v (!var_m)))
          (unwrap_int_seq (array_value_of (!var_pi)) (SizeT.v (!var_m)))
          (SizeT.v (!var_q))
      )
    ))
    _invariant((_slprop) _inline_pulse(
      with_pure (
        is_prefix_suffix #int
          (unwrap_int_seq _vp (SizeT.v (!var_m)))
          (SizeT.v (!var_q) - 1)
          (to_nat (Int32.v (!var_k)))
      )
    ))
    _invariant((_slprop) _inline_pulse(
      with_pure (
        Int32.v (!var_k) ==
        unwrap_int_val (Seq.index (array_value_of (!var_pi)) (SizeT.v (!var_q) - 1))
      )
    ))
  {
    _ghost_stmt(let _vpi = array_value_of (!var_pi));

    _ghost_stmt(
      inner_init_int
        (unwrap_int_seq _vp (SizeT.v (!var_m)))
        (unwrap_int_seq _vpi (SizeT.v (!var_m)))
        (SizeT.v (!var_q))
        (to_nat (Int32.v (!var_k)))
    );

    /* Follow failure chain until match or k == 0 */
    int found = 0;
    while (k > 0 && found == 0)
      _invariant(_live(k) && _live(found))
      _invariant((_slprop) _inline_pulse(
        exists* (mask_p: (nat -> prop)) (mask_pi: (nat -> prop)).
          (array_pts_to (!var_pattern) 1.0R _vp mask_p) **
          (array_pts_to (!var_pi) 1.0R _vpi mask_pi)
      ))
      _invariant(pattern._length == m && pi._length == m)
      _invariant(k >= 0)
      _invariant((_specint) k < (_specint) q && q < m)
      _invariant((_specint) m < 2147483647)
      _invariant(m > 0)
      _invariant(found == 0 || found == 1)
      _invariant(found == 1 ==> pattern[(size_t)k] == pattern[q])
      _invariant(_forall(size_t j, j < q ==> pi[j] >= 0))
      _invariant(_forall(size_t j, j < q ==> (_specint) pi[j] <= (_specint) j))
      _invariant((_slprop) _inline_pulse(
        with_pure (
          pi_max_up_to_int
            (unwrap_int_seq _vp (SizeT.v (!var_m)))
            (unwrap_int_seq _vpi (SizeT.v (!var_m)))
            (SizeT.v (!var_q))
        )
      ))
      _invariant((_slprop) _inline_pulse(
        with_pure (
          is_prefix_suffix #int
            (unwrap_int_seq _vp (SizeT.v (!var_m)))
            (SizeT.v (!var_q) - 1)
            (to_nat (Int32.v (!var_k)))
        )
      ))
      _invariant((_slprop) _inline_pulse(
        with_pure (
          CLRS.Ch32.KMP.Bridge.all_ps_above_mismatch #int
            (unwrap_int_seq _vp (SizeT.v (!var_m)))
            (SizeT.v (!var_q))
            (to_nat (Int32.v (!var_k)))
        )
      ))
    {
      if (pattern[(size_t)k] == pattern[q]) {
        found = 1;
      } else {
        _ghost_stmt(
          unwrap_seq_index_lemma _vp
            (SizeT.v (!var_m))
            (to_nat (Int32.v (!var_k)))
        );
        _ghost_stmt(
          unwrap_seq_index_lemma _vp
            (SizeT.v (!var_m))
            (SizeT.v (!var_q))
        );
        _ghost_stmt(
          pi_max_instantiate_int
            (unwrap_int_seq _vp (SizeT.v (!var_m)))
            (unwrap_int_seq _vpi (SizeT.v (!var_m)))
            (SizeT.v (!var_q))
            (to_nat (Int32.v (!var_k) - 1))
        );
        _ghost_stmt(
          unwrap_seq_index_lemma _vpi
            (SizeT.v (!var_m))
            (to_nat (Int32.v (!var_k) - 1))
        );
        _ghost_stmt(
          inner_step_int
            (unwrap_int_seq _vp (SizeT.v (!var_m)))
            (unwrap_int_seq _vpi (SizeT.v (!var_m)))
            (SizeT.v (!var_q))
            (to_nat (Int32.v (!var_k)))
            (to_nat (unwrap_int_val (Seq.index _vpi (to_nat (Int32.v (!var_k) - 1)))))
        );
        k = pi[(size_t)(k - 1)];
      }
    }

    int k_final = k;

    if (pattern[(size_t)k] == pattern[q]) {
      k = k + 1;
    }

    _assert(k >= 0);
    _assert((_specint)k <= (_specint)q);

    pi[q] = k;

    _ghost_stmt(let _vpi_new = array_value_of (!var_pi));
    _ghost_stmt(
      unwrap_seq_update _vpi
        (SizeT.v (!var_m))
        (SizeT.v (!var_q))
        (!var_k)
    );
    _ghost_stmt(
      unwrap_seq_index_lemma _vp
        (SizeT.v (!var_m))
        (to_nat (Int32.v (!var_k_final)))
    );
    _ghost_stmt(
      unwrap_seq_index_lemma _vp
        (SizeT.v (!var_m))
        (SizeT.v (!var_q))
    );
    _ghost_stmt(
      extend_maximality_int
        (unwrap_int_seq _vp (SizeT.v (!var_m)))
        (unwrap_int_seq _vpi (SizeT.v (!var_m)))
        (unwrap_int_seq _vpi_new (SizeT.v (!var_m)))
        (SizeT.v (!var_q))
        (to_nat (Int32.v (!var_k_final)))
        (op_Equality
          (Seq.index (unwrap_int_seq _vp (SizeT.v (!var_m))) (to_nat (Int32.v (!var_k_final))))
          (Seq.index (unwrap_int_seq _vp (SizeT.v (!var_m))) (SizeT.v (!var_q))))
    );
  }
}

/* Count pattern occurrences in text using prefix function pi. */
size_t kmp_count(_array int *text, size_t n,
                 _array int *pattern, size_t m,
                 _array int *pi)
  _preserves(text._length == n)
  _preserves(pattern._length == m)
  _preserves(pi._length == m)
  _requires(m > 0 && m <= n)
  _requires((_specint) m < 2147483647)
  _requires(_forall(size_t j, j < m ==> pi[j] >= 0))
  _requires(_forall(size_t j, j < m ==> (_specint) pi[j] <= (_specint) j))
  _requires((_slprop) _inline_pulse(
    with_pure (
      pi_max
        (unwrap_int_seq (array_value_of var_pattern) (SizeT.v var_m))
        (unwrap_int_seq (array_value_of var_pi) (SizeT.v var_m))
    )
  ))
  _ensures(return <= n - m + 1)
  _ensures(_forall(size_t j, j < m ==> pi[j] >= 0))
  _ensures(_forall(size_t j, j < m ==> (_specint) pi[j] <= (_specint) j))
  _ensures((_slprop) _inline_pulse(
    with_pure (
      SizeT.v return_1 =
        count_matches_spec
          (unwrap_int_seq (array_value_of var_text) (SizeT.v var_n))
          (unwrap_int_seq (array_value_of var_pattern) (SizeT.v var_m))
          (SizeT.v var_n) (SizeT.v var_m)
    )
  ))
{
  _ghost_stmt(let _vt = array_value_of (!var_text));
  _ghost_stmt(let _vp = array_value_of (!var_pattern));
  _ghost_stmt(let _vpi = array_value_of (!var_pi));

  _ghost_stmt(
    is_max_prefix_below_init
      (unwrap_int_seq _vt (SizeT.v (!var_n)))
      (unwrap_int_seq _vp (SizeT.v (!var_m)))
      (SizeT.v (!var_n)) (SizeT.v (!var_m))
  );

  int q = 0;
  size_t count = 0;
  for (size_t i = 0; i < n; i = i + 1)
    _invariant(_live(i) && _live(q) && _live(count))
    _invariant((_slprop) _inline_pulse(
      exists* (mask_t: (nat -> prop)) (mask_p: (nat -> prop)) (mask_pi: (nat -> prop)).
        (array_pts_to (!var_text) 1.0R _vt mask_t) **
        (array_pts_to (!var_pattern) 1.0R _vp mask_p) **
        (array_pts_to (!var_pi) 1.0R _vpi mask_pi)
    ))
    _invariant(text._length == n && pattern._length == m && pi._length == m && i <= n && q >= 0 && (_specint) q < (_specint) m && (_specint) q <= (_specint) i && (_specint) q + 1 <= 2147483647 && m > 0 && m <= n && (_specint) m < 2147483647)
    _invariant(_forall(size_t j, j < m ==> pi[j] >= 0))
    _invariant(_forall(size_t j, j < m ==> (_specint) pi[j] <= (_specint) j))
    _invariant((_specint) i < (_specint) m ==> count == 0)
    _invariant((_specint) i >= (_specint) m ==> (_specint) count <= (_specint) i - (_specint) m + 1)
    _invariant((_slprop) _inline_pulse(
      with_pure (
        Prims.l_and
          (pi_max
            (unwrap_int_seq _vp (SizeT.v (!var_m)))
            (unwrap_int_seq _vpi (SizeT.v (!var_m))))
          (Prims.l_and
            (is_max_prefix_below
              (unwrap_int_seq _vt (SizeT.v (!var_n)))
              (unwrap_int_seq _vp (SizeT.v (!var_m)))
              (SizeT.v (!var_i))
              (to_nat (Int32.v (!var_q))))
            (Prims.l_and
              (SizeT.v (!var_i) >= SizeT.v (!var_m) ==>
                SizeT.v (!var_count) =
                  count_before
                    (unwrap_int_seq _vt (SizeT.v (!var_n)))
                    (unwrap_int_seq _vp (SizeT.v (!var_m)))
                    (SizeT.v (!var_i) - SizeT.v (!var_m) + 1))
              (SizeT.v (!var_i) < SizeT.v (!var_m) ==>
                SizeT.v (!var_count) = 0)))
      )
    ))
  {
    int q_init = q;
    /* Follow failure chain (break-free compound condition) */
    int found = 0;
    while (q > 0 && found == 0)
      _invariant(_live(q) && _live(found) && _live(q_init))
      _invariant((_slprop) _inline_pulse(
        exists* (mask_t: (nat -> prop)) (mask_p: (nat -> prop)) (mask_pi: (nat -> prop)).
          (array_pts_to (!var_text) 1.0R _vt mask_t) **
          (array_pts_to (!var_pattern) 1.0R _vp mask_p) **
          (array_pts_to (!var_pi) 1.0R _vpi mask_pi)
      ))
      _invariant(text._length == n && pattern._length == m && pi._length == m && q >= 0 && (_specint) q < (_specint) m && (_specint) q <= (_specint) i && i < n && (_specint) q + 1 <= 2147483647 && m > 0 && m <= n && (_specint) m < 2147483647 && (found == 0 || found == 1) && q_init >= 0 && (_specint) q_init < (_specint) m && (_specint) q <= (_specint) q_init)
      _invariant(_forall(size_t j, j < m ==> pi[j] >= 0))
      _invariant(_forall(size_t j, j < m ==> (_specint) pi[j] <= (_specint) j))
      _invariant((_specint) i < (_specint) m ==> count == 0)
      _invariant((_specint) i >= (_specint) m ==> (_specint) count <= (_specint) i - (_specint) m + 1)
      _invariant((_slprop) _inline_pulse(
        with_pure (
          Prims.l_and
            (pi_max
              (unwrap_int_seq _vp (SizeT.v (!var_m)))
              (unwrap_int_seq _vpi (SizeT.v (!var_m))))
            (Prims.l_and
              (is_max_prefix_below
                (unwrap_int_seq _vt (SizeT.v (!var_n)))
                (unwrap_int_seq _vp (SizeT.v (!var_m)))
                (SizeT.v (!var_i))
                (to_nat (Int32.v (!var_q_init))))
              (Prims.l_and
                (follow_fail
                  (unwrap_int_seq _vp (SizeT.v (!var_m)))
                  (unwrap_int_seq _vpi (SizeT.v (!var_m)))
                  (to_nat (Int32.v (!var_q_init)))
                  (unwrap_int_val (Seq.index _vt (SizeT.v (!var_i))))
                ==
                follow_fail
                  (unwrap_int_seq _vp (SizeT.v (!var_m)))
                  (unwrap_int_seq _vpi (SizeT.v (!var_m)))
                  (to_nat (Int32.v (!var_q)))
                  (unwrap_int_val (Seq.index _vt (SizeT.v (!var_i)))))
                (Prims.l_and
                  (SizeT.v (!var_i) >= SizeT.v (!var_m) ==>
                    SizeT.v (!var_count) =
                      count_before
                        (unwrap_int_seq _vt (SizeT.v (!var_n)))
                        (unwrap_int_seq _vp (SizeT.v (!var_m)))
                        (SizeT.v (!var_i) - SizeT.v (!var_m) + 1))
                  (Prims.l_and
                    (SizeT.v (!var_i) < SizeT.v (!var_m) ==>
                      SizeT.v (!var_count) = 0)
                    (Prims.l_and
                      (((to_nat (Int32.v (!var_found))) = 1) ==>
                        ((to_nat (Int32.v (!var_q))) > 0))
                      (((to_nat (Int32.v (!var_found))) = 1) ==>
                        (unwrap_int_val (Seq.index _vp (to_nat (Int32.v (!var_q)))) =
                         unwrap_int_val (Seq.index _vt (SizeT.v (!var_i)))))))))))
      ))
    {
      if (pattern[(size_t)q] == text[i]) {
        found = 1;
      } else {
        _ghost_stmt(
          follow_fail_step
            (unwrap_int_seq _vp (SizeT.v (!var_m)))
            (unwrap_int_seq _vpi (SizeT.v (!var_m)))
            (to_nat (Int32.v (!var_q)))
            (unwrap_int_val (Seq.index _vt (SizeT.v (!var_i))))
        );
        q = pi[(size_t)(q - 1)];
      }
    }

    /* Bridge: connect inner loop result to kmp_step_result */
    _ghost_stmt(
      unwrap_seq_index_lemma _vp
        (SizeT.v (!var_m))
        (to_nat (Int32.v (!var_q)))
    );

    _ghost_stmt(
      kmp_extend_connection
        (unwrap_int_seq _vp (SizeT.v (!var_m)))
        (unwrap_int_seq _vpi (SizeT.v (!var_m)))
        (to_nat (Int32.v (!var_q_init)))
        (to_nat (Int32.v (!var_q)))
        (unwrap_int_val (Seq.index _vt (SizeT.v (!var_i))))
        (SizeT.v (!var_m))
    );

    if (pattern[(size_t)q] == text[i]) {
      q = q + 1;
    }

    size_t count_before_match = count;

    if (q >= 0 && (size_t)q == m) {
      count = count + 1;
      q = pi[(size_t)(q - 1)];
    }

    _ghost_stmt(
      kmp_count_step
        (unwrap_int_seq _vt (SizeT.v (!var_n)))
        (unwrap_int_seq _vp (SizeT.v (!var_m)))
        (unwrap_int_seq _vpi (SizeT.v (!var_m)))
        (SizeT.v (!var_i))
        (to_nat (Int32.v (!var_q_init)))
        (SizeT.v (!var_count_before_match))
    );
  }

  _ghost_stmt(
    count_finish _vt _vp
      (SizeT.v (!var_n)) (SizeT.v (!var_m))
  );
  _ghost_stmt(
    count_matches_spec_bounded
      (unwrap_int_seq _vt (SizeT.v (!var_n)))
      (unwrap_int_seq _vp (SizeT.v (!var_m)))
      (SizeT.v (!var_n)) (SizeT.v (!var_m))
  );

  return count;
}
