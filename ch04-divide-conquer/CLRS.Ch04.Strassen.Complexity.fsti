(*
   Strassen's Algorithm — Complexity Analysis (CLRS §4.2)
   
   Interface for complexity definitions and bounds:
   - Strassen performs 7^(log₂ n) scalar multiplications
   - This is strictly less than n³ for n > 1
*)

module CLRS.Ch04.Strassen.Complexity

open FStar.Mul
open FStar.Math.Lemmas
open CLRS.Ch04.Strassen.Spec

val log2_floor (n:pos) : Tot nat (decreases n)

val pow7 (n:nat) : Tot pos (decreases n)

val strassen_mult_count (n:pos{is_pow2 n}) : Tot nat (decreases n)

val standard_mult_count (n:pos) : nat

val lemma_strassen_better_than_cubic (n:pos{is_pow2 n /\ n > 1})
  : Lemma (ensures strassen_mult_count n < standard_mult_count n)

val lemma_pow2_log2_inverse (n:pos{is_pow2 n})
  : Lemma (ensures pow2 (log2_floor n) == n)

val lemma_log2_half (n:pos{is_pow2 n /\ n > 1})
  : Lemma (ensures log2_floor n == 1 + log2_floor (n / 2))

val lemma_pow7_succ (k:nat)
  : Lemma (ensures pow7 (k + 1) == 7 * pow7 k)

val lemma_strassen_mult_closed_form (n:pos{is_pow2 n})
  : Lemma (ensures (let k = log2_floor n in
                    strassen_mult_count n == pow7 k))
