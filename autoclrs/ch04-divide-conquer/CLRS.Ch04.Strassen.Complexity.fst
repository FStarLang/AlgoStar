(*
   Strassen's Algorithm — Complexity Analysis (CLRS §4.2)
   
   Proofs that Strassen uses 7^(log₂ n) scalar multiplications,
   which is O(n^{lg 7}) ≈ O(n^{2.807}), strictly better than n³.
*)

module CLRS.Ch04.Strassen.Complexity
open FStar.Math.Lemmas
open CLRS.Ch04.Strassen.Spec

// Helper for log2
let rec log2_floor (n:pos) : Tot nat =
  if n = 1 then 0
  else 1 + log2_floor (n / 2)

// Power of 7 function (7^n)
let rec pow7 (n:nat) : Tot pos =
  if n = 0 then 1
  else 7 * pow7 (n - 1)

//SNIPPET_START: strassen_complexity
// Number of matrix multiplications performed by Strassen
let rec strassen_mult_count (n:pos{is_pow2 n}) : Tot nat =
  if n = 1 then 1
  else 7 * strassen_mult_count (n / 2)

// Standard matrix multiply: n³ multiplications
let standard_mult_count (n:pos) : nat = n * n * n

// Strassen performs fewer multiplications than standard
let rec lemma_strassen_better_than_cubic (n:pos{is_pow2 n /\ n > 1})
  : Lemma (ensures strassen_mult_count n < standard_mult_count n)
          (decreases n)
  = if n = 2 then ()
    else lemma_strassen_better_than_cubic (n / 2)
//SNIPPET_END: strassen_complexity

// T(n) = 7T(n/2) for multiplications
// Solving: T(n) = 7^{log_2 n} = n^{log_2 7} ≈ n^{2.807}
// Master theorem: a=7, b=2, f(n)=0, so T(n) = Θ(n^{log_b a}) = Θ(n^{log_2 7})

// Lemma 1: For powers of 2, pow2(log2_floor(n)) equals n
let rec lemma_pow2_log2_inverse (n:pos{is_pow2 n})
  : Lemma (ensures pow2 (log2_floor n) == n)
          (decreases n)
  = if n = 1 then ()
    else begin
      lemma_pow2_half n;
      lemma_pow2_log2_inverse (n / 2);
      pow2_double_mult (log2_floor (n / 2))
    end

// Lemma 2: log2_floor relates to division by 2
let lemma_log2_half (n:pos{is_pow2 n /\ n > 1})
  : Lemma (ensures log2_floor n == 1 + log2_floor (n / 2))
  = ()

// Lemma 3: pow7 relates to multiplication by 7
let lemma_pow7_succ (k:nat)
  : Lemma (ensures pow7 (k + 1) == 7 * pow7 k)
  = ()

//SNIPPET_START: strassen_closed_form
// Prove the closed form
let rec lemma_strassen_mult_closed_form (n:pos{is_pow2 n})
  : Lemma (ensures (let k = log2_floor n in
                    strassen_mult_count n == pow7 k))
          (decreases n)
  = if n = 1 then ()
    else begin
      let half = n / 2 in
      lemma_pow2_half n;
      lemma_strassen_mult_closed_form half;
      lemma_log2_half n;
      lemma_pow7_succ (log2_floor half)
    end
//SNIPPET_END: strassen_closed_form
