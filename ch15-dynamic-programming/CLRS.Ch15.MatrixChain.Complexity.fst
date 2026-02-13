module CLRS.Ch15.MatrixChain.Complexity

open FStar.Mul

(*
 * Complexity analysis for the matrix chain multiplication DP algorithm
 * 
 * The algorithm has three nested loops:
 * - Outer loop: l from 2 to n (chain length)
 * - Middle loop: i from 1 to n-l+1 (starting position)
 * - Inner loop: k from i to i+l-2 (split point, runs l-1 times)
 * 
 * Total iterations = Σ_{l=2}^{n} (n-l+1) * (l-1)
 * 
 * We prove this sum is O(n³), specifically ≤ n³ for n ≥ 1
 *)

(** 
 * Compute the sum Σ_{l=2}^{n} (n-l+1) * (l-1)
 * This counts the total number of innermost loop iterations
 *)
let rec mc_inner_sum (n: nat) (l: nat) : Tot nat (decreases (n + 1 - l)) =
  if l > n then 0
  else 
    let term = if l >= 1 && l <= n then (n - l + 1) * (l - 1) else 0 in
    term + mc_inner_sum n (l + 1)

let mc_iterations (n: nat) : nat =
  if n <= 1 then 0
  else mc_inner_sum n 2

(**
 * Key lemma: each term (n-l+1)(l-1) is bounded by n²
 * when 2 ≤ l ≤ n
 *)
let term_bound_lemma (n l: nat) : Lemma
  (requires 2 <= l /\ l <= n)
  (ensures (n - l + 1) * (l - 1) <= n * n)
  =
  // n - l + 1 <= n (since l >= 1)
  // l - 1 <= n - 1 < n (since l <= n)
  // Therefore (n-l+1)(l-1) <= n * n
  ()

(**
 * The sum from l to n contains at most (n - l + 1) terms
 *)
let rec mc_inner_sum_term_count (n l: nat) : Lemma
  (requires l <= n + 1)
  (ensures mc_inner_sum n l <= (n - l + 1) * (n * n))
  (decreases (n + 1 - l))
  =
  if l > n then ()
  else begin
    mc_inner_sum_term_count n (l + 1);
    if l >= 2 then term_bound_lemma n l
  end

(**
 * Main theorem: mc_iterations n ≤ n³
 *)
let mc_iterations_bound (n: nat) : Lemma
  (ensures mc_iterations n <= n * n * n)
  =
  if n <= 1 then ()
  else begin
    // mc_iterations n = mc_inner_sum n 2
    // The sum runs from l=2 to l=n, which is (n-1) terms
    // Each term is bounded by n²
    // Total ≤ (n-1) * n² < n³
    
    mc_inner_sum_term_count n 2;
    
    // Now we know: mc_inner_sum n 2 <= (n - 2 + 1) * (n * n) = (n - 1) * n²
    // We need to show (n - 1) * n² <= n³
    // This is equivalent to: n³ - n² <= n³, which is true
    
    assert ((n - 1) * (n * n) == n * n * n - n * n);
    assert (n * n * n - n * n <= n * n * n)
  end

(**
 * Alternative formulation: iterations are cubic in n
 *)
let mc_is_cubic (n: nat) : Lemma
  (ensures mc_iterations n <= n * n * n)
  =
  mc_iterations_bound n

(**
 * For non-trivial inputs (n >= 2), we do at least some work
 *)
let mc_iterations_positive (n: nat) : Lemma
  (requires n >= 2)
  (ensures mc_iterations n > 0)
  =
  // When n >= 2, l=2 contributes (n-1)*1 = n-1 >= 1 iterations
  assert (mc_iterations n == mc_inner_sum n 2);
  assert (mc_inner_sum n 2 == (n - 2 + 1) * (2 - 1) + mc_inner_sum n 3);
  assert ((n - 2 + 1) * (2 - 1) == n - 1);
  assert (n - 1 >= 1)

(**
 * The exact sum can be computed: Σ_{l=2}^{n} (n-l+1)(l-1) = (n³-n)/6
 * But our O(n³) bound is sufficient for complexity analysis
 *)
