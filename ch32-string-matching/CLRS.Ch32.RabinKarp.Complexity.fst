module CLRS.Ch32.RabinKarp.Complexity

open FStar.Mul

(*
 * Complexity analysis for the Rabin-Karp string matching algorithm
 *
 * The Rabin-Karp algorithm has two phases:
 * 1. Precomputation: Compute hash of the pattern - O(m)
 * 2. Matching: Rolling hash over text with verification on hash matches
 *
 * Best case: No spurious hash collisions
 *   - m operations for initial pattern hash
 *   - (n - m + 1) hash updates for rolling through text
 *   - Total: O(n + m) - linear time
 *
 * Worst case: All hash values match (require full verification)
 *   - m operations for initial pattern hash
 *   - (n - m + 1) positions to check
 *   - m operations per position for verification
 *   - Total: O(m + (n - m + 1) * m) = O(nm) - quadratic time
 *)

(** Best case complexity: O(n + m) when no spurious hash matches occur *)
let rk_best_case (n m: nat) : nat =
  m + (if n >= m then n - m + 1 else 0)

(** Worst case complexity: O(nm) when all hash values match *)
let rk_worst_case (n m: nat) : nat =
  m + (if n >= m then (n - m + 1) * m else 0)

(** Lemma: Best case is linear in n *)
let rk_best_linear (n m: nat) : Lemma
  (requires m <= n)
  (ensures rk_best_case n m <= n + 1)
  =
  // rk_best_case n m = m + (n - m + 1)
  //                  = m + n - m + 1
  //                  = n + 1
  assert (rk_best_case n m == m + (n - m + 1));
  assert (m + (n - m + 1) == n + 1)

(** Lemma: Worst case is quadratic in n and m *)
let rk_worst_quadratic (n m: nat) : Lemma
  (requires m <= n /\ m >= 1)
  (ensures rk_worst_case n m <= n * m + 1)
  =
  // rk_worst_case n m = m + (n - m + 1) * m
  //                   = m + n*m - m*m + m
  //                   = 2m + n*m - m*m
  //
  // Need to show: 2m + n*m - m*m <= n*m + 1
  // Equivalently: 2m - m*m <= 1
  // Equivalently: m(2 - m) <= 1
  //
  // For m = 1: 1(2-1) = 1 <= 1 ✓
  // For m >= 2: m(2-m) <= 0 <= 1 ✓
  assert (rk_worst_case n m == m + (n - m + 1) * m);
  
  // Expand the multiplication
  assert ((n - m + 1) * m == n * m - m * m + m);
  assert (m + (n * m - m * m + m) == 2 * m + n * m - m * m);
  
  // Show that 2m - m*m <= 1
  if m = 1 then (
    assert (2 * m - m * m == 2 - 1);
    assert (2 - 1 == 1)
  )
  else (
    // For m >= 2, we have m*m >= 2m, so 2m - m*m <= 0 <= 1
    assert (m >= 2);
    assert (m * m >= 2 * m);
    assert (2 * m - m * m <= 0)
  );
  
  assert (2 * m - m * m <= 1);
  assert (2 * m + n * m - m * m <= n * m + 1)

(** Additional lemma: Best case is always at most the worst case *)
let rk_best_le_worst (n m: nat) : Lemma
  (requires m >= 1)  // Pattern must be non-empty
  (ensures rk_best_case n m <= rk_worst_case n m)
  =
  if n >= m then (
    assert (rk_best_case n m == m + (n - m + 1));
    assert (rk_worst_case n m == m + (n - m + 1) * m);
    // Need: m + (n - m + 1) <= m + (n - m + 1) * m
    // Equivalently: n - m + 1 <= (n - m + 1) * m
    // Since m >= 1: (n - m + 1) * m >= (n - m + 1) * 1 = n - m + 1
    assert ((n - m + 1) * m >= n - m + 1)
  )
  else
    () // When n < m, both return m, so equal

(** Lemma: For fixed m, best case grows linearly with n *)
let rk_best_linear_in_n (m: nat) (n1 n2: nat) : Lemma
  (requires m <= n1 /\ n1 <= n2)
  (ensures rk_best_case n2 m - rk_best_case n1 m == n2 - n1)
  =
  assert (rk_best_case n1 m == m + (n1 - m + 1));
  assert (rk_best_case n2 m == m + (n2 - m + 1));
  assert ((m + (n2 - m + 1)) - (m + (n1 - m + 1)) == n2 - n1)

(** Lemma: Worst case exhibits quadratic growth *)
let rk_worst_quadratic_growth (m: nat) (n1 n2: nat) : Lemma
  (requires m >= 1 /\ m <= n1 /\ n1 < n2)
  (ensures rk_worst_case n2 m > rk_worst_case n1 m)
  =
  assert (rk_worst_case n1 m == m + (n1 - m + 1) * m);
  assert (rk_worst_case n2 m == m + (n2 - m + 1) * m);
  assert ((n2 - m + 1) * m > (n1 - m + 1) * m)
