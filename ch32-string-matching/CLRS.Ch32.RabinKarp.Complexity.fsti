(*
   Rabin-Karp String Matching — Complexity Interface (CLRS §32.2)
*)

module CLRS.Ch32.RabinKarp.Complexity

open FStar.Mul

(** Best case complexity: O(n + m) when no spurious hash matches occur *)
let rk_best_case (n m: nat) : nat =
  m + (if n >= m then n - m + 1 else 0)

(** Worst case complexity: O(nm) when all hash values match *)
let rk_worst_case (n m: nat) : nat =
  m + (if n >= m then (n - m + 1) * m else 0)

(** Lemma: Best case is linear in n *)
val rk_best_linear (n m: nat)
  : Lemma (requires m <= n)
          (ensures rk_best_case n m <= n + 1)

(** Lemma: Worst case is quadratic in n and m *)
val rk_worst_quadratic (n m: nat)
  : Lemma (requires m <= n /\ m >= 1)
          (ensures rk_worst_case n m <= n * m + 1)

(** Additional lemma: Best case is always at most the worst case *)
val rk_best_le_worst (n m: nat)
  : Lemma (requires m >= 1)
          (ensures rk_best_case n m <= rk_worst_case n m)

(** Lemma: For fixed m, best case grows linearly with n *)
val rk_best_linear_in_n (m: nat) (n1 n2: nat)
  : Lemma (requires m <= n1 /\ n1 <= n2)
          (ensures rk_best_case n2 m - rk_best_case n1 m == n2 - n1)

(** Lemma: Worst case exhibits quadratic growth *)
val rk_worst_quadratic_growth (m: nat) (n1 n2: nat)
  : Lemma (requires m >= 1 /\ m <= n1 /\ n1 < n2)
          (ensures rk_worst_case n2 m > rk_worst_case n1 m)
