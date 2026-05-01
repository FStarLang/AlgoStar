(*
   Modular Exponentiation — Complexity Interface

   Transparent definitions for log2f and complexity bound, plus lemma signatures.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExp.Complexity


// log2 for complexity bound (floor of log base 2, transparent for unfolding)
let rec log2f (n: int) : Tot nat (decreases (if n > 0 then n else 0)) =
  if n <= 1 then 0
  else 1 + log2f (n / 2)

//SNIPPET_START: modexp_complexity_bounded
// Complexity bound predicate (transparent)
let modexp_complexity_bounded (cf c0: nat) (e_init: nat) : prop =
  cf >= c0 /\ cf - c0 <= log2f e_init + 1
//SNIPPET_END: modexp_complexity_bounded

val lemma_log2f_halve (n: int)
  : Lemma (requires n > 1)
          (ensures log2f (n / 2) + 1 == log2f n)

val lemma_log2f_halve_le (n: int)
  : Lemma (requires n > 0)
          (ensures log2f (n / 2) + 1 <= log2f n + 1)
