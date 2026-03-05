(*
   Modular Exponentiation — Complexity Implementation

   Proves the log2f helper lemmas.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExp.Complexity

open FStar.Mul

let lemma_log2f_halve (n: int)
  : Lemma (requires n > 1)
          (ensures log2f (Prims.op_Division n 2) + 1 == log2f n)
  = ()

let lemma_log2f_halve_le (n: int)
  : Lemma (requires n > 0)
          (ensures log2f (Prims.op_Division n 2) + 1 <= log2f n + 1)
  = if n > 1 then lemma_log2f_halve n
    else ()
