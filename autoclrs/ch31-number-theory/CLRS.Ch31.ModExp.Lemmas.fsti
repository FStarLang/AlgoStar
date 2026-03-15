(*
   Modular Exponentiation — Lemmas Interface

   Signatures for pow lemmas and the key modular exponentiation step lemma.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExp.Lemmas

open FStar.Mul
open CLRS.Ch31.ModExp.Spec

val pow_add (b: int) (e1 e2: nat)
  : Lemma (ensures pow b (e1 + e2) == pow b e1 * pow b e2)

val pow_pow (b: int) (e1 e2: nat)
  : Lemma (ensures pow (pow b e1) e2 == pow b (e1 * e2))

val pow_square (b: int) (k: nat)
  : Lemma (pow (b * b) k == pow b (2 * k))

val pow_even (b: int) (e: nat{e > 0 /\ e % 2 == 0})
  : Lemma (pow b e == pow (b * b) (e / 2))

val pow_odd (b: int) (e: nat{e > 0 /\ e % 2 == 1})
  : Lemma (pow b e == b * pow (b * b) (e / 2))

val pow_mod_base (b: int) (e: nat) (m: pos)
  : Lemma (ensures pow (b % m) e % m == pow b e % m)

val mod_exp_step (vr vb: int) (ve: nat) (m: pos)
  : Lemma (requires ve > 0)
          (ensures (let new_r = if ve % 2 = 1 then (vr * vb) % m else vr in
                    let new_b = (vb * vb) % m in
                    let new_e = ve / 2 in
                    (new_r * pow new_b new_e) % m == (vr * pow vb ve) % m))

/// mod_exp_spec always returns a value in [0, m)
val mod_exp_spec_bounds (b: int) (e: nat) (m: pos)
  : Lemma (ensures mod_exp_spec b e m >= 0 /\ mod_exp_spec b e m < m)
