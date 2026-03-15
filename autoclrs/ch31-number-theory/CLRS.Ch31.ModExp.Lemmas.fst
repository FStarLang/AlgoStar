(*
   Modular Exponentiation — Lemmas Implementation

   Proves properties of pow and the modular exponentiation step lemma.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExp.Lemmas

open FStar.Mul
open FStar.Math.Lemmas
open CLRS.Ch31.ModExp.Spec

let rec pow_add (b: int) (e1 e2: nat)
  : Lemma (ensures pow b (e1 + e2) == pow b e1 * pow b e2)
          (decreases e1)
  = if e1 = 0 then ()
    else (pow_add b (e1 - 1) e2; assert (e1 - 1 + e2 == e1 + e2 - 1))

let rec pow_pow (b: int) (e1 e2: nat)
  : Lemma (ensures pow (pow b e1) e2 == pow b (e1 * e2))
          (decreases e2)
  = if e2 = 0 then ()
    else (pow_pow b e1 (e2 - 1);
          pow_add b e1 (e1 * (e2 - 1));
          assert (e1 + e1 * (e2 - 1) == e1 * e2))

let pow_square (b: int) (k: nat)
  : Lemma (pow (b * b) k == pow b (2 * k))
  = pow_pow b 2 k

let pow_even (b: int) (e: nat{e > 0 /\ e % 2 == 0})
  : Lemma (pow b e == pow (b * b) (e / 2))
  = pow_square b (e / 2)

let pow_odd (b: int) (e: nat{e > 0 /\ e % 2 == 1})
  : Lemma (pow b e == b * pow (b * b) (e / 2))
  = pow_square b (e / 2)

// pow (b%m) e % m == pow b e % m
let rec pow_mod_base (b: int) (e: nat) (m: pos)
  : Lemma (ensures pow (b % m) e % m == pow b e % m)
          (decreases e)
  = if e = 0 then ()
    else begin
      pow_mod_base b (e - 1) m;
      calc (==) {
        pow (b % m) e % m;
        == {}
        ((b % m) * pow (b % m) (e - 1)) % m;
        == { lemma_mod_mul_distr_r (b % m) (pow (b % m) (e - 1)) m }
        ((b % m) * (pow (b % m) (e - 1) % m)) % m;
        == { (* IH *) }
        ((b % m) * (pow b (e - 1) % m)) % m;
        == { lemma_mod_mul_distr_r (b % m) (pow b (e - 1)) m }
        ((b % m) * pow b (e - 1)) % m;
        == { lemma_mod_mul_distr_l b (pow b (e - 1)) m }
        (b * pow b (e - 1)) % m;
      }
    end

// Step lemmas
#push-options "--z3rlimit 20"
let mod_exp_step_even (vr vb: int) (ve: nat{ve > 0 /\ ve % 2 == 0}) (m: pos)
  : Lemma (let new_b = (vb * vb) % m in
           let new_e = ve / 2 in
           (vr * pow new_b new_e) % m == (vr * pow vb ve) % m)
  = pow_mod_base (vb * vb) (ve / 2) m;
    pow_even vb ve;
    lemma_mod_mul_distr_r vr (pow ((vb * vb) % m) (ve / 2)) m;
    lemma_mod_mul_distr_r vr (pow (vb * vb) (ve / 2)) m

let mod_exp_step_odd (vr vb: int) (ve: nat{ve > 0 /\ ve % 2 == 1}) (m: pos)
  : Lemma (let new_r = (vr * vb) % m in
           let new_b = (vb * vb) % m in
           let new_e = ve / 2 in
           (new_r * pow new_b new_e) % m == (vr * pow vb ve) % m)
  = pow_mod_base (vb * vb) (ve / 2) m;
    pow_odd vb ve;
    lemma_mod_mul_distr_l (vr * vb) (pow ((vb * vb) % m) (ve / 2)) m;
    lemma_mod_mul_distr_r (vr * vb) (pow ((vb * vb) % m) (ve / 2)) m;
    lemma_mod_mul_distr_r (vr * vb) (pow (vb * vb) (ve / 2)) m

//SNIPPET_START: mod_exp_step
let mod_exp_step (vr vb: int) (ve: nat) (m: pos)
  : Lemma (requires ve > 0)
          (ensures (let new_r = if ve % 2 = 1 then (vr * vb) % m else vr in
                    let new_b = (vb * vb) % m in
                    let new_e = ve / 2 in
                    (new_r * pow new_b new_e) % m == (vr * pow vb ve) % m))
  = if ve % 2 = 0 then mod_exp_step_even vr vb ve m
    else mod_exp_step_odd vr vb ve m
//SNIPPET_END: mod_exp_step
#pop-options

/// mod_exp_spec always returns a value in [0, m)
let mod_exp_spec_bounds (b: int) (e: nat) (m: pos)
  : Lemma (ensures mod_exp_spec b e m >= 0 /\ mod_exp_spec b e m < m)
  = FStar.Math.Lemmas.lemma_mod_lt (pow b e) m
