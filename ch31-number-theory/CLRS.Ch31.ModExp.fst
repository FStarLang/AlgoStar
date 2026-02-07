(*
   Modular Exponentiation - Verified implementation in Pulse

   Implements MODULAR-EXPONENTIATION from CLRS Chapter 31 using repeated squaring.
   Functional correctness: result == mod_exp_spec b e m == pow b e % m

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExp
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open FStar.Mul
open FStar.Math.Lemmas

module R = Pulse.Lib.Reference

// ========== Pure Specification ==========

let rec pow (b: int) (e: nat) : Tot int (decreases e) =
  if e = 0 then 1
  else b * pow b (e - 1)

let mod_exp_spec (b: int) (e: nat) (m: pos) : int = pow b e % m

// ========== Lemmas about pow ==========

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

// ========== pow (b%m) e % m == pow b e % m ==========

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

// ========== Step lemma ==========

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
    // pow vb ve == vb * pow (vb*vb) (ve/2)
    // so vr * pow vb ve == vr * vb * pow(vb*vb)(ve/2)
    // LHS: ((vr*vb)%m * pow((vb*vb)%m)(ve/2)) % m
    //    = ((vr*vb) * pow((vb*vb)%m)(ve/2)) % m        [mod_mul_distr_l]
    //    = ((vr*vb) * (pow((vb*vb)%m)(ve/2) % m)) % m  [mod_mul_distr_r]  -- not needed
    //    Need to connect pow((vb*vb)%m)(ve/2) with pow(vb*vb)(ve/2)
    // Actually: (a%m * b) % m = (a * b) % m
    lemma_mod_mul_distr_l (vr * vb) (pow ((vb * vb) % m) (ve / 2)) m;
    // = (vr * vb * pow((vb*vb)%m)(ve/2)) % m
    lemma_mod_mul_distr_r (vr * vb) (pow ((vb * vb) % m) (ve / 2)) m;
    // = (vr * vb * (pow((vb*vb)%m)(ve/2) % m)) % m
    // By pow_mod_base: pow((vb*vb)%m)(ve/2) % m == pow(vb*vb)(ve/2) % m
    lemma_mod_mul_distr_r (vr * vb) (pow (vb * vb) (ve / 2)) m
    // = (vr * vb * pow(vb*vb)(ve/2)) % m
    // = (vr * (vb * pow(vb*vb)(ve/2))) % m  [by assoc, which Z3 knows]
    // = (vr * pow vb ve) % m                [by pow_odd]
#pop-options

let mod_exp_step (vr vb: int) (ve: nat) (m: pos)
  : Lemma (requires ve > 0)
          (ensures (let new_r = if ve % 2 = 1 then (vr * vb) % m else vr in
                    let new_b = (vb * vb) % m in
                    let new_e = ve / 2 in
                    (new_r * pow new_b new_e) % m == (vr * pow vb ve) % m))
  = if ve % 2 = 0 then mod_exp_step_even vr vb ve m
    else mod_exp_step_odd vr vb ve m

// ========== Pulse Implementation ==========

#push-options "--z3rlimit 20"
fn mod_exp_impl (b_init: int) (e_init: nat) (m_init: pos)
  requires emp ** pure (m_init > 1)
  returns result: int
  ensures emp ** pure (result == mod_exp_spec b_init e_init m_init)
{
  pow_mod_base b_init e_init m_init;
  
  let mut result: int = 1;
  let mut base: int = b_init % m_init;
  let mut exp: int = e_init;
  
  while (
    let ve = !exp;
    ve > 0
  )
  invariant exists* vr vb ve.
    R.pts_to result vr **
    R.pts_to base vb **
    R.pts_to exp ve **
    pure (
      ve >= 0 /\ ve <= e_init /\
      vr >= 0 /\ vr < m_init /\
      vb >= 0 /\ vb < m_init /\
      (vr * pow vb ve) % m_init == mod_exp_spec b_init e_init m_init
    )
  {
    let ve = !exp;
    let vr = !result;
    let vb = !base;
    
    mod_exp_step vr vb ve m_init;
    
    if (ve % 2 = 1) {
      result := (vr * vb) % m_init;
    } else {
      result := vr;
    };
    
    let vb2 = !base;
    base := (vb2 * vb2) % m_init;
    
    let ve2 = !exp;
    exp := ve2 / 2;
  };
  
  !result
}
#pop-options
