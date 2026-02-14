(*
   Modular Exponentiation with Complexity Bound

   Proves O(log e) complexity for modular exponentiation (repeated squaring).
   Specifically: at most ⌊log₂(e)⌋ + 1 squarings for exponent e.

   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   Each squaring step (halving of exponent) gets one ghost tick.

   Also proves functional correctness (result == mod_exp_spec b e m).

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExp.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open FStar.Mul
open FStar.Math.Lemmas

module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference

// ========== Ghost tick ==========

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// ========== Pure Specification (same as ModExp.fst) ==========

let rec pow (b: int) (e: nat) : Tot int (decreases e) =
  if e = 0 then 1
  else b * pow b (e - 1)

let mod_exp_spec (b: int) (e: nat) (m: pos) : int = pow b e % m

// ========== Lemmas about pow (same as ModExp.fst) ==========

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

let mod_exp_step (vr vb: int) (ve: nat) (m: pos)
  : Lemma (requires ve > 0)
          (ensures (let new_r = if ve % 2 = 1 then (vr * vb) % m else vr in
                    let new_b = (vb * vb) % m in
                    let new_e = ve / 2 in
                    (new_r * pow new_b new_e) % m == (vr * pow vb ve) % m))
  = if ve % 2 = 0 then mod_exp_step_even vr vb ve m
    else mod_exp_step_odd vr vb ve m
#pop-options

// ========== log2f for complexity bound ==========

let rec log2f (n: int) : Tot nat (decreases (if n > 0 then n else 0)) =
  if Prims.op_LessThanOrEqual n 1 then 0
  else Prims.op_Addition 1 (log2f (Prims.op_Division n 2))

// Key property: log2f(n/2) + 1 == log2f(n) when n > 1
let lemma_log2f_halve (n: int)
  : Lemma (requires n > 1)
          (ensures log2f (Prims.op_Division n 2) + 1 == log2f n)
  = ()

// When n > 0: log2f(n/2) <= log2f(n) (handles n==1 case where n/2==0)
let lemma_log2f_halve_le (n: int)
  : Lemma (requires n > 0)
          (ensures log2f (Prims.op_Division n 2) + 1 <= log2f n + 1)
  = if n > 1 then lemma_log2f_halve n
    else ()

// ========== Complexity bound predicate ==========
let modexp_complexity_bounded (cf c0: nat) (e_init: nat) : prop =
  cf >= c0 /\ cf - c0 <= log2f e_init + 1

// ========== Pulse Implementation with Complexity ==========

#push-options "--z3rlimit 20"
fn mod_exp_complexity (b_init: int) (e_init: nat) (m_init: pos)
  (ctr: GR.ref nat) (#c0: erased nat)
  requires GR.pts_to ctr c0 ** pure (m_init > 1 /\ e_init > 0)
  returns result: int
  ensures exists* (cf: nat). GR.pts_to ctr cf ** pure (
    result == mod_exp_spec b_init e_init m_init /\
    modexp_complexity_bounded cf (reveal c0) e_init
  )
{
  pow_mod_base b_init e_init m_init;

  let mut result: int = 1;
  let mut base: int = b_init % m_init;
  let mut exp: int = e_init;

  while (
    let ve = !exp;
    ve > 0
  )
  invariant exists* vr vb ve (vc : nat).
    R.pts_to result vr **
    R.pts_to base vb **
    R.pts_to exp ve **
    GR.pts_to ctr vc **
    pure (
      ve >= 0 /\ ve <= e_init /\
      vr >= 0 /\ vr < m_init /\
      vb >= 0 /\ vb < m_init /\
      (vr * pow vb ve) % m_init == mod_exp_spec b_init e_init m_init /\
      // Complexity: overall bound (relative to c0)
      vc >= reveal c0 /\
      vc - reveal c0 <= log2f e_init + 1 /\
      (ve > 0 ==> (vc - reveal c0) + log2f ve <= log2f e_init)
    )
  {
    let ve = !exp;
    let vr = !result;
    let vb = !base;

    mod_exp_step vr vb ve m_init;
    tick ctr;
    lemma_log2f_halve_le ve;

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
