(*
   Modular Exponentiation (Right-to-Left) — Pulse Implementation

   Implements the right-to-left (LSB → MSB) variant of modular exponentiation
   (CLRS Exercise 31.6-2). Maintains a running result accumulator and a
   squaring base, processing bits from least to most significant.

   Functional correctness: result == mod_exp_spec b e m == pow b e % m
   Complexity bound: at most ⌊log₂(e)⌋ + 1 squarings for exponent e.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExp.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open FStar.Mul
open FStar.Math.Lemmas
open CLRS.Ch31.ModExp.Spec
open CLRS.Ch31.ModExp.Lemmas
open CLRS.Ch31.ModExp.Complexity
open CLRS.Common.Complexity

module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 30"
//SNIPPET_START: mod_exp_impl_sig
fn mod_exp_impl (b_init: int) (e_init: nat) (m_init: pos)
  (ctr: GR.ref nat) (#c0: erased nat)
  requires GR.pts_to ctr c0
  returns result: int
  ensures exists* (cf: nat). GR.pts_to ctr cf ** pure (
    result == mod_exp_spec b_init e_init m_init /\
    modexp_complexity_bounded cf (reveal c0) e_init
  )
//SNIPPET_END: mod_exp_impl_sig
{
  pow_mod_base b_init e_init m_init;
  lemma_mod_mul_distr_l 1 (pow (b_init % m_init) e_init) m_init;

  let mut result: int = 1 % m_init;
  let mut base: int = b_init % m_init;
  let mut exp: int = e_init;

//SNIPPET_START: mod_exp_loop
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
      vc >= reveal c0 /\
      vc - reveal c0 <= log2f e_init + 1 /\
      (ve > 0 ==> (vc - reveal c0) + log2f ve <= log2f e_init)
    )
  decreases (!exp)
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
//SNIPPET_END: mod_exp_loop

  !result
}
#pop-options
