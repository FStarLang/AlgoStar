(*
   Modular Exponentiation (Right-to-Left) — Pulse Implementation

   Implements the right-to-left (LSB → MSB) variant of modular exponentiation
   (CLRS Exercise 31.6-2). Maintains a running result accumulator and a
   squaring base, processing bits from least to most significant.

   Uses machine-width SZ.t types for clean C extraction via KaRaMeL.
   Precondition requires m^2 fits in SZ.t to ensure intermediate
   products don't overflow.

   Functional correctness: result == mod_exp_spec b e m == pow b e % m
   Complexity bound: at most ⌊log₂(e)⌋ + 1 squarings for exponent e.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExp.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open FStar.Math.Lemmas
open CLRS.Ch31.ModExp.Spec
open CLRS.Ch31.ModExp.Lemmas
open CLRS.Ch31.ModExp.Complexity
open CLRS.Common.Complexity

module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT

#push-options "--z3rlimit 10"
//SNIPPET_START: mod_exp_impl_sig
fn mod_exp_impl (b_init e_init: SZ.t) (m_init: SZ.t{SZ.v m_init > 0 /\ SZ.fits (SZ.v m_init * SZ.v m_init)})
  (ctr: GR.ref nat) (#c0: erased nat)
  requires GR.pts_to ctr c0
  returns result: SZ.t
  ensures exists* (cf: nat). GR.pts_to ctr cf ** pure (
    mod_exp_spec (SZ.v b_init) (SZ.v e_init) (SZ.v m_init) == SZ.v result /\
    SZ.v result >= 0 /\ SZ.v result < SZ.v m_init /\
    modexp_complexity_bounded cf (reveal c0) (SZ.v e_init)
  )
//SNIPPET_END: mod_exp_impl_sig
{
  pow_mod_base (SZ.v b_init) (SZ.v e_init) (SZ.v m_init);
  lemma_mod_mul_distr_l 1 (pow (SZ.v b_init % SZ.v m_init) (SZ.v e_init)) (SZ.v m_init);

  let mut result: SZ.t = 1sz %^ m_init;
  let mut base: SZ.t = b_init %^ m_init;
  let mut exp: SZ.t = e_init;

//SNIPPET_START: mod_exp_loop
  while (
    let ve = !exp;
    ve >^ 0sz
  )
  invariant exists* vr vb ve (vc : nat).
    R.pts_to result vr **
    R.pts_to base vb **
    R.pts_to exp ve **
    GR.pts_to ctr vc **
    pure (
      SZ.v ve <= SZ.v e_init /\
      SZ.v vr >= 0 /\ SZ.v vr < SZ.v m_init /\
      SZ.v vb >= 0 /\ SZ.v vb < SZ.v m_init /\
      (SZ.v vr * pow (SZ.v vb) (SZ.v ve)) % SZ.v m_init == mod_exp_spec (SZ.v b_init) (SZ.v e_init) (SZ.v m_init) /\
      vc >= reveal c0 /\
      vc - reveal c0 <= log2f (SZ.v e_init) + 1 /\
      (SZ.v ve > 0 ==> (vc - reveal c0) + log2f (SZ.v ve) <= log2f (SZ.v e_init))
    )
  decreases (SZ.v !exp)
  {
    let ve = !exp;
    let vr = !result;
    let vb = !base;

    mod_exp_step (SZ.v vr) (SZ.v vb) (SZ.v ve) (SZ.v m_init);
    tick ctr;
    lemma_log2f_halve_le (SZ.v ve);

    // Prove multiplication fits in SZ.t
    assert (pure (SZ.v vr * SZ.v vb <= SZ.v vr * SZ.v m_init));
    assert (pure (SZ.v vr * SZ.v m_init < SZ.v m_init * SZ.v m_init));

    if (ve %^ 2sz =^ 1sz) {
      result := (vr *^ vb) %^ m_init;
    } else {
      result := vr;
    };

    let vb2 = !base;
    // Prove squaring fits in SZ.t
    assert (pure (SZ.v vb2 * SZ.v vb2 <= SZ.v vb2 * SZ.v m_init));
    assert (pure (SZ.v vb2 * SZ.v m_init < SZ.v m_init * SZ.v m_init));
    base := (vb2 *^ vb2) %^ m_init;

    let ve2 = !exp;
    exp := ve2 /^ 2sz;
  };
//SNIPPET_END: mod_exp_loop

  let r = !result;
  // After loop: ve == 0, so pow vb 0 == 1 and (vr * 1) % m == vr
  assert (pure (mod_exp_spec (SZ.v b_init) (SZ.v e_init) (SZ.v m_init) == SZ.v r));
  r
}
#pop-options
