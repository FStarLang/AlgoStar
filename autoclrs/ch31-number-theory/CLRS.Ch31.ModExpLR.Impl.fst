(*
   Left-to-Right Modular Exponentiation — Pulse Implementation

   Implements the primary MODULAR-EXPONENTIATION from CLRS p. 957,
   scanning bits from MSB to LSB (left-to-right).

   The algorithm maintains d = a^c mod n where c is the prefix of the binary
   representation of b processed so far. At each step, we square d (doubling c)
   and optionally multiply by a (incrementing c by 1 if the current bit is 1).

   Functional correctness: result == mod_exp_spec b e m == pow b e % m
   Complexity bound: at most num_bits(e) squarings.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExpLR.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open FStar.Mul
open FStar.Math.Lemmas
open CLRS.Ch31.ModExp.Spec
open CLRS.Ch31.ModExpLR.Lemmas
open CLRS.Ch31.GCD.Complexity
open CLRS.Ch31.ModExpLR.Complexity
open CLRS.Common.Complexity

module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 30"
fn mod_exp_lr_impl (b_init: int) (e_init: nat) (m_init: pos)
  (ctr: GR.ref nat) (#c0: erased nat)
  requires GR.pts_to ctr c0
  returns result: int
  ensures exists* (cf: nat). GR.pts_to ctr cf ** pure (
    result == mod_exp_spec b_init e_init m_init /\
    result >= 0 /\ result < m_init /\
    modexp_lr_complexity_bounded cf (reveal c0) e_init
  )
{
  lemma_prefix_zero e_init;

  let mut d : int = 1 % m_init;
  let mut i : int = num_bits e_init - 1;

  while (
    let vi = !i;
    vi >= 0
  )
  invariant exists* (vd: int) (vi_val: int) (vc: nat).
    R.pts_to d vd **
    R.pts_to i vi_val **
    GR.pts_to ctr vc **
    pure (
      vi_val >= -1 /\
      vi_val + 1 <= num_bits e_init /\
      vd >= 0 /\ vd < m_init /\
      vd == pow b_init (e_init / pow2 (vi_val + 1)) % m_init /\
      vc >= reveal c0 /\
      vc - reveal c0 + (vi_val + 1) == num_bits e_init
    )
  decreases (!i + 1)
  {
    let vi = !i;
    let vd = !d;

    lemma_bit_decompose e_init vi;
    mod_exp_lr_step b_init (e_init / pow2 (vi + 1)) m_init ((e_init / pow2 vi) % 2);

    if ((e_init / pow2 vi) % 2 = 1) {
      d := ((vd * vd) % m_init * b_init) % m_init;
    } else {
      d := (vd * vd) % m_init;
    };

    tick ctr;
    i := vi - 1;
  };

  !d
}
#pop-options
