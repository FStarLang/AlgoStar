(*
   Left-to-Right Modular Exponentiation — Pulse Implementation Interface

   Signature for the left-to-right (MSB → LSB) modular exponentiation
   (CLRS p. 957, Alg 31.6).

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExpLR.Impl

open Pulse.Lib.Pervasives
open FStar.Mul
open CLRS.Ch31.ModExp.Spec
open CLRS.Ch31.GCD.Complexity

module GR = Pulse.Lib.GhostReference

val mod_exp_lr_impl (b_init: int) (e_init: nat) (m_init: pos)
  (ctr: GR.ref nat) (#c0: erased nat)
  : stt int
    (GR.pts_to ctr c0)
    (fun result -> exists* (cf: nat). GR.pts_to ctr cf ** pure (
      result == mod_exp_spec b_init e_init m_init /\
      cf >= reveal c0 /\
      cf - reveal c0 <= num_bits e_init
    ))
