(*
   Modular Exponentiation (Right-to-Left) — Pulse Implementation Interface

   Signature for the right-to-left (LSB → MSB) modular exponentiation
   (CLRS Exercise 31.6-2).

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExp.Impl

open Pulse.Lib.Pervasives
open FStar.Mul
open CLRS.Ch31.ModExp.Spec
open CLRS.Ch31.ModExp.Complexity

module GR = Pulse.Lib.GhostReference

val mod_exp_impl (b_init: int) (e_init: nat) (m_init: pos)
  (ctr: GR.ref nat) (#c0: erased nat)
  : stt int
    (GR.pts_to ctr c0)
    (fun result -> exists* (cf: nat). GR.pts_to ctr cf ** pure (
      result == mod_exp_spec b_init e_init m_init /\
      modexp_complexity_bounded cf (reveal c0) e_init
    ))
