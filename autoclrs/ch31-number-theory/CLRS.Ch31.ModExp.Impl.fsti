(*
   Modular Exponentiation (Right-to-Left) — Pulse Implementation Interface

   Signature for the right-to-left (LSB → MSB) modular exponentiation
   (CLRS Exercise 31.6-2).

   Uses machine-width SZ.t types for clean C extraction via KaRaMeL.
   Precondition requires m^2 fits in SZ.t to ensure intermediate
   products don't overflow.

   NO admits. NO assumes.
*)

module CLRS.Ch31.ModExp.Impl

open Pulse.Lib.Pervasives
open FStar.SizeT
open FStar.Mul
open CLRS.Ch31.ModExp.Spec
open CLRS.Ch31.ModExp.Complexity

module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT

val mod_exp_impl (b_init e_init: SZ.t) (m_init: SZ.t{SZ.v m_init > 0 /\ SZ.fits (SZ.v m_init * SZ.v m_init)})
  (ctr: GR.ref nat) (#c0: erased nat)
  : stt SZ.t
    (GR.pts_to ctr c0)
    (fun result -> exists* (cf: nat). GR.pts_to ctr cf ** pure (
      mod_exp_spec (SZ.v b_init) (SZ.v e_init) (SZ.v m_init) == SZ.v result /\
      SZ.v result >= 0 /\ SZ.v result < SZ.v m_init /\
      modexp_complexity_bounded cf (reveal c0) (SZ.v e_init)
    ))
