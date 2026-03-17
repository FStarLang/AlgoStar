(*
   GCD Pulse Implementation — Interface

   Signature for the imperative GCD implementation with ghost tick counting.

   NO admits. NO assumes.
*)

module CLRS.Ch31.GCD.Impl

open Pulse.Lib.Pervasives
open FStar.SizeT
open FStar.Mul
open FStar.Math.Euclid
open CLRS.Ch31.GCD.Spec
open CLRS.Ch31.GCD.Complexity

module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT

val gcd_impl (a_init b_init: SZ.t)
  (ctr: GR.ref nat) (#c0: erased nat)
  : stt SZ.t
    (GR.pts_to ctr c0 ** pure (SZ.v a_init > 0 \/ SZ.v b_init > 0))
    (fun result -> exists* (cf: nat). GR.pts_to ctr cf ** pure (
      SZ.v result == gcd_spec (SZ.v a_init) (SZ.v b_init) /\
      SZ.v result > 0 /\
      divides (SZ.v result) (SZ.v a_init) /\
      divides (SZ.v result) (SZ.v b_init) /\
      cf >= reveal c0 /\
      cf - reveal c0 == gcd_steps (SZ.v a_init) (SZ.v b_init) /\
      (SZ.v b_init > 0 ==> cf - reveal c0 <= op_Multiply 2 (num_bits (SZ.v b_init)) + 1)
    ))
