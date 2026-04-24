(*
   Extended Euclidean Algorithm — Pulse Implementation Interface

   Signature for the imperative extended GCD implementation with ghost
   tick counting.  The concrete return is d = gcd(a, b) in machine-width
   SZ.t; Bézout coefficients x, y are proven to exist via the
   postcondition (they match the pure spec extended_gcd).

   NO admits. NO assumes.
*)

module CLRS.Ch31.ExtendedGCD.Impl

open Pulse.Lib.Pervasives
open FStar.SizeT
open FStar.Math.Euclid
open CLRS.Ch31.GCD.Spec
open CLRS.Ch31.GCD.Complexity
open CLRS.Ch31.ExtendedGCD.Spec

module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT

val extended_gcd_impl (a_init b_init: SZ.t)
  (ctr: GR.ref nat) (#c0: erased nat)
  : stt SZ.t
    (GR.pts_to ctr c0 ** pure (SZ.v a_init > 0 \/ SZ.v b_init > 0))
    (fun result -> exists* (cf: nat). GR.pts_to ctr cf ** pure (
      let (| d, x, y |) = extended_gcd (SZ.v a_init) (SZ.v b_init) in
      SZ.v result == d /\
      SZ.v result > 0 /\
      SZ.v a_init * x + SZ.v b_init * y == SZ.v result /\
      divides (SZ.v result) (SZ.v a_init) /\
      divides (SZ.v result) (SZ.v b_init) /\
      cf >= reveal c0 /\
      cf - reveal c0 == gcd_steps (SZ.v a_init) (SZ.v b_init)
    ))
