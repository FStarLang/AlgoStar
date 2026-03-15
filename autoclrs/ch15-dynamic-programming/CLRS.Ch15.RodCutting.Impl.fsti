module CLRS.Ch15.RodCutting.Impl
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.Vec
open FStar.SizeT

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

open CLRS.Ch15.RodCutting.Spec

let triangle (n: nat) : nat = op_Multiply n (Prims.op_Addition n 1) / 2

let rod_cutting_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == triangle n

open Pulse.Lib.BoundedIntegers

fn rod_cutting
  (#p: perm)
  (prices: A.array nat)
  (n: SZ.t)
  (#s_prices: erased (Seq.seq nat))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to prices #p s_prices **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s_prices /\
      SZ.v n == A.length prices /\
      SZ.fits (SZ.v n + 1)
    )
  returns result: nat
  ensures exists* (cf: nat).
    A.pts_to prices #p s_prices **
    GR.pts_to ctr cf **
    pure (
      result == optimal_revenue s_prices (SZ.v n) /\
      rod_cutting_bounded cf (reveal c0) (SZ.v n)
    )
