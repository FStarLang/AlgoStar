module CLRS.Ch15.LCS.Impl
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

open CLRS.Ch15.LCS.Spec

let lcs_complexity_bounded (cf c0 m n: nat) : prop =
  cf >= c0 /\
  (m > 0 /\ n > 0 ==> cf - c0 == op_Star (m + 1) (n + 1)) /\
  (m = 0 \/ n = 0 ==> cf == c0)

open Pulse.Lib.BoundedIntegers

fn lcs
  (#px #py: perm)
  (x: A.array int)
  (y: A.array int)
  (m: SZ.t)
  (n: SZ.t)
  (#sx #sy: erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to x #px sx **
    A.pts_to y #py sy **
    GR.pts_to ctr c0 **
    pure (
      SZ.v m == Seq.length sx /\
      SZ.v m == A.length x /\
      SZ.v n == Seq.length sy /\
      SZ.v n == A.length y /\
      SZ.fits (op_Star (SZ.v m + 1) (SZ.v n + 1))
    )
  returns result: int
  ensures exists* (cf: nat).
    A.pts_to x #px sx **
    A.pts_to y #py sy **
    GR.pts_to ctr cf **
    pure (
      result == lcs_length sx sy (SZ.v m) (SZ.v n) /\
      result >= 0 /\
      result <= SZ.v m /\
      result <= SZ.v n /\
      lcs_complexity_bounded cf (reveal c0) (SZ.v m) (SZ.v n)
    )
