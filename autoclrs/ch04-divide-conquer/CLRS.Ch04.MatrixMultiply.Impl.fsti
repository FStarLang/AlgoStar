(*
   Matrix Multiply — Public interface for the imperative implementation
*)

module CLRS.Ch04.MatrixMultiply.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch04.MatrixMultiply.Spec

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

fn matrix_multiply
  (#pa #pb: perm)
  (a: array int)
  (b: array int)
  (c: array int)
  (#sa: Ghost.erased (Seq.seq int))
  (#sb: Ghost.erased (Seq.seq int))
  (#sc: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to a #pa sa **
    A.pts_to b #pb sb **
    A.pts_to c sc **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length sa == SZ.v n * SZ.v n /\
      Seq.length sb == SZ.v n * SZ.v n /\
      Seq.length sc == SZ.v n * SZ.v n
    )
  ensures exists* sc' (cf: nat).
    A.pts_to a #pa sa **
    A.pts_to b #pb sb **
    A.pts_to c sc' **
    GR.pts_to ctr cf **
    pure (
      mat_mul_correct sa sb sc' (SZ.v n) /\
      complexity_bounded_cubic cf (reveal c0) (SZ.v n)
    )
