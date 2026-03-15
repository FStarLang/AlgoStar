module CLRS.Ch15.MatrixChain.Impl
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.Vec
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

open CLRS.Ch15.MatrixChain.Spec
open CLRS.Ch15.MatrixChain.Complexity

let mc_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == mc_iterations n

open Pulse.Lib.BoundedIntegers

fn matrix_chain_order
  (#p: perm)
  (dims: A.array int)
  (n: SZ.t)
  (#s_dims: erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to dims #p s_dims **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n + 1 == Seq.length s_dims /\
      SZ.v n + 1 == A.length dims /\
      SZ.v n > 0 /\
      SZ.fits (op_Multiply (SZ.v n) (SZ.v n)) /\
      (forall (i: nat). i < Seq.length s_dims ==> Seq.index s_dims i > 0)
    )
  returns result: int
  ensures exists* (cf: nat).
    A.pts_to dims #p s_dims **
    GR.pts_to ctr cf **
    pure (
      result == mc_result s_dims (SZ.v n) /\
      mc_complexity_bounded cf (reveal c0) (SZ.v n)
    )
