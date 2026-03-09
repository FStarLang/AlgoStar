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
module SZ = FStar.SizeT
module Seq = FStar.Seq

open CLRS.Ch15.MatrixChain.Spec

open Pulse.Lib.BoundedIntegers

fn matrix_chain_order
  (#p: perm)
  (dims: A.array int)
  (n: SZ.t)
  (#s_dims: erased (Seq.seq int))
  requires
    A.pts_to dims #p s_dims **
    pure (
      SZ.v n + 1 == Seq.length s_dims /\
      SZ.v n + 1 == A.length dims /\
      SZ.v n > 0 /\
      SZ.fits (op_Multiply (SZ.v n) (SZ.v n)) /\
      (forall (i: nat). i < Seq.length s_dims ==> Seq.index s_dims i > 0)
    )
  returns result: int
  ensures
    A.pts_to dims #p s_dims **
    pure (
      result == mc_result s_dims (SZ.v n)
    )
