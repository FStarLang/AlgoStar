(*
   Maximum Subarray (Kadane's Algorithm) — Public interface
*)

module CLRS.Ch04.MaxSubarray.Kadane

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch04.MaxSubarray.Spec

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

val max_subarray
  (#p: perm)
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  : stt int
    (A.pts_to a #p s0 ** GR.pts_to ctr c0 **
     pure (
       SZ.v len == Seq.length s0 /\
       Seq.length s0 <= A.length a /\
       SZ.v len > 0
     ))
    (fun result -> exists* (cf: nat). A.pts_to a #p s0 ** GR.pts_to ctr cf ** pure (
       result == max_subarray_spec s0 /\
       complexity_bounded_linear cf (reveal c0) (SZ.v len)
     ))
