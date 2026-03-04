(*
   Insertion Sort - Public interface for the imperative implementation
*)
module CLRS.Ch02.InsertionSort.Impl

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open CLRS.Common.SortSpec
open CLRS.Ch02.InsertionSort.Spec

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

val insertion_sort
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  : stt unit
    (A.pts_to a s0 ** GR.pts_to ctr c0 **
     pure (
       SZ.v len == Seq.length s0 /\
       Seq.length s0 <= A.length a /\
       SZ.v len > 0))
    (fun _ -> exists* s (cf: nat). A.pts_to a s ** GR.pts_to ctr cf ** pure (
       Seq.length s == Seq.length s0 /\
       sorted s /\
       permutation s0 s /\
       complexity_bounded cf (reveal c0) (SZ.v len)))
