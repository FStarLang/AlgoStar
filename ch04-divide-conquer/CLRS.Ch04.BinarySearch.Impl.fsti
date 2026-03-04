(*
   Binary Search — Public interface for the imperative implementation
*)

module CLRS.Ch04.BinarySearch.Impl

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch04.BinarySearch.Spec

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

val binary_search
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (key: int)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  : stt SZ.t
    (A.pts_to a s0 ** GR.pts_to ctr c0 **
     pure (
       SZ.v len == Seq.length s0 /\
       Seq.length s0 <= A.length a /\
       SZ.v len > 0 /\
       is_sorted s0
     ))
    (fun result -> exists* (cf: nat). A.pts_to a s0 ** GR.pts_to ctr cf **
     pure (
       SZ.v result <= SZ.v len /\
       (SZ.v result < SZ.v len ==> (
         SZ.v result < Seq.length s0 /\
         Seq.index s0 (SZ.v result) == key
       )) /\
       (SZ.v result == SZ.v len ==> (
         forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i =!= key
       )) /\
       complexity_bounded_log cf (reveal c0) (SZ.v len)
     ))
