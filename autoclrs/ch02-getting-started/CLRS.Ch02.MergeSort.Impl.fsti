(*
   Merge Sort - Public interface for the imperative implementation
*)
module CLRS.Ch02.MergeSort.Impl

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Array.PtsToRange
open CLRS.Common.SortSpec
open CLRS.Ch02.MergeSort.Spec

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

val merge
  (a: array int) (lo mid hi: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  (#s1 #s2: Ghost.erased (Seq.seq int))
  : stt unit
    (pts_to_range a (SZ.v lo) (SZ.v mid) s1 **
     pts_to_range a (SZ.v mid) (SZ.v hi) s2 **
     GR.pts_to ctr c0 **
     pure (SZ.v lo <= SZ.v mid /\ SZ.v mid <= SZ.v hi /\ sorted s1 /\ sorted s2))
    (fun _ -> exists* s_out (cf: nat).
       pts_to_range a (SZ.v lo) (SZ.v hi) s_out **
       GR.pts_to ctr cf **
       pure (
         sorted s_out /\ 
         permutation (Seq.append s1 s2) s_out /\
         merge_complexity_bounded cf (reveal c0) (SZ.v lo) (SZ.v hi)))

val merge_sort
  (a: A.array int)
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  (#s0: erased (Seq.seq int))
  : stt unit
    (A.pts_to a s0 **
     GR.pts_to ctr c0 **
     pure (
       SZ.v len == Seq.length s0 /\ 
       Seq.length s0 <= A.length a))
    (fun _ -> exists* s (cf: nat).
       A.pts_to a s **
       GR.pts_to ctr cf **
       pure (
         Seq.length s == Seq.length s0 /\
         sorted s /\
         permutation s0 s /\
         sort_complexity_bounded cf (reveal c0) 0 (SZ.v len)))
