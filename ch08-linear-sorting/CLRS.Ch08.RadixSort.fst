(*
   Radix Sort - Verified implementation in Pulse
   
   CLRS RADIX-SORT (Section 8.3) for d-digit numbers sorts by digit
   using a stable sort subroutine:
   
     RADIX-SORT(A, d)
       for i = 1 to d
         use a stable sort to sort array A on digit i
   
   Current scope: Integers in [0, k] — single-digit (d=1) radix sort
   using counting_sort_inplace (in-place counting sort)
   as the subroutine.
   
   Proves:
   1. The result is sorted
   2. The result is a permutation of the input
   
   NO admits. NO assumes.
*)

module CLRS.Ch08.RadixSort
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Impl = CLRS.Ch08.CountingSort.Impl
module S = CLRS.Ch08.CountingSort.Spec

// ========== Main Algorithm ==========

//SNIPPET_START: radix_sort_sig
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
fn radix_sort
  (a: A.array nat)
  (len: SZ.t)
  (k_val: SZ.t)
  (#s0: erased (Seq.seq nat))
requires
  A.pts_to a s0 **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len == Seq.length s0 /\
    Seq.length s0 == A.length a /\
    S.in_range s0 (SZ.v k_val) /\
    SZ.v len > 0 /\
    SZ.fits (SZ.v k_val + 2) /\
    SZ.fits (SZ.v len + SZ.v k_val + 2)
  )
ensures exists* s.
  A.pts_to a s **
  pure (
    Seq.length s == Seq.length s0 /\
    S.sorted s /\
    S.permutation s0 s
  )
//SNIPPET_END: radix_sort_sig
{
  // d=1: one pass of in-place counting sort
  Impl.counting_sort_inplace a len k_val
}
#pop-options
