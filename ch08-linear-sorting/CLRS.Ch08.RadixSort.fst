(*
   Radix Sort - Verified implementation in Pulse
   
   CLRS RADIX-SORT (Section 8.3) for d-digit numbers sorts by digit
   using a stable sort subroutine:
   
     RADIX-SORT(A, d)
       for i = 1 to d
         use a stable sort to sort array A on digit i
   
   Current scope: Integers in [0, k] — single-digit (d=1) radix sort
   with counting sort as the stable subroutine.
   
   Limitation: A multi-digit version (d > 1) would require:
   - Digit extraction: digit_i(x) = (x / base^i) mod base
   - Stability proof for counting sort (currently proven as permutation)
   - Inductive argument: after i passes, elements are sorted on low i digits
   
   The d=1 case is correct but does not exercise the multi-pass structure.
   
   Proves:
   1. The result is sorted
   2. The result is a permutation of the input
   
   NO admits. NO assumes.
*)

module CLRS.Ch08.RadixSort
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module CS = CLRS.Ch08.CountingSort
module L = CLRS.Ch08.CountingSort.Lemmas

// ========== Main Algorithm ==========

// Radix sort for non-negative integers bounded by k.
// Uses counting sort as the stable sorting subroutine.
// For integers in [0, k], this reduces to a single pass of counting sort.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
fn radix_sort
  (a: A.array int)
  (len: SZ.t)
  (k_val: SZ.t)
  (#s0: erased (Seq.seq int))
requires
  A.pts_to a s0 **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len == Seq.length s0 /\
    Seq.length s0 == A.length a /\
    L.in_range s0 (SZ.v k_val) /\
    SZ.v len > 0 /\
    SZ.fits (SZ.v k_val + 2) /\
    SZ.fits (SZ.v len + SZ.v k_val + 2)
  )
ensures exists* s.
  A.pts_to a s **
  pure (
    Seq.length s == Seq.length s0 /\
    L.sorted s /\
    L.permutation s0 s
  )
{
  // For integers bounded by k, radix sort with base k+1 is a single
  // pass of counting sort. This is the CLRS radix sort specialization
  // where d=1 (one digit in base k+1).
  CS.counting_sort a len k_val
}
#pop-options
