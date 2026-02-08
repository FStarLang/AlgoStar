(*
   Radix Sort - Verified implementation in Pulse
   
   Implements CLRS radix sort for non-negative integers bounded by k.
   Uses counting sort (from CLRS.Ch08.CountingSort) as the stable
   subroutine for sorting by digit.
   
   For integers in [0, k], this is a single-digit radix sort:
   one pass of counting sort with base k+1.
   
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
