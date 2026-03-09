(*
   Counting Sort — Implementation Interface (CLRS §8.2)

   CLRS-faithful stable counting sort with separate input/output arrays.
   Postconditions guarantee the output is sorted and a permutation of the input.

   NO admits. NO assumes.
*)
module CLRS.Ch08.CountingSort.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S = CLRS.Ch08.CountingSort.Spec
module Stab = CLRS.Ch08.RadixSort.Stability

fn counting_sort_impl
  (a: A.array nat)     // Input array (read-only)
  (b: A.array nat)     // Output array (will be written)
  (len: SZ.t)          // Length of arrays
  (k_val: SZ.t)        // Maximum value in array
  (#sa: erased (Seq.seq nat))
  (#sb: erased (Seq.seq nat))
requires
  A.pts_to a #0.5R sa **
  A.pts_to b sb **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len <= A.length b /\
    SZ.v len == Seq.length sa /\
    SZ.v len == Seq.length sb /\
    Seq.length sa == A.length a /\
    Seq.length sb == A.length b /\
    S.in_range sa (SZ.v k_val) /\
    SZ.v len > 0 /\
    SZ.fits (SZ.v k_val + 2) /\
    SZ.fits (SZ.v len + SZ.v k_val + 2)
  )
ensures exists* sb'.
  A.pts_to a #0.5R sa **
  A.pts_to b sb' **
  pure (
    Seq.length sb' == Seq.length sa /\
    S.sorted sb' /\
    S.permutation sb' sa
  )

// In-place counting sort (simpler 2-phase variant used by RadixSort)
fn counting_sort_inplace
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

// Digit-keyed counting sort (for multi-digit radix sort)
fn counting_sort_by_digit
  (a: A.array nat)     // Input array (read-only)
  (b: A.array nat)     // Output array (will be written)
  (len: SZ.t)          // Length of arrays
  (base_val: SZ.t)     // Base for digit extraction
  (d: nat)             // Digit position
  (#sa: erased (Seq.seq nat))
  (#sb: erased (Seq.seq nat))
requires
  A.pts_to a #0.5R sa **
  A.pts_to b sb **
  pure (
    SZ.v len <= A.length a /\
    SZ.v len <= A.length b /\
    SZ.v len == Seq.length sa /\
    SZ.v len == Seq.length sb /\
    Seq.length sa == A.length a /\
    Seq.length sb == A.length b /\
    SZ.v base_val >= 2 /\
    SZ.v len > 0 /\
    SZ.fits (SZ.v base_val + 2) /\
    SZ.fits (SZ.v len + SZ.v base_val + 2)
  )
ensures exists* sb'.
  A.pts_to a #0.5R sa **
  A.pts_to b sb' **
  pure (
    Seq.length sb' == Seq.length sa /\
    Stab.is_stable_sort_on_digit sa sb' d (SZ.v base_val)
  )
