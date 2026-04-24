(*
   CLRS Chapter 9: Partial Selection Sort — Implementation Interface
*)
module CLRS.Ch09.PartialSelectionSort.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module GR = Pulse.Lib.GhostReference
module PSSSpec = CLRS.Ch09.PartialSelectionSort.Spec

[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)

let is_min_in_range (s: Seq.seq int) (i: nat) (start: nat) (len: nat) : prop =
  start <= i /\ i < len /\ len <= Seq.length s /\
  (forall (j: nat). start <= j /\ j < len ==> Seq.index s i <= Seq.index s j)

let sorted_prefix (s: Seq.seq int) (bound: nat) : prop =
  bound <= Seq.length s /\
  (forall (i j: nat). i < j /\ j < bound ==> Seq.index s i <= Seq.index s j)

let prefix_leq_suffix (s: Seq.seq int) (bound: nat) : prop =
  bound <= Seq.length s /\
  (forall (i j: nat). i < bound /\ bound <= j /\ j < Seq.length s ==>
    Seq.index s i <= Seq.index s j)

fn find_min_index_from
  (#p: perm)
  (a: array int)
  (#s: Ghost.erased (Seq.seq int))
  (start: SZ.t)
  (len: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a #p s ** GR.pts_to ctr c0 **
    pure (
      SZ.v start < SZ.v len /\
      SZ.v len == Seq.length s /\
      SZ.v len == A.length a
    )
  returns min_idx: SZ.t
  ensures exists* (cf: nat).
    A.pts_to a #p s ** GR.pts_to ctr cf **
    pure (
      SZ.v start <= SZ.v min_idx /\
      SZ.v min_idx < SZ.v len /\
      is_min_in_range s (SZ.v min_idx) (SZ.v start) (SZ.v len) /\
      cf >= reveal c0 /\
      cf - reveal c0 == SZ.v len - SZ.v start - 1
    )

/// Selection complexity: at most k × (n−1) comparisons.
/// k rounds, each scanning up to n−1 elements. This is O(nk) worst case.
let complexity_bounded_select (cf c0 n k: nat) : prop =
  k > 0 /\ k <= n /\ n > 0 /\
  cf >= c0 /\
  cf - c0 <= op_Star k (n - 1)

fn select
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (k: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires A.pts_to a s0 ** GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s0 /\
      SZ.v n == A.length a /\
      SZ.v n > 0 /\
      SZ.v k > 0 /\
      SZ.v k <= SZ.v n
    )
  returns result: int
  ensures exists* s_final (cf: nat).
    A.pts_to a s_final ** GR.pts_to ctr cf **
    pure (
      Seq.length s_final == Seq.length s0 /\
      permutation s0 s_final /\
      sorted_prefix s_final (SZ.v k) /\
      prefix_leq_suffix s_final (SZ.v k) /\
      SZ.v k > 0 /\
      result == Seq.index s_final (SZ.v k `Prims.op_Subtraction` 1) /\
      result == PSSSpec.select_spec s0 (SZ.v k `Prims.op_Subtraction` 1) /\
      complexity_bounded_select cf (reveal c0) (SZ.v n) (SZ.v k)
    )
