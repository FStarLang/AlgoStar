(*
   CLRS Chapter 9: Partial Selection Sort — Pulse Implementation Interface

   Public API for partial selection sort operations.
*)
module CLRS.Ch09.PartialSelectionSort.Impl
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
module GR = Pulse.Lib.GhostReference

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
  requires A.pts_to a #p s
  requires pure (
    SZ.v start < SZ.v len /\
    SZ.v len == Seq.length s /\
    SZ.v len == A.length a
  )
  returns min_idx: SZ.t
  ensures A.pts_to a #p s ** pure (
    SZ.v start <= SZ.v min_idx /\
    SZ.v min_idx < SZ.v len /\
    is_min_in_range s (SZ.v min_idx) (SZ.v start) (SZ.v len)
  )

fn select
  (a: array int)
  (#s0: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (k: SZ.t)
  requires A.pts_to a s0
  requires pure (
    SZ.v n == Seq.length s0 /\
    SZ.v n == A.length a /\
    SZ.v n > 0 /\
    SZ.v k > 0 /\
    SZ.v k <= SZ.v n
  )
  returns result: int
  ensures exists* s_final.
    A.pts_to a s_final **
    pure (
      Seq.length s_final == Seq.length s0 /\
      permutation s0 s_final /\
      sorted_prefix s_final (SZ.v k) /\
      prefix_leq_suffix s_final (SZ.v k) /\
      SZ.v k > 0 /\
      result == Seq.index s_final (SZ.v k `Prims.op_Subtraction` 1)
    )

val complexity_bounded_select (cf c0 n k: nat) : prop

fn select_complexity
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
      complexity_bounded_select cf (reveal c0) (SZ.v n) (SZ.v k)
    )
