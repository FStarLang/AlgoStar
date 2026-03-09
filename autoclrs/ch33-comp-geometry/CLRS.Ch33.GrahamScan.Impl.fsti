(*
   Graham Scan — CLRS Chapter 33, Section 33.3
   
   Pulse implementation interface: verified imperative versions of
   find_bottom, polar_cmp, and pop_while.
*)

module CLRS.Ch33.GrahamScan.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.GrahamScan.Spec
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

//SNIPPET_START: find_bottom_sig
fn find_bottom (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len > 0 /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys
    )
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v result == find_bottom_spec sxs sys /\
      SZ.v result < SZ.v len
    )
//SNIPPET_END: find_bottom_sig

//SNIPPET_START: polar_cmp_sig
fn polar_cmp (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t) (p0 a b: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v p0 < SZ.v len /\
      SZ.v a < SZ.v len /\
      SZ.v b < SZ.v len /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys
    )
  returns result: int
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (result == polar_cmp_spec sxs sys (SZ.v p0) (SZ.v a) (SZ.v b))
//SNIPPET_END: polar_cmp_sig

//SNIPPET_START: pop_while_sig
fn pop_while (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (#ph: perm) (hull: array SZ.t)
  (#shull: Ghost.erased (Seq.seq SZ.t))
  (top_in: SZ.t) (p_idx: SZ.t) (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    A.pts_to hull #ph shull **
    pure (
      SZ.v top_in >= 2 /\
      SZ.v top_in <= Seq.length shull /\
      SZ.v p_idx < SZ.v len /\
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys /\
      Seq.length shull == A.length hull /\
      (forall (i: nat). i < SZ.v top_in ==> SZ.v (Seq.index shull i) < SZ.v len)
    )
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    A.pts_to hull #ph shull **
    pure (
      SZ.v result == pop_while_spec sxs sys shull (SZ.v top_in) (SZ.v p_idx) /\
      SZ.v result <= SZ.v top_in
    )
//SNIPPET_END: pop_while_sig
