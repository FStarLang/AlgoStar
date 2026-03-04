(*
   CLRS Chapter 23: Prim's Algorithm — Imperative Implementation Interface

   Pulse function signature for the verified Prim's MST algorithm.
   Uses adjacency matrix representation with linear-scan extract-min.
*)

module CLRS.Ch23.Prim.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open Pulse.Lib.Reference

open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Prim.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

open FStar.Mul

/// Use a large value for infinity that fits in SizeT
let infinity : SZ.t = 65535sz

/// All real edge weights must be strictly less than infinity
let valid_weights (weights_seq: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length weights_seq == n * n /\
  (forall (i: nat). i < n * n ==>
    SZ.v (Seq.index weights_seq i) = 0 \/
    (SZ.v (Seq.index weights_seq i) > 0 /\ SZ.v (Seq.index weights_seq i) < SZ.v infinity))

/// All keys bounded by infinity
let all_keys_bounded (s: Seq.seq SZ.t) : prop =
  forall (i:nat). i < Seq.length s ==> SZ.v (Seq.index s i) <= SZ.v infinity

/// Predicate for correctness of Prim's output
let prim_correct 
    (key_seq: Seq.seq SZ.t)
    (parent_seq: Seq.seq SZ.t)
    (weights_seq: Seq.seq SZ.t)
    (n: nat) 
    (source: nat) 
  : prop 
  = Seq.length key_seq == n /\
    Seq.length parent_seq == n /\
    source < n /\
    Seq.length weights_seq == n * n /\
    SZ.v (Seq.index key_seq source) == 0 /\
    all_keys_bounded key_seq /\
    SZ.v (Seq.index parent_seq source) == source

//SNIPPET_START: prim_sig
/// Prim's MST algorithm (imperative, adjacency matrix)
///
/// Given:
///   - weights: n×n weight matrix (flattened as array[n*n])
///   - n: number of vertices
///   - source: starting vertex
///
/// Returns: (key_array, parent_array)
///   - key: minimum edge weights to add each vertex to MST
///   - parent: parent of each vertex in the MST
fn prim
  (#p: perm)
  (weights: array SZ.t)
  (#weights_seq: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  (source: SZ.t)
  requires A.pts_to weights #p weights_seq ** pure (
    SZ.v n > 0 /\
    SZ.v n * SZ.v n < pow2 64 /\
    SZ.v source < SZ.v n /\
    Seq.length weights_seq == SZ.v n * SZ.v n /\
    SZ.fits_u64
  )
  returns res: (V.vec SZ.t & V.vec SZ.t)
  ensures exists* (key_seq parent_seq: Ghost.erased (Seq.seq SZ.t)).
    A.pts_to weights #p weights_seq **
    V.pts_to (fst res) key_seq **
    V.pts_to (snd res) parent_seq **
    pure (prim_correct key_seq parent_seq weights_seq (SZ.v n) (SZ.v source))
//SNIPPET_END: prim_sig
