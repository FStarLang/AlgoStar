(*
   CLRS Chapter 23: Prim's Algorithm — Imperative Implementation Interface

   Pulse function signature for the verified Prim's MST algorithm.
   Uses adjacency matrix representation with linear-scan extract-min.

   ============================================================
   SPEC CONNECTION STATUS — PARTIAL
   ============================================================
   The prim fn postcondition (prim_correct) proves:
   - key[source] = 0, all keys bounded, parent[source] = source

   The lemma prim_impl_produces_mst states but does NOT prove (admitted):
   - The edges encoded in the parent array form a spanning tree
     that is a subset of some MST (matching Prim.Spec.prim_spec)
   
   Completing the proof requires strengthening the main loop invariant
   to track correspondence between key/parent arrays and pure_prim_step.
   ============================================================
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

module PrimSpec = CLRS.Ch23.Prim.Spec

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

/// Convert weight matrix from SizeT array to adjacency matrix spec
val weights_to_adj_matrix (weights_seq: Seq.seq SZ.t) (n: nat) 
  : Pure adj_matrix
    (requires Seq.length weights_seq == n * n)
    (ensures fun adj -> 
      Seq.length adj == n /\
      (forall (u:nat). u < n ==> Seq.length (Seq.index adj u) == n))

/// Extract MST edges from the parent array:
/// For each vertex v ≠ source, emit edge {parent[v], v, key[v]}
val edges_from_parent_key
  (parent_seq key_seq: Seq.seq SZ.t) (n source: nat) (i: nat)
  : Pure (list edge)
    (requires Seq.length parent_seq == n /\ Seq.length key_seq == n /\ i <= n)
    (ensures fun _ -> True)

//SNIPPET_START: prim_impl_produces_mst
/// Impl ↔ Spec bridging lemma — ADMITTED, WORK IN PROGRESS
/// States that the edges from the parent array form a spanning tree
/// subset of some MST, matching the guarantees of Prim.Spec.prim_spec.
val prim_impl_produces_mst
  (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma (requires
      prim_correct key_seq parent_seq weights_seq n source /\
      valid_weights weights_seq n /\
      n > 0 /\ source < n /\
      n * n < pow2 64 /\
      PrimSpec.well_formed_adj (weights_to_adj_matrix weights_seq n) n /\
      all_connected n (PrimSpec.adj_to_edges (weights_to_adj_matrix weights_seq n) n) /\
      (exists (t: list edge). is_mst (PrimSpec.adj_to_graph (weights_to_adj_matrix weights_seq n) n) t))
    (ensures (
      let adj = weights_to_adj_matrix weights_seq n in
      let g = PrimSpec.adj_to_graph adj n in
      let impl_edges = edges_from_parent_key parent_seq key_seq n source 0 in
      List.Tot.length impl_edges = n - 1 /\
      (exists (t: list edge). is_mst g t /\ subset_edges impl_edges t) /\
      all_connected n impl_edges))
//SNIPPET_END: prim_impl_produces_mst

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
