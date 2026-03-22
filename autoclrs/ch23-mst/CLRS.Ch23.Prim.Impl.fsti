(*
   CLRS Chapter 23: Prim's Algorithm — Imperative Implementation Interface

   Pulse function signature for the verified Prim's MST algorithm.
   Uses adjacency matrix representation with linear-scan extract-min.

   The prim fn postcondition (prim_correct) proves:
   - key[source] = 0, all keys bounded, parent[source] = source

   The function edges_from_parent_key extracts edges from the parent
   array for use in MST reasoning.
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
module Bridge = CLRS.Ch23.Kruskal.Bridge

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

/// All parent values are valid vertex indices
let parent_valid (parent_seq: Seq.seq SZ.t) (n: nat) : prop =
  forall (v:nat). v < Seq.length parent_seq ==> SZ.v (Seq.index parent_seq v) < n

/// For non-source vertices with finite key, key equals the edge weight to the parent.
/// This links the imperative output to the graph structure: key[v] is the actual
/// weight of the edge connecting v to its parent in the MST.
let key_parent_consistent
    (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat) : prop =
  forall (v:nat). (v < n /\ v <> source /\
    v < Seq.length key_seq /\
    v < Seq.length parent_seq /\
    SZ.v (Seq.index key_seq v) < SZ.v infinity /\
    SZ.v (Seq.index parent_seq v) < n /\
    SZ.v (Seq.index parent_seq v) * n + v < Seq.length weights_seq) ==>
    SZ.v (Seq.index key_seq v) == SZ.v (Seq.index weights_seq (SZ.v (Seq.index parent_seq v) * n + v))

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
    SZ.v (Seq.index parent_seq source) == source /\
    parent_valid parent_seq n /\
    key_parent_consistent key_seq parent_seq weights_seq n source

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

/// Symmetric weight matrix (undirected graph)
let symmetric_weights (weights_seq: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length weights_seq == n * n /\
  (forall (u v: nat). u < n /\ v < n ==>
    SZ.v (Seq.index weights_seq (u * n + v)) = SZ.v (Seq.index weights_seq (v * n + u)))

/// MST result: for connected symmetric graphs, pure_prim gives is_mst
val prim_mst_result (weights_seq: Seq.seq SZ.t) (n source: nat) : prop

/// Elim: extract is_mst from prim_mst_result for connected symmetric graphs
val prim_mst_result_elim (weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires prim_mst_result weights_seq n source /\
              symmetric_weights weights_seq n /\
              all_connected n
                (PrimSpec.adj_to_edges (weights_to_adj_matrix weights_seq n) n))
    (ensures is_mst (PrimSpec.adj_to_graph (weights_to_adj_matrix weights_seq n) n)
                    (PrimSpec.pure_prim (weights_to_adj_matrix weights_seq n) n source))

(*** Kruskal MST Function ***)

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
    pure (prim_correct key_seq parent_seq weights_seq (SZ.v n) (SZ.v source) /\
          prim_mst_result weights_seq (SZ.v n) (SZ.v source))
//SNIPPET_END: prim_sig

(*** MST Bridging Theorem ***)

//SNIPPET_START: prim_result_is_mst
/// Main MST theorem: if the extracted edges form a safe spanning tree, the result is MST.
///
/// Uses Bridge.safe_spanning_tree_is_mst. The preconditions capture:
///   - What Pulse proves: prim_correct
///   - What greedy selection provides: is_spanning_tree, safe (⊆ some MST)
///   - Technical: noRepeats_edge, valid graph edges
///
/// Connection to the CLRS cut property:
///   greedy_step_safe (Bridge) proves each step preserves safety.
///   safe_spanning_tree_is_mst (Bridge) proves the final result is MST.
val prim_result_is_mst
    (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat)
  : Lemma
    (requires
      n > 0 /\
      prim_correct key_seq parent_seq weights_seq n source /\
      Seq.length weights_seq == n * n /\
      (let adj = weights_to_adj_matrix weights_seq n in
       let g = PrimSpec.adj_to_graph adj n in
       let wes = edges_from_parent_key parent_seq key_seq n source 0 in
       is_spanning_tree g wes /\
       (exists (t: list edge). is_mst g t /\ subset_edges wes t) /\
       Bridge.noRepeats_edge wes /\
       (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n /\ e.u <> e.v)))
    (ensures
      (let adj = weights_to_adj_matrix weights_seq n in
       let g = PrimSpec.adj_to_graph adj n in
       let wes = edges_from_parent_key parent_seq key_seq n source 0 in
       is_mst g wes))
//SNIPPET_END: prim_result_is_mst
