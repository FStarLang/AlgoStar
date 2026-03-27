(*
   CLRS Chapter 23: Kruskal's Algorithm — Imperative Implementation Interface

   Pulse function signature for the verified Kruskal MST algorithm.
   Uses adjacency matrix representation with union-find.

   Exports:
   - fn kruskal: imperative Kruskal with postcondition result_is_forest_adj
   - adj_array_to_graph, weighted_edges_from_arrays: bridge imperative ↔ spec
   - weighted_edges_subset_graph: weighted edges ⊆ graph edges
   - adj_graph_valid_edges: graph edges have valid endpoints
   - kruskal_result_is_mst: safe spanning tree ⟹ MST (via Bridge)
*)

module CLRS.Ch23.Kruskal.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Kruskal.Spec
open CLRS.Ch23.Kruskal.Defs

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

/// Convert SZ.t sequence to int sequence (for bridging implementation → spec)
let sizet_seq_to_int (s: Seq.seq SZ.t) : Seq.seq int =
  Seq.init (Seq.length s) (fun (i:nat{i < Seq.length s}) -> (SZ.v (Seq.index s i) <: int))
module MSTSpec = CLRS.Ch23.MST.Spec
module KSpec = CLRS.Ch23.Kruskal.Spec
module UF = CLRS.Ch23.Kruskal.UF
module Helpers = CLRS.Ch23.Kruskal.Helpers
module Bridge = CLRS.Ch23.Kruskal.Bridge

(*** Impl ↔ Spec Bridging ***)

/// Convert flat adjacency matrix to graph
let rec adj_row_edges (sadj: Seq.seq int) (n: nat) (u v: nat)
  : Pure (list MSTSpec.edge)
    (requires Seq.length sadj == n * n /\ u < n /\ v <= n /\ n > 0)
    (ensures fun _ -> True)
    (decreases (n - v))
  = if v >= n then []
    else
      let w = Seq.index sadj (u * n + v) in
      let rest = adj_row_edges sadj n u (v + 1) in
      if w > 0 && u < v then { MSTSpec.u = u; MSTSpec.v = v; MSTSpec.w = w } :: rest
      else rest

let rec adj_all_edges (sadj: Seq.seq int) (n: nat) (u: nat)
  : Pure (list MSTSpec.edge)
    (requires Seq.length sadj == n * n /\ u <= n /\ n > 0)
    (ensures fun _ -> True)
    (decreases (n - u))
  = if u >= n then []
    else adj_row_edges sadj n u 0 `FStar.List.Tot.append` adj_all_edges sadj n (u + 1)

let adj_array_to_graph (sadj: Seq.seq int) (n: nat{Seq.length sadj == n * n /\ n > 0}) : MSTSpec.graph =
  { MSTSpec.n = n; MSTSpec.edges = adj_all_edges sadj n 0 }

(*** Graph Properties ***)

/// Adjacency matrix is symmetric (undirected graph)
let symmetric_adj (sadj: Seq.seq int) (n: nat) : prop =
  Seq.length sadj == n * n /\
  (forall (u v: nat). u < n /\ v < n ==>
    Seq.index sadj (u * n + v) = Seq.index sadj (v * n + u))

/// No self-loops: diagonal entries are zero
let no_self_loops_adj (sadj: Seq.seq int) (n: nat) : prop =
  Seq.length sadj == n * n /\
  (forall (u: nat). u < n ==> Seq.index sadj (u * n + u) = 0)

(*** MST Bridging Theorems ***)

/// The graph produced by adj_array_to_graph has valid edges
val adj_graph_valid_edges (sadj: Seq.seq int) (n: nat)
  : Lemma
    (requires Seq.length sadj == n * n /\ n > 0)
    (ensures
      (forall (e: edge). mem_edge e (adj_array_to_graph sadj n).edges ==>
        e.u < n /\ e.v < n /\ e.u <> e.v))

/// Weighted edges from the imperative arrays are subset of the graph's edge set
val weighted_edges_subset_graph
    (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires
      n > 0 /\ Seq.length sadj == n * n /\
      ec <= Seq.length seu /\ ec <= Seq.length sev /\
      (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
                                    Seq.index seu k < n /\ Seq.index sev k < n) /\
      edges_adj_pos sadj seu sev n ec /\
      symmetric_adj sadj n /\
      no_self_loops_adj sadj n)
    (ensures
      subset_edges (weighted_edges_from_arrays sadj seu sev n ec 0) (adj_array_to_graph sadj n).edges)

(*** Transfer Lemmas ***)

/// Transfer noRepeats from w=1 edges to weighted edges
val noRepeats_transfer
    (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat) (i: nat{i <= ec})
  : Lemma
    (requires
      n > 0 /\ ec <= Seq.length seu /\ ec <= Seq.length sev /\
      Seq.length sadj == n * n /\
      (forall (k:nat). i <= k /\ k < ec ==>
        Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
        Seq.index seu k < n /\ Seq.index sev k < n) /\
      (forall (k:nat). k < ec ==>
        Seq.index seu k >= 0 /\ Seq.index sev k >= 0) /\
      Bridge.noRepeats_edge (edges_from_arrays seu sev ec i))
    (ensures Bridge.noRepeats_edge (weighted_edges_from_arrays sadj seu sev n ec i))

/// Transfer acyclicity from w=1 edges to weighted edges (requires symmetric adj)
val acyclic_transfer
    (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires
      n > 0 /\ ec <= Seq.length seu /\ ec <= Seq.length sev /\
      Seq.length sadj == n * n /\
      (forall (k:nat). k < ec ==>
        Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
        Seq.index seu k < n /\ Seq.index sev k < n) /\
      symmetric_adj sadj n /\
      MSTSpec.acyclic n (edges_from_arrays seu sev ec 0) /\
      (forall (e: edge). mem_edge e (adj_array_to_graph sadj n).edges ==>
        e.u < n /\ e.v < n /\ e.u <> e.v))
    (ensures MSTSpec.acyclic n (weighted_edges_from_arrays sadj seu sev n ec 0))

//SNIPPET_START: kruskal_result_is_mst
/// Main MST theorem: if the weighted edges form a safe spanning tree, the result is MST.
///
/// Uses Bridge.safe_spanning_tree_is_mst. The preconditions capture:
///   - What Pulse proves: result_is_forest_adj
///   - Graph properties: symmetric, no self-loops
///   - What greedy selection provides: is_spanning_tree, safe (⊆ some MST)
///   - Technical: noRepeats_edge, valid endpoints
///
/// Connection to the CLRS cut property:
///   greedy_step_safe (Bridge) proves each step preserves safety.
///   safe_spanning_tree_is_mst (Bridge) proves the final result is MST.
val kruskal_result_is_mst
    (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires
      n > 0 /\ Seq.length sadj == n * n /\
      ec <= Seq.length seu /\ ec <= Seq.length sev /\
      (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
                                    Seq.index seu k < n /\ Seq.index sev k < n) /\
      result_is_forest_adj sadj seu sev n ec /\
      symmetric_adj sadj n /\
      no_self_loops_adj sadj n /\
      is_spanning_tree (adj_array_to_graph sadj n) (weighted_edges_from_arrays sadj seu sev n ec 0) /\
      (exists (t: list edge). is_mst (adj_array_to_graph sadj n) t /\
        subset_edges (weighted_edges_from_arrays sadj seu sev n ec 0) t) /\
      Bridge.noRepeats_edge (weighted_edges_from_arrays sadj seu sev n ec 0) /\
      (forall (e: edge). mem_edge e (adj_array_to_graph sadj n).edges ==>
        e.u < n /\ e.v < n /\ e.u <> e.v))
    (ensures
      is_mst (adj_array_to_graph sadj n) (weighted_edges_from_arrays sadj seu sev n ec 0))
//SNIPPET_END: kruskal_result_is_mst


(*** Pure Spec MST Theorem ***)

(*** Safety Infrastructure ***)

/// Safety predicate: edges ⊆ some MST
let edges_safe (g: graph) (es: list edge) : prop =
  exists (t: list edge). is_mst g t /\ subset_edges es t


/// Pure Kruskal spec produces MST for connected graphs
val pure_kruskal_is_mst (sadj: Seq.seq int) (n: nat)
  : Lemma
    (requires
      n > 0 /\ Seq.length sadj == n * n /\
      symmetric_adj sadj n /\
      no_self_loops_adj sadj n /\
      all_connected n (adj_array_to_graph sadj n).edges)
    (ensures
      is_mst (adj_array_to_graph sadj n) (KSpec.pure_kruskal (adj_array_to_graph sadj n)))



/// Result predicate: for connected graphs, the imperative output is safe (⊆ some MST)
val kruskal_mst_result (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat) : prop

/// Elim lemma: extract is_mst from kruskal_mst_result for connected symmetric graphs.
/// This is the main MST theorem for the imperative kruskal: calling kruskal on a
/// connected symmetric graph produces an MST.
val kruskal_mst_result_elim (sadj: Seq.seq int) (seu sev: Seq.seq int) (n ec: nat)
  : Lemma
    (requires kruskal_mst_result sadj seu sev n ec /\
              result_is_forest_adj sadj seu sev n ec /\
              n > 0 /\ Seq.length sadj == n * n /\
              ec <= Seq.length seu /\ ec <= Seq.length sev /\
              (forall (k:nat). k < ec ==> Seq.index seu k >= 0 /\ Seq.index sev k >= 0 /\
                                            Seq.index seu k < n /\ Seq.index sev k < n) /\
              symmetric_adj sadj n /\ no_self_loops_adj sadj n /\
              all_connected n (adj_array_to_graph sadj n).edges)
    (ensures is_mst (adj_array_to_graph sadj n) (weighted_edges_from_arrays sadj seu sev n ec 0))

(*** Kruskal Function ***)

//SNIPPET_START: kruskal_sig
fn kruskal
  (adj: A.array int)
  (#p: perm) (#sadj: Ghost.erased (Seq.seq int))
  (edge_u edge_v: A.array SZ.t)
  (#sedge_u #sedge_v: Ghost.erased (Seq.seq SZ.t))
  (edge_count: R.ref SZ.t)
  (n: SZ.t)
  requires
    A.pts_to adj #p sadj **
    A.pts_to edge_u sedge_u **
    A.pts_to edge_v sedge_v **
    R.pts_to edge_count 0sz **
    pure (
      SZ.v n > 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sedge_u == SZ.v n /\
      Seq.length sedge_v == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns _: unit
  ensures exists* vec sedge_u' sedge_v'.
    A.pts_to adj #p sadj **
    A.pts_to edge_u sedge_u' **
    A.pts_to edge_v sedge_v' **
    R.pts_to edge_count vec **
    pure (result_is_forest_adj sadj (sizet_seq_to_int sedge_u') (sizet_seq_to_int sedge_v') (SZ.v n) (SZ.v vec) /\
          kruskal_mst_result sadj (sizet_seq_to_int sedge_u') (sizet_seq_to_int sedge_v') (SZ.v n) (SZ.v vec))
//SNIPPET_END: kruskal_sig
