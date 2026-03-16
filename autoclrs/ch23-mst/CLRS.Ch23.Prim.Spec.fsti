(*
   CLRS Chapter 23: Prim's Algorithm — Pure Specification Interface

   Exports the pure functional specification of Prim's MST algorithm
   and its key correctness theorems.
*)

module CLRS.Ch23.Prim.Spec

open FStar.List.Tot
open FStar.Seq
open CLRS.Ch23.MST.Spec

(*** Adjacency Matrix Representation ***)

let adj_matrix = seq (seq int)

let infinity : int = 1000000000

val well_formed_adj (adj: adj_matrix) (n: nat) : prop

val has_edge (adj: adj_matrix) (n: nat) (u v: nat) : bool

val adj_to_edges (adj: adj_matrix) (n: nat) : list edge

val adj_to_graph (adj: adj_matrix) (n: nat) : graph

/// All edges produced by adj_to_graph have valid endpoints
val adj_to_graph_edges_valid (adj: adj_matrix) (n: nat) (e: edge)
  : Lemma (requires mem_edge e (adj_to_graph adj n).edges)
          (ensures e.u < n /\ e.v < n)

(*** Vertex Set / Cut ***)

type vertex_set = seq bool

val in_tree (s: vertex_set) (v: nat) : prop

val vertex_set_to_cut (s: vertex_set) : cut

val add_to_tree (s: vertex_set) (v: nat) : vertex_set

(*** Core Algorithm ***)

//SNIPPET_START: pure_prim
/// Pure Prim's algorithm: given adjacency matrix, size, and start vertex
val pure_prim (adj: adj_matrix) (n: nat) (start: nat) : list edge
//SNIPPET_END: pure_prim

(*** Correctness Properties ***)

val lemma_prim_has_n_minus_1_edges (adj: adj_matrix) (n: nat) (start: nat)
  : Lemma (requires n > 0 /\ start < n /\ well_formed_adj adj n /\
                    all_connected n (adj_to_edges adj n))
          (ensures List.Tot.length (pure_prim adj n start) = n - 1)

val lemma_prim_all_connected (adj: adj_matrix) (n: nat) (start: nat)
  : Lemma (requires n > 0 /\ start < n /\ well_formed_adj adj n /\
                    all_connected n (adj_to_edges adj n))
          (ensures all_connected n (pure_prim adj n start))

val lemma_prim_result_is_safe (adj: adj_matrix) (n: nat) (start: nat)
  : Lemma (requires n > 0 /\ start < n /\ well_formed_adj adj n /\
                    (exists (t: list edge). is_mst (adj_to_graph adj n) t))
          (ensures (exists (t: list edge).
                     is_mst (adj_to_graph adj n) t /\
                     subset_edges (pure_prim adj n start) t))

//SNIPPET_START: prim_spec
/// Full specification: Prim produces edges that are subset of MST, connect all vertices, count = n-1
val prim_spec (adj: adj_matrix) (n: nat) (start: nat)
  : Pure (list edge)
    (requires n > 0 /\ start < n /\
              well_formed_adj adj n /\
              all_connected n (adj_to_edges adj n) /\
              (exists (t: list edge). is_mst (adj_to_graph adj n) t))
    (ensures fun result ->
      let g = adj_to_graph adj n in
      List.Tot.length result = n - 1 /\
      (exists (t: list edge). is_mst g t /\ subset_edges result t) /\
      all_connected n result)
//SNIPPET_END: prim_spec
