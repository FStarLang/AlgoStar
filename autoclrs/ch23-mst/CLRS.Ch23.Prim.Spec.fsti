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

/// Intro lemma for well_formed_adj
val well_formed_adj_intro (adj: adj_matrix) (n: nat)
  : Lemma (requires length adj = n /\
                    (forall (u: nat). u < n ==> length (index adj u) = n) /\
                    (forall (u v: nat). u < n /\ v < n ==>
                      index (index adj u) v = index (index adj v) u))
          (ensures well_formed_adj adj n)

val has_edge (adj: adj_matrix) (n: nat) (u v: nat) : bool

/// Intro: establish has_edge from concrete matrix data
val has_edge_intro (adj: adj_matrix) (n: nat) (u v: nat)
  : Lemma (requires u < n /\ v < n /\ length adj = n /\ length (index adj u) = n /\
                    index (index adj u) v <> infinity)
          (ensures has_edge adj n u v = true)

val adj_to_edges (adj: adj_matrix) (n: nat) : list edge

val adj_to_graph (adj: adj_matrix) (n: nat) : graph

/// The edges of adj_to_graph are adj_to_edges
val adj_to_graph_edges (adj: adj_matrix) (n: nat)
  : Lemma (ensures (adj_to_graph adj n).edges == adj_to_edges adj n /\
                   (adj_to_graph adj n).n == n)

/// All edges produced by adj_to_graph have valid endpoints
val adj_to_graph_edges_valid (adj: adj_matrix) (n: nat) (e: edge)
  : Lemma (requires mem_edge e (adj_to_graph adj n).edges)
          (ensures e.u < n /\ e.v < n /\ e.u <> e.v)

/// Graph edge weight equals adj matrix entry
val adj_to_graph_edge_weight (adj: adj_matrix) (n: nat) (e: edge)
  : Lemma (requires well_formed_adj adj n /\ n > 0 /\
                    mem_edge e (adj_to_graph adj n).edges /\
                    e.u < n /\ e.v < n /\ length adj = n /\ length (index adj e.u) = n)
          (ensures e.w = index (index adj e.u) e.v)

/// If adj is well-formed, u < v, and adj[u][v] ≠ infinity, the edge is in the graph
val adj_to_graph_has_edge (adj: adj_matrix) (n: nat) (eu ev: nat)
  : Lemma (requires well_formed_adj adj n /\ eu < n /\ ev < n /\ eu < ev /\
                    length adj = n /\ length (index adj eu) = n /\
                    has_edge adj n eu ev)
          (ensures mem_edge ({u = eu; v = ev; w = index (index adj eu) ev})
                            (adj_to_graph adj n).edges)

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

/// Pure Prim produces MST for connected graphs with valid edges
val pure_prim_is_mst (adj: adj_matrix) (n: nat) (start: nat)
  : Lemma (requires n > 0 /\ start < n /\
                    well_formed_adj adj n /\
                    all_connected n (adj_to_edges adj n) /\
                    (forall (e: edge). mem_edge e (adj_to_graph adj n).edges ==>
                      e.u < n /\ e.v < n /\ e.u <> e.v))
          (ensures is_mst (adj_to_graph adj n) (pure_prim adj n start))

/// Connectivity implies crossing edge exists between in-tree and non-tree vertices
val lemma_connected_implies_crossing_edge
    (adj: adj_matrix) (n: nat) (its: vertex_set)
  : Lemma (requires well_formed_adj adj n /\ length its = n /\
                    all_connected n (adj_to_edges adj n) /\ n > 0 /\
                    (exists (u: nat). u < n /\ index its u = true) /\
                    (exists (v: nat). v < n /\ index its v = false))
          (ensures (exists (u' v': nat). u' < n /\ v' < n /\
                    u' < length its /\ v' < length its /\
                    index its u' = true /\ index its v' = false /\
                    has_edge adj n u' v'))
