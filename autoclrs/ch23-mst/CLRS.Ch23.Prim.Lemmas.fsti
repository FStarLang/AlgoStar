(*
   CLRS Chapter 23: Prim's Algorithm — Lemmas Interface

   Façade re-exporting key lemma signatures from Prim.Spec:
   - Adjacency matrix edge validity
   - Correctness properties (edge count, connectivity, safe-edge)

   Internal helper lemmas (prim step properties, safety preservation)
   remain in Prim.Spec.fst as they reference internal definitions
   like pure_prim_step that are not part of the public interface.
*)

module CLRS.Ch23.Prim.Lemmas

open FStar.List.Tot
open FStar.Seq
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Prim.Spec

(*** Graph Validity ***)

/// All edges produced by adj_to_graph have valid endpoints
val adj_to_graph_edges_valid (adj: adj_matrix) (n: nat) (e: edge)
  : Lemma (requires mem_edge e (adj_to_graph adj n).edges)
          (ensures e.u < n /\ e.v < n)

(*** Correctness Properties ***)

/// pure_prim produces exactly n-1 edges
val lemma_prim_has_n_minus_1_edges (adj: adj_matrix) (n: nat) (start: nat)
  : Lemma (requires n > 0 /\ start < n /\ well_formed_adj adj n /\
                    all_connected n (adj_to_edges adj n))
          (ensures List.Tot.length (pure_prim adj n start) = n - 1)

/// pure_prim result connects all vertices
val lemma_prim_all_connected (adj: adj_matrix) (n: nat) (start: nat)
  : Lemma (requires n > 0 /\ start < n /\ well_formed_adj adj n /\
                    all_connected n (adj_to_edges adj n))
          (ensures all_connected n (pure_prim adj n start))

/// pure_prim result is safe (subset of some MST)
val lemma_prim_result_is_safe (adj: adj_matrix) (n: nat) (start: nat)
  : Lemma (requires n > 0 /\ start < n /\ well_formed_adj adj n /\
                    (exists (t: list edge). is_mst (adj_to_graph adj n) t))
          (ensures (exists (t: list edge).
                     is_mst (adj_to_graph adj n) t /\
                     subset_edges (pure_prim adj n start) t))
