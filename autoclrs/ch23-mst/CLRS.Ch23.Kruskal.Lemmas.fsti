(*
   CLRS Chapter 23: Kruskal's Algorithm — Lemmas Interface

   Façade re-exporting key lemma signatures from the Kruskal helper modules:
   - Components: BFS reachability, same-component, forest/acyclicity
   - EdgeSorting: sort permutation, MST weight independence
   - SortedEdges: Kruskal over sorted input
   - UF: Union-find correctness
   - Helpers: Forest invariant maintenance
*)

module CLRS.Ch23.Kruskal.Lemmas

open FStar.List.Tot
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Kruskal.Components
open CLRS.Ch23.Kruskal.Spec

module KComp = CLRS.Ch23.Kruskal.Components
module KEdge = CLRS.Ch23.Kruskal.EdgeSorting
module KSort = CLRS.Ch23.Kruskal.SortedEdges
module KUF   = CLRS.Ch23.Kruskal.UF
module KHelp = CLRS.Ch23.Kruskal.Helpers

(*** Components / Reachability ***)

/// Reachability is reflexive
val same_component_reflexive (edges: list edge) (u: nat)
  : Lemma (same_component edges u u)

/// Reachability is symmetric
val same_component_symmetric (edges: list edge) (u v: nat)
  : Lemma (requires same_component edges u v)
          (ensures same_component edges v u)

/// Reachability is transitive
val same_component_transitive (edges: list edge) (u v w: nat)
  : Lemma (requires same_component edges u v /\ same_component edges v w)
          (ensures same_component edges u w)

/// BFS decision procedure is sound
val same_component_dec_sound (edges: list edge) (u v: nat)
  : Lemma (requires same_component_dec edges u v = true)
          (ensures same_component edges u v)

(*** Edge Sorting ***)

/// Sorting produces a permutation (membership equivalence)
val sort_edges_is_permutation (edges: list edge)
  : Lemma (ensures (forall (e: edge). mem_edge e edges <==> mem_edge e (sort_edges edges)))

/// Sorting produces sorted output
val sort_edges_produces_sorted (edges: list edge)
  : Lemma (ensures KEdge.edges_sorted_by_weight (sort_edges edges))

(*** Sorted Edges — Kruskal over pre-sorted input ***)

/// Kruskal result over sorted input is a subset of the input
val kruskal_result_subset (edges: list edge) (n: nat)
  : Lemma (subset_edges (KSort.kruskal_spec edges n) edges)

/// Kruskal result over sorted input is a forest
val kruskal_result_is_forest (edges: list edge) (n: nat)
  : Lemma (is_forest (KSort.kruskal_spec edges n) n)

(*** Union-Find Correctness ***)

/// UF invariant on identity parent array
val uf_inv_init (sparent: FStar.Seq.seq FStar.SizeT.t) (n: nat)
  : Lemma (requires KUF.identity_parent n sparent /\ n > 0)
          (ensures KUF.uf_inv sparent [] n 0)
