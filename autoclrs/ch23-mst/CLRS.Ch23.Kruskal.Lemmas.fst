(*
   CLRS Chapter 23: Kruskal's Algorithm — Lemmas Façade

   Opens all Kruskal helper modules and re-exports their key lemmas.
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

(*** Components / Reachability — delegate to Components ***)

let same_component_reflexive = KComp.same_component_reflexive

let same_component_symmetric = KComp.same_component_symmetric

let same_component_transitive = KComp.same_component_transitive

let same_component_dec_sound = KComp.same_component_dec_sound

(*** Edge Sorting — delegate to EdgeSorting ***)

let sort_edges_is_permutation (edges: list edge) =
  KEdge.sort_edges_is_permutation edges

let sort_edges_produces_sorted (edges: list edge) =
  KEdge.sort_edges_produces_sorted edges

(*** Sorted Edges — delegate to SortedEdges ***)

let kruskal_result_subset = KSort.kruskal_result_subset

let kruskal_result_is_forest = KSort.kruskal_result_is_forest

(*** Union-Find — delegate to UF ***)

let uf_inv_init = KUF.uf_inv_init
