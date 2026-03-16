(*
   CLRS Chapter 23: Prim's Algorithm — Lemmas Façade

   Opens Prim.Spec and re-exports key lemmas.
*)

module CLRS.Ch23.Prim.Lemmas

open FStar.List.Tot
open FStar.Seq
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Prim.Spec

module PSpec = CLRS.Ch23.Prim.Spec

(*** Graph Validity — delegate to Prim.Spec ***)

let adj_to_graph_edges_valid = PSpec.adj_to_graph_edges_valid

(*** Correctness Properties — delegate to Prim.Spec ***)

let lemma_prim_has_n_minus_1_edges = PSpec.lemma_prim_has_n_minus_1_edges

let lemma_prim_all_connected = PSpec.lemma_prim_all_connected

let lemma_prim_result_is_safe = PSpec.lemma_prim_result_is_safe
