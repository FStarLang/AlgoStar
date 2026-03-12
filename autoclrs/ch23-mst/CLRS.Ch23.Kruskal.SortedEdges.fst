(*
   Kruskal's MST Algorithm - Pure Specification with Sorted Edges
   
   This module defines a pure F* specification of Kruskal's algorithm
   that takes a sorted edge list (by weight) as input.
   
   Key components:
   1. Sorted edges predicate (uses MST.Spec edge type)
   2. Pure Kruskal algorithm specification (using BFS-based reachability)
   3. Correctness properties: subset and forest formation (fully proven)
   
   Uses CLRS.Ch23.MST.Spec for graph-theoretic definitions (edge, acyclic,
   reachable, mem_edge, subset_edges) and CLRS.Ch23.Kruskal.Spec for
   proven kruskal_step and forest preservation lemma.
*)

module CLRS.Ch23.Kruskal.SortedEdges

open FStar.List.Tot
open CLRS.Ch23.MST.Spec

module KSpec = CLRS.Ch23.Kruskal.Spec

(*** Sorted Edges Predicate ***)

// Edges are sorted by weight in non-decreasing order
let rec sorted_edges (es: list edge) : prop =
  match es with
  | [] -> True
  | [_] -> True
  | e1 :: e2 :: rest -> 
      e1.w <= e2.w /\ sorted_edges (e2 :: rest)

// Alternative formulation using indices
let sorted_edges_indices (es: list edge) : prop =
  forall (i j: nat). i < j /\ j < length es ==> 
    (index es i).w <= (index es j).w

#restart-solver
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec sorted_edges_indices_helper (es: list edge)
  : Lemma (requires sorted_edges es)
          (ensures sorted_edges_indices es)
          (decreases es)
  = match es with
    | [] | [_] -> ()
    | e1 :: e2 :: rest ->
        sorted_edges_indices_helper (e2 :: rest);
        introduce forall (i j: nat). i < j /\ j < length es ==> (index es i).w <= (index es j).w
        with introduce _ ==> _
        with _. (
          if i = 0 then (
            // e1.w <= e2.w from sorted_edges, and e2.w <= (index (e2::rest) (j-1)).w from IH
            if j = 1 then ()
            else assert ((index (e2 :: rest) 0).w <= (index (e2 :: rest) (j - 1)).w)
          ) else
            // Both in tail: follows directly from IH
            assert ((index (e2 :: rest) (i - 1)).w <= (index (e2 :: rest) (j - 1)).w)
        )
#pop-options

let sorted_edges_implies_indices (es: list edge)
  : Lemma (requires sorted_edges es)
          (ensures sorted_edges_indices es)
  = sorted_edges_indices_helper es

(*** Kruskal Algorithm ***)

// Process one edge using BFS-based reachability from Kruskal.Spec
let process_edge (e: edge) (result: list edge) (n: nat) : list edge =
  KSpec.kruskal_step e result n

// Main Kruskal algorithm: process edges in order
let rec kruskal_pure
  (edges: list edge)
  (result: list edge)
  (n: nat)
  : list edge =
  match edges with
  | [] -> result
  | e :: rest ->
      kruskal_pure rest (process_edge e result n) n

// Top-level Kruskal specification
let kruskal_spec (edges: list edge) (n: nat) : list edge =
  kruskal_pure edges [] n

(*** Correctness Properties ***)

// process_edge result is subset when input is subset
let process_edge_subset (e: edge) (result: list edge) (n: nat) (full_edges: list edge)
  : Lemma (requires subset_edges result full_edges /\ mem_edge e full_edges)
          (ensures subset_edges (process_edge e result n) full_edges)
  = // kruskal_step either returns (e :: result) or result
    subset_edges_cons result e full_edges

// Property 1: Result is subset of input edges
#push-options "--fuel 3 --ifuel 1 --z3rlimit 30"
let rec kruskal_subset_lemma
  (edges: list edge)
  (result: list edge)
  (n: nat)
  (full_edges: list edge)
  : Lemma
    (requires subset_edges result full_edges /\ subset_edges edges full_edges)
    (ensures subset_edges (kruskal_pure edges result n) full_edges)
    (decreases edges)
  = match edges with
    | [] -> ()
    | e :: rest ->
        process_edge_subset e result n full_edges;
        kruskal_subset_lemma rest (process_edge e result n) n full_edges
#pop-options

// Theorem: Kruskal result is subset of input
let kruskal_result_subset (edges: list edge) (n: nat)
  : Lemma (subset_edges (kruskal_spec edges n) edges)
  = subset_edges_reflexive edges;
    kruskal_subset_lemma edges [] n edges

// Property 2: Result forms a forest (fully proven)
// Uses lemma_kruskal_step_preserves_forest from Kruskal.Spec
let rec kruskal_acyclic_lemma
  (edges: list edge)
  (result: list edge)
  (n: nat)
  : Lemma
    (requires KSpec.is_forest result n)
    (ensures KSpec.is_forest (kruskal_pure edges result n) n)
    (decreases edges)
  = match edges with
    | [] -> ()
    | e :: rest ->
        KSpec.lemma_kruskal_step_preserves_forest e result n;
        kruskal_acyclic_lemma rest (process_edge e result n) n

// Theorem: Kruskal result is a forest
let kruskal_result_is_forest (edges: list edge) (n: nat)
  : Lemma (KSpec.is_forest (kruskal_spec edges n) n)
  = kruskal_acyclic_lemma edges [] n


