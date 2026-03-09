(*
   CLRS Chapter 23: Kruskal's Algorithm — Pure Specification Interface

   Exports the pure functional specification of Kruskal's MST algorithm
   and its key correctness theorems.
*)

module CLRS.Ch23.Kruskal.Spec

open FStar.List.Tot
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Kruskal.Components

(*** Definitions ***)

// Re-export from Components
let is_forest (edges: list edge) (n: nat) : prop =
  CLRS.Ch23.Kruskal.Components.is_forest edges n

(*** Edge Sorting ***)

let rec insert_edge (e: edge) (sorted: list edge) : list edge =
  match sorted with
  | [] -> [e]
  | hd :: tl ->
    if e.w <= hd.w then e :: sorted
    else hd :: insert_edge e tl

let rec sort_edges (edges: list edge) : list edge =
  match edges with
  | [] -> []
  | e :: rest -> insert_edge e (sort_edges rest)

let rec is_sorted_by_weight (edges: list edge) : bool =
  match edges with
  | [] -> true
  | [e] -> true
  | e1 :: e2 :: rest -> e1.w <= e2.w && is_sorted_by_weight (e2 :: rest)

(*** Core Algorithm ***)

/// Process one edge: add to forest if it doesn't create a cycle
let kruskal_step (e: edge) (forest: list edge) (n: nat) : list edge =
  if e.u < n && e.v < n && 
     not (same_component_dec forest e.u e.v) &&
     not (mem_edge e forest)
  then e :: forest
  else forest

/// Process sorted edges greedily
let rec kruskal_process (sorted_edges: list edge) (forest: list edge) (n: nat) 
  : Tot (list edge) (decreases sorted_edges)
  = match sorted_edges with
    | [] -> forest
    | e :: rest ->
      let forest' = kruskal_step e forest n in
      kruskal_process rest forest' n

//SNIPPET_START: pure_kruskal
/// Pure Kruskal: sort edges, then process greedily
let pure_kruskal (g: graph) : list edge =
  let sorted = sort_edges g.edges in
  kruskal_process sorted [] g.n
//SNIPPET_END: pure_kruskal

(*** Sorting Properties ***)

val sort_edges_mem (e: edge) (edges: list edge)
  : Lemma (ensures mem_edge e (sort_edges edges) <==> mem_edge e edges)

val sort_edges_subset (edges: list edge)
  : Lemma (ensures subset_edges (sort_edges edges) edges /\
                   subset_edges edges (sort_edges edges))

val sort_edges_sorted (edges: list edge)
  : Lemma (ensures is_sorted_by_weight (sort_edges edges) = true)

(*** Forest Preservation ***)

val lemma_kruskal_step_preserves_forest (e: edge) (forest: list edge) (n: nat)
  : Lemma (requires is_forest forest n)
          (ensures is_forest (kruskal_step e forest n) n)

(*** Main Correctness Theorems ***)

//SNIPPET_START: theorem_kruskal_produces_spanning_tree
/// Kruskal produces a spanning tree
val theorem_kruskal_produces_spanning_tree (g: graph)
  : Lemma (requires g.n > 0 /\
                    all_connected g.n g.edges /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n /\ e.u <> e.v) /\
                    (exists (mst: list edge). is_mst g mst))
          (ensures is_spanning_tree g (pure_kruskal g))
//SNIPPET_END: theorem_kruskal_produces_spanning_tree

//SNIPPET_START: theorem_kruskal_produces_mst
/// Kruskal produces a minimum spanning tree
val theorem_kruskal_produces_mst (g: graph)
  : Lemma (requires g.n > 0 /\
                    all_connected g.n g.edges /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n /\ e.u <> e.v) /\
                    (exists (mst: list edge). is_mst g mst))
          (ensures is_mst g (pure_kruskal g))
//SNIPPET_END: theorem_kruskal_produces_mst
