(*
   CLRS Chapter 23: Kruskal's Algorithm - Pure Specification
   
   This module provides a pure functional specification of Kruskal's MST algorithm.
   Key components:
   1. Forest/acyclic edge set definition
   2. Connected components computation
   3. Pure Kruskal algorithm specification
   4. Correctness properties using cut property from CLRS.Ch23.MST.Spec
*)

module CLRS.Ch23.Kruskal.Spec

open FStar.List.Tot
open CLRS.Ch23.MST.Spec

(*** Forest and Acyclicity ***)

// A forest is an acyclic edge set
// (Directly using acyclic from MST.Spec for consistency)
let is_forest (edges: list edge) (n: nat) : prop =
  acyclic n edges

(*** Connected Components ***)

// Two vertices are in the same component if they're reachable via the edge set
let same_component (edges: list edge) (u v: nat) : prop =
  reachable edges u v

// Same component is reflexive
let same_component_reflexive (edges: list edge) (u: nat)
  : Lemma (same_component edges u u)
  = assert (is_path_from_to [] u u)

// Helper: appending a single edge at the end extends a path
let rec is_path_append_edge (path: list edge) (u v w: nat) (e: edge)
  : Lemma 
    (requires is_path_from_to path u v /\ (e.u = v /\ w = e.v \/ e.v = v /\ w = e.u))
    (ensures is_path_from_to (path @ [e]) u w)
    (decreases path)
  = match path with
    | [] -> ()
    | hd :: rest ->
      if hd.u = u then 
        is_path_append_edge rest hd.v v w e
      else 
        is_path_append_edge rest hd.u v w e

// Helper: reversing a path reverses direction
#push-options "--fuel 3 --ifuel 1 --z3rlimit 30"
let rec is_path_reverse (path: list edge) (u v: nat)
  : Lemma 
    (requires is_path_from_to path u v)
    (ensures is_path_from_to (rev path) v u)
    (decreases path)
  = match path with
    | [] -> ()
    | e :: rest ->
      if e.u = u then (
        is_path_reverse rest e.v v;
        assert (is_path_from_to (rev rest) v e.v);
        is_path_append_edge (rev rest) v e.v u e;
        assert (is_path_from_to (rev rest @ [e]) v u);
        FStar.List.Tot.Properties.rev_append [e] rest;
        assert (rev (e :: rest) == rev rest @ [e])
      ) else (
        assert (e.v = u);
        is_path_reverse rest e.u v;
        assert (is_path_from_to (rev rest) v e.u);
        is_path_append_edge (rev rest) v e.u u e;
        assert (is_path_from_to (rev rest @ [e]) v u);
        FStar.List.Tot.Properties.rev_append [e] rest;
        assert (rev (e :: rest) == rev rest @ [e])
      )
#pop-options

// Helper for subset appending a single edge
let rec subset_edges_append_single (prefix: list edge) (e: edge) (es: list edge)
  : Lemma 
    (requires subset_edges prefix es /\ mem_edge e es)
    (ensures subset_edges (prefix @ [e]) es)
    (decreases prefix)
  = match prefix with
    | [] -> ()
    | hd :: rest -> subset_edges_append_single rest e es

// Helper: subset preserved under reversal
#push-options "--fuel 3 --ifuel 1 --z3rlimit 20"
let rec subset_edges_rev (path: list edge) (es: list edge)
  : Lemma 
    (requires subset_edges path es)
    (ensures subset_edges (rev path) es)
    (decreases path)
  = match path with
    | [] -> ()
    | e :: rest ->
      subset_edges_rev rest es;
      subset_edges_append_single (rev rest) e es;
      FStar.List.Tot.Properties.rev_append [e] rest
#pop-options

// Helper: path concatenation
let rec is_path_concat (p1 p2: list edge) (u v w: nat)
  : Lemma 
    (requires is_path_from_to p1 u v /\ is_path_from_to p2 v w)
    (ensures is_path_from_to (p1 @ p2) u w)
    (decreases p1)
  = match p1 with
    | [] -> ()
    | e :: rest ->
      if e.u = u then 
        is_path_concat rest p2 e.v v w
      else 
        is_path_concat rest p2 e.u v w

// Helper: subset_edges distributes over append
let rec subset_edges_concat (p1 p2: list edge) (es: list edge)
  : Lemma 
    (requires subset_edges p1 es /\ subset_edges p2 es)
    (ensures subset_edges (p1 @ p2) es)
    (decreases p1)
  = match p1 with
    | [] -> ()
    | _ :: rest -> subset_edges_concat rest p2 es

// Same component is symmetric
let same_component_symmetric (edges: list edge) (u v: nat)
  : Lemma (requires same_component edges u v)
          (ensures same_component edges v u)
  = eliminate exists (path: list edge). subset_edges path edges /\ is_path_from_to path u v
    returns same_component edges v u
    with _. (
      is_path_reverse path u v;
      subset_edges_rev path edges
    )

// Same component is transitive
let same_component_transitive (edges: list edge) (u v w: nat)
  : Lemma (requires same_component edges u v /\ same_component edges v w)
          (ensures same_component edges u w)
  = eliminate exists (p1: list edge). subset_edges p1 edges /\ is_path_from_to p1 u v
    returns same_component edges u w
    with _. (
      eliminate exists (p2: list edge). subset_edges p2 edges /\ is_path_from_to p2 v w
      returns same_component edges u w
      with _. (
        is_path_concat p1 p2 u v w;
        subset_edges_concat p1 p2 edges
      )
    )

// Helper: get maximum vertex index from edge list
let rec max_vertex_in_edges (edges: list edge) : nat =
  match edges with
  | [] -> 0
  | e :: rest ->
    let mr = max_vertex_in_edges rest in
    let m = if e.u > e.v then e.u else e.v in
    if m > mr then m else mr

// Helper: get all neighbors of vertex v in edge list
let rec edge_neighbors (edges: list edge) (v: nat) : list nat =
  match edges with
  | [] -> []
  | e :: rest ->
    let ns = edge_neighbors rest v in
    if e.u = v then e.v :: ns
    else if e.v = v then e.u :: ns
    else ns

// BFS reachability: explore from frontier, tracking visited vertices
let rec bfs_reach_list (edges: list edge) (frontier: list nat) (visited: list nat) (fuel: nat)
  : Tot (list nat) (decreases %[fuel; List.Tot.length frontier])
  = if fuel = 0 then visited
    else match frontier with
    | [] -> visited
    | v :: rest ->
      if mem v visited then
        bfs_reach_list edges rest visited fuel
      else
        let visited' = v :: visited in
        let new_neighbors = edge_neighbors edges v in
        bfs_reach_list edges (List.Tot.append rest new_neighbors) visited' (fuel - 1)

// Decidable version of same_component using BFS
// Returns true if there exists a path from u to v using edges
let same_component_dec (edges: list edge) (u v: nat) : bool =
  if u = v then true
  else
    let n = max_vertex_in_edges edges + 1 in
    let visited = bfs_reach_list edges [u] [] n in
    mem v visited

// Get all vertices reachable from v
let rec vertices_in_component (edges: list edge) (v: nat) (n: nat) (i: nat{i <= n}) 
  : Tot (list nat) (decreases (n - i))
  = if i >= n then []
    else if same_component_dec edges v i then
      i :: vertices_in_component edges v n (i + 1)
    else
      vertices_in_component edges v n (i + 1)

// Component containing vertex v
let component_of (edges: list edge) (v: nat) (n: nat) : list nat =
  vertices_in_component edges v n 0

// All connected components (represented as list of vertex lists)
// Build by iterating through vertices and adding new components
// Check if vertex v is in any component list
let rec in_some_component (v: nat) (comps: list (list nat)) : bool =
  match comps with
  | [] -> false
  | c :: rest -> mem v c || in_some_component v rest

let rec build_components (edges: list edge) (n: nat) (i: nat{i <= n}) 
                         (acc: list (list nat))
  : Tot (list (list nat)) (decreases (n - i))
  = if i >= n then acc
    else begin
      if in_some_component i acc then
        build_components edges n (i + 1) acc
      else
        let new_comp = component_of edges i n in
        build_components edges n (i + 1) (new_comp :: acc)
    end

// Main function to compute components
let components (edges: list edge) (n: nat) : list (list nat) =
  if n = 0 then [] else build_components edges n 0 []

(*** Properties of Components ***)

/// in_some_component returns false when v is not in any component
let rec in_some_component_false (v: nat) (comps: list (list nat))
  : Lemma (requires forall (c: list nat). mem c comps ==> ~(mem v c))
          (ensures in_some_component v comps = false)
          (decreases comps)
  = match comps with
  | [] -> ()
  | c :: rest -> in_some_component_false v rest

// Helper: if w is in edge_neighbors of v, then there's an edge between v and w
let rec edge_neighbors_sound (edges: list edge) (v w: nat)
  : Lemma (requires mem w (edge_neighbors edges v))
          (ensures exists e. mem_edge e edges /\ 
                            ((e.u = v /\ e.v = w) \/ (e.v = v /\ e.u = w)))
          (decreases edges)
  = match edges with
    | [] -> ()
    | e :: rest ->
      if e.u = v && e.v = w then ()
      else if e.v = v && e.u = w then ()
      else edge_neighbors_sound rest v w

// Helper: if there's an edge between v and w, then w is reachable from v
let edge_gives_reachability (edges: list edge) (v w: nat) (e: edge)
  : Lemma (requires mem_edge e edges /\ ((e.u = v /\ e.v = w) \/ (e.v = v /\ e.u = w)))
          (ensures reachable edges v w)
  = let path = [e] in
    assert (is_path_from_to path v w);
    assert (subset_edges path edges)

// Helper: reachability is transitive via path concatenation
let reachability_transitive (edges: list edge) (u v w: nat)
  : Lemma (requires reachable edges u v /\ reachable edges v w)
          (ensures reachable edges u w)
  = same_component_transitive edges u v w

// Helper lemma: if a vertex is in the frontier, we can reach it
let rec mem_frontier_reachable (frontier: list nat) (u v: nat)
  : Lemma (requires mem u frontier)
          (ensures exists u'. mem u' frontier /\ reachable [] u' v ==> reachable [] u v)
  = ()

// Helper: membership in appended list
let rec mem_append (#a: eqtype) (x: a) (l1 l2: list a)
  : Lemma (mem x (l1 @ l2) <==> (mem x l1 \/ mem x l2))
  = match l1 with
    | [] -> ()
    | hd :: tl -> mem_append x tl l2

// Key lemma: BFS soundness - every vertex in result is either in visited or reachable from frontier  
// NOTE: This is a difficult proof. The high-level idea is correct but F*'s SMT encoding
// makes it hard to connect exists/forall reasoning. Admitting for now to unblock other proofs.
#push-options "--warn_error -271"
let rec bfs_reach_list_sound (edges: list edge) (frontier: list nat) (visited: list nat) (fuel: nat) (w: nat)
  : Lemma (requires mem w (bfs_reach_list edges frontier visited fuel))
          (ensures mem w visited \/ (exists u. mem u frontier /\ reachable edges u w))
          (decreases %[fuel; List.Tot.length frontier])
  = admit() // TODO: Complete this proof
#pop-options

// Corollary: same_component_dec is sound
let same_component_dec_sound (edges: list edge) (u v: nat)
  : Lemma (requires same_component_dec edges u v = true)
          (ensures same_component edges u v)
  = if u = v then
      same_component_reflexive edges u
    else begin
      let n = max_vertex_in_edges edges + 1 in
      let visited = bfs_reach_list edges [u] [] n in
      assert (mem v visited);
      bfs_reach_list_sound edges [u] [] n v;
      // From soundness: v is in [], or reachable from someone in [u]
      // v is not in [], so v must be reachable from u
      assert (mem u [u]);
      assert (reachable edges u v)
    end

// Helper: if mem x (vertices_in_component edges v n i), then same_component_dec edges v x
let rec vertices_in_component_mem (edges: list edge) (v: nat) (n: nat) (i: nat{i <= n}) (x: nat)
  : Lemma (requires mem x (vertices_in_component edges v n i))
          (ensures same_component_dec edges v x = true)
          (decreases (n - i))
  = if i >= n then ()
    else if same_component_dec edges v i then begin
      if x = i then ()
      else vertices_in_component_mem edges v n (i + 1) x
    end else
      vertices_in_component_mem edges v n (i + 1) x

// Helper: A component in components is always component_of some seed vertex
let rec build_components_structure (edges: list edge) (n: nat) (i: nat{i <= n}) (acc: list (list nat))
  : Lemma (ensures forall comp. mem comp (build_components edges n i acc) ==>
                   (mem comp acc \/ (exists seed. comp == component_of edges seed n)))
          (decreases (n - i))
  = if i >= n then ()
    else begin
      if in_some_component i acc then
        build_components_structure edges n (i + 1) acc
      else begin
        let new_comp = component_of edges i n in
        build_components_structure edges n (i + 1) (new_comp :: acc)
      end
    end

let components_structure (edges: list edge) (n: nat)
  : Lemma (ensures forall comp. mem comp (components edges n) ==>
                   exists seed. comp == component_of edges seed n)
  = if n = 0 then ()
    else build_components_structure edges n 0 []

// If two vertices are in the same component, they satisfy same_component predicate
let lemma_component_implies_same (edges: list edge) (u v: nat) (n: nat) (comp: list nat)
  : Lemma (requires mem u comp /\ mem v comp /\ mem comp (components edges n))
          (ensures same_component edges u v)
  = components_structure edges n;
    // comp is component_of edges seed n for some seed
    eliminate exists seed. comp == component_of edges seed n
    returns same_component edges u v
    with _. begin
      assert (comp == component_of edges seed n);
      assert (mem u (component_of edges seed n));
      assert (mem v (component_of edges seed n));
      vertices_in_component_mem edges seed n 0 u;
      vertices_in_component_mem edges seed n 0 v;
      same_component_dec_sound edges seed u;
      same_component_dec_sound edges seed v;
      same_component_symmetric edges seed u;
      same_component_transitive edges u seed v
    end

// If two vertices are in different components, adding an edge between them merges components
let lemma_different_components (edges: list edge) (u v: nat) (n: nat)
  : Lemma (requires ~(same_component edges u v) /\ u < n /\ v < n)
          (ensures ~(mem u (component_of edges v n)))
  = // Proof by contradiction
    if mem u (component_of edges v n) then begin
      // u is in component_of edges v n
      // component_of edges v n = vertices_in_component edges v n 0
      vertices_in_component_mem edges v n 0 u;
      // So same_component_dec edges v u = true
      same_component_dec_sound edges v u;
      // So same_component edges v u
      same_component_symmetric edges v u;
      // So same_component edges u v - contradiction!
      assert false
    end else ()

(*** Edge Sorting ***)

// Sort edges by weight (ascending order)
// Using insertion sort for simplicity
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

// Properties of sorted edges
let rec insert_edge_mem (e e': edge) (sorted: list edge)
  : Lemma (ensures mem_edge e' (insert_edge e sorted) <==>
                   (edge_eq e e' || mem_edge e' sorted))
  = match sorted with
    | [] -> ()
    | hd :: tl ->
      if e.w <= hd.w then ()
      else insert_edge_mem e e' tl

let rec sort_edges_mem (e: edge) (edges: list edge)
  : Lemma (ensures mem_edge e (sort_edges edges) <==> mem_edge e edges)
          (decreases edges)
  = match edges with
    | [] -> ()
    | hd :: tl ->
      sort_edges_mem e tl;
      insert_edge_mem hd e (sort_edges tl)

// Sorted list contains same edges as original
let rec sort_edges_subset_forward (edges: list edge)
  : Lemma (ensures subset_edges (sort_edges edges) edges)
          (decreases edges)
  = match edges with
    | [] -> ()
    | e :: rest ->
      sort_edges_subset_forward rest;
      // Need to show: every edge in (insert_edge e (sort_edges rest)) is in (e :: rest)
      let rec insert_forward (e: edge) (sorted: list edge) (orig: list edge)
        : Lemma (requires subset_edges sorted orig)
                (ensures subset_edges (insert_edge e sorted) (e :: orig))
                (decreases sorted)
        = match sorted with
          | [] -> 
            mem_edge_hd e orig
          | hd :: tl ->
            if e.w <= hd.w then begin
              mem_edge_hd e orig;
              subset_edges_cons (hd :: tl) e orig
            end else begin
              insert_forward e tl orig;
              assert (mem_edge hd sorted);
              mem_edge_subset hd sorted orig;
              subset_edges_cons (insert_edge e tl) hd (e :: orig)
            end
      in
      insert_forward e (sort_edges rest) rest

let rec sort_edges_subset_backward (edges: list edge)
  : Lemma (ensures subset_edges edges (sort_edges edges))
          (decreases edges)
  = match edges with
    | [] -> ()
    | e :: rest ->
      sort_edges_subset_backward rest;
      // Need: subset_edges (e :: rest) (insert_edge e (sort_edges rest))
      // We have: subset_edges rest (sort_edges rest)
      // We need to show: 
      // 1. mem_edge e (insert_edge e (sort_edges rest))
      // 2. subset_edges rest (insert_edge e (sort_edges rest))
      
      // Part 1: e is in insert_edge e sorted for any sorted
      let rec e_in_insert (e: edge) (sorted: list edge)
        : Lemma (ensures mem_edge e (insert_edge e sorted))
                (decreases sorted)
        = match sorted with
          | [] -> mem_edge_hd e []
          | hd :: tl ->
            if e.w <= hd.w then mem_edge_hd e (hd :: tl)
            else e_in_insert e tl
      in
      e_in_insert e (sort_edges rest);
      
      // Part 2: rest ⊆ sort_edges rest ⊆ insert_edge e (sort_edges rest)
      let rec sorted_subset_insert (e: edge) (sorted: list edge)
        : Lemma (ensures subset_edges sorted (insert_edge e sorted))
                (decreases sorted)
        = match sorted with
          | [] -> ()
          | hd :: tl ->
            if e.w <= hd.w then begin
              subset_edges_reflexive (hd :: tl);
              subset_edges_cons (hd :: tl) e (hd :: tl)
            end else begin
              sorted_subset_insert e tl;
              subset_edges_cons tl hd (insert_edge e tl)
            end
      in
      sorted_subset_insert e (sort_edges rest);
      subset_edges_transitive rest (sort_edges rest) (insert_edge e (sort_edges rest))

let sort_edges_subset (edges: list edge)
  : Lemma (ensures subset_edges (sort_edges edges) edges /\
                   subset_edges edges (sort_edges edges))
  = sort_edges_subset_forward edges;
    sort_edges_subset_backward edges

// If edges are sorted, elements appear in non-decreasing weight order
let rec is_sorted_by_weight (edges: list edge) : bool =
  match edges with
  | [] -> true
  | [e] -> true
  | e1 :: e2 :: rest -> e1.w <= e2.w && is_sorted_by_weight (e2 :: rest)

let rec insert_maintains_sorted (e: edge) (sorted: list edge)
  : Lemma (requires is_sorted_by_weight sorted)
          (ensures is_sorted_by_weight (insert_edge e sorted))
  = match sorted with
    | [] -> ()
    | hd :: tl ->
      if e.w <= hd.w then ()
      else begin
        insert_maintains_sorted e tl;
        match tl with
        | [] -> ()
        | hd' :: tl' -> ()
      end

let rec sort_edges_sorted (edges: list edge)
  : Lemma (ensures is_sorted_by_weight (sort_edges edges))
  = match edges with
    | [] -> ()
    | e :: rest ->
      sort_edges_sorted rest;
      insert_maintains_sorted e (sort_edges rest)

(*** Pure Kruskal Step ***)

// Single step of Kruskal: try to add next edge if it connects different components
// This is a pure specification function - the is_forest check is implicit
let kruskal_step (e: edge) (forest: list edge) (n: nat) : list edge =
  if e.u < n && e.v < n && 
     not (same_component_dec forest e.u e.v) &&
     not (mem_edge e forest)
  then e :: forest
  else forest

// Process all edges in order
let rec kruskal_process (sorted_edges: list edge) (forest: list edge) (n: nat) 
  : Tot (list edge) (decreases sorted_edges)
  = match sorted_edges with
    | [] -> forest
    | e :: rest ->
      let forest' = kruskal_step e forest n in
      kruskal_process rest forest' n

(*** Pure Kruskal Algorithm ***)

// Main Kruskal algorithm: sort edges, then greedily add safe edges
let pure_kruskal (g: graph) : list edge =
  let sorted = sort_edges g.edges in
  kruskal_process sorted [] g.n

(*** Correctness Properties ***)

// Property 1: Kruskal maintains forest invariant
let lemma_kruskal_step_preserves_forest (e: edge) (forest: list edge) (n: nat)
  : Lemma (requires is_forest forest n)
          (ensures is_forest (kruskal_step e forest n) n)
  = // If edge is added, it connects different components, so no cycle created
    // kruskal_step only adds e if ~(same_component_dec forest e.u e.v)
    // This implies ~(same_component forest e.u e.v) = ~(reachable forest e.u e.v)
    // Adding edge between different components preserves acyclicity
    admit() // Needs: ~(reachable forest u v) ==> acyclic n (e :: forest)

let rec lemma_kruskal_process_preserves_forest 
    (sorted_edges: list edge) (forest: list edge) (n: nat)
  : Lemma (requires is_forest forest n)
          (ensures is_forest (kruskal_process sorted_edges forest n) n)
          (decreases sorted_edges)
  = match sorted_edges with
    | [] -> ()
    | e :: rest ->
      lemma_kruskal_step_preserves_forest e forest n;
      lemma_kruskal_process_preserves_forest rest (kruskal_step e forest n) n

// Property 2: All edges in result are from the graph
let lemma_kruskal_step_edges_from_graph 
    (e: edge) (forest: list edge) (graph_edges: list edge) (n: nat)
  : Lemma (requires subset_edges forest graph_edges /\ mem_edge e graph_edges)
          (ensures subset_edges (kruskal_step e forest n) graph_edges)
  = ()

let rec lemma_kruskal_process_edges_from_graph 
    (sorted_edges: list edge) (forest: list edge) (graph_edges: list edge) (n: nat)
  : Lemma (requires subset_edges forest graph_edges /\ 
                    subset_edges sorted_edges graph_edges)
          (ensures subset_edges (kruskal_process sorted_edges forest n) graph_edges)
          (decreases sorted_edges)
  = match sorted_edges with
    | [] -> ()
    | e :: rest ->
      lemma_kruskal_step_edges_from_graph e forest graph_edges n;
      lemma_kruskal_process_edges_from_graph rest (kruskal_step e forest n) graph_edges n

// Property 3: Safe Edge Property via Cut Property
// When Kruskal adds an edge (u,v), it's because u and v are in different components.
// This means the cut S = {vertices reachable from u} separates u from v.
// The cut respects current forest A (no edge in A crosses the cut by definition of components).
// Since edges are processed in sorted order, (u,v) is the lightest edge seen so far
// that crosses this particular cut.

let lemma_kruskal_step_safe_edge (g: graph) (e: edge) (forest: list edge) 
  : Lemma (requires 
            e.u < g.n /\ e.v < g.n /\
            mem_edge e g.edges /\
            is_forest forest g.n /\
            subset_edges forest g.edges /\
            ~(same_component forest e.u e.v) /\
            not (mem_edge e forest) /\
            // Edges before e in sorted order have higher or equal weight
            (forall (e': edge). 
              mem_edge e' g.edges /\ 
              not (mem_edge e' forest) /\ 
              ~(same_component forest e'.u e'.v) ==>
              e.w <= e'.w) /\
            // Forest is subset of some MST
            (exists (mst: list edge). is_mst g mst /\ subset_edges forest mst))
          (ensures 
            // After adding e, still subset of some MST
            (exists (mst: list edge). is_mst g mst /\ subset_edges (e :: forest) mst))
  = // Define cut: S = component containing e.u
    // We use the decidable version for the cut definition
    let s : cut = fun v -> same_component_dec forest e.u v in
    
    // The edge e crosses this cut
    // From precondition: ~(same_component forest e.u e.v)
    // This means same_component_dec forest e.u e.v should be false
    // and same_component_dec forest e.u e.u should be true (by reflexivity)
    admit(); // Would need: same_component_dec correct wrt same_component
    assert (crosses_cut e s);
    
    // The cut respects forest A
    // (because edges in forest don't connect different components)
    let rec lemma_forest_respects_own_cut (f: list edge) (u: nat)
      : Lemma (ensures respects f (fun v -> same_component_dec f u v))
      = admit() // All edges in f connect vertices in same component
    in
    lemma_forest_respects_own_cut forest e.u;
    
    // Edge e is light: it has minimum weight among edges crossing the cut
    // that haven't been added yet
    // Since edges are processed in sorted order, e.w <= e'.w for any
    // edge e' that crosses this cut and isn't in forest
    let lemma_edge_is_light (e: edge) (g: graph) (forest: list edge) (s: cut)
      : Lemma (requires 
                mem_edge e g.edges /\
                crosses_cut e s /\
                (forall (e': edge).
                  mem_edge e' g.edges /\
                  not (mem_edge e' forest) /\
                  crosses_cut e' s ==>
                  e.w <= e'.w))
              (ensures is_light_edge e s g \/ 
                       (exists (e': edge). 
                         mem_edge e' forest /\ 
                         crosses_cut e' s /\ 
                         e'.w < e.w))
      = admit() // Either e is light, or there's a lighter edge already in forest
    in
    
    // Since cut respects forest, no edge in forest crosses the cut,
    // so e must be light (or tied for lightest)
    // Apply cut property: A ∪ {e} ⊆ some MST
    cut_property g forest e s

(*** Main Correctness Theorem ***)

// Kruskal's algorithm produces a spanning tree
let theorem_kruskal_produces_spanning_tree (g: graph)
  : Lemma (requires g.n > 0 /\ 
                    // Graph is connected
                    all_connected g.n g.edges /\
                    // There exists an MST (i.e., graph is valid)
                    (exists (mst: list edge). is_mst g mst))
          (ensures (let result = pure_kruskal g in
                    is_spanning_tree g result))
  = let result = pure_kruskal g in
    let sorted = sort_edges g.edges in
    
    // Part 1: Result is a forest (acyclic)
    lemma_kruskal_process_preserves_forest sorted [] g.n;
    
    // Part 2: All edges from graph
    sort_edges_subset g.edges;
    lemma_kruskal_process_edges_from_graph sorted [] g.edges g.n;
    
    // Part 3: Result connects all vertices
    // This requires showing that Kruskal adds enough edges
    // and that these edges connect all components
    admit() // Complex: needs to show n-1 edges added and they form spanning tree
    
    // Part 4: Result has exactly n-1 edges
    // Follows from: algorithm stops when all vertices are in one component
    // and each edge added reduces component count by 1
    

// Kruskal's algorithm produces a minimum spanning tree
let theorem_kruskal_produces_mst (g: graph)
  : Lemma (requires g.n > 0 /\ 
                    all_connected g.n g.edges /\
                    (exists (mst: list edge). is_mst g mst))
          (ensures (let result = pure_kruskal g in
                    is_mst g result))
  = theorem_kruskal_produces_spanning_tree g;
    
    // The MST property follows from:
    // 1. Result is a spanning tree (proven above)
    // 2. Each edge added is safe (via cut property)
    // 3. Safe edges maintain "subset of some MST" invariant
    // 4. Final spanning tree that's subset of MST must be MST
    
    let result = pure_kruskal g in
    
    // Induction over edge additions showing "subset of MST" invariant
    admit() // Would need to show: each step maintains subset_edges result some_mst

(*** Additional Helper Properties ***)

// Number of components decreases or stays same when adding edge
let lemma_edge_addition_reduces_components (edges: list edge) (e: edge) (n: nat)
  : Lemma (requires is_forest edges n /\ 
                    e.u < n /\ e.v < n /\
                    ~(same_component edges e.u e.v) /\
                    is_forest (e :: edges) n)
          (ensures length (components (e :: edges) n) <= length (components edges n))
  = admit()

/// Helper: bfs_reach_list with empty edges and singleton frontier returns [u]
let bfs_reach_empty_edges (u: nat)
  : Lemma (ensures bfs_reach_list [] [u] [] 1 == [u])
  = assert (edge_neighbors ([] #edge) u == []);
    List.Tot.Properties.append_nil_l ([] #nat)

/// Helper: same_component_dec with no edges only returns true for equal vertices
let same_component_dec_empty (u v: nat)
  : Lemma (ensures same_component_dec [] u v = (u = v))
  = if u = v then ()
    else begin
      bfs_reach_empty_edges u;
      assert (bfs_reach_list [] [u] [] 1 == [u]);
      assert (mem v [u] = (v = u))
    end

/// Helper: vertices_in_component with empty edges returns [v] when v < n
#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
let rec vertices_in_component_empty (v: nat) (n: nat) (i: nat{i <= n})
  : Lemma (requires v < n)
          (ensures vertices_in_component [] v n i == (if i <= v && v < n then [v] else []))
          (decreases (n - i))
  = same_component_dec_empty v i;
    if i >= n then ()
    else begin
      vertices_in_component_empty v n (i + 1);
      if i = v then begin
        assert (same_component_dec [] v i = true)
      end else begin
        assert (same_component_dec [] v i = false)
      end
    end
#pop-options

/// Helper: component_of with empty edges is [v] when v < n
let component_of_empty (v: nat) (n: nat)
  : Lemma (requires v < n)
          (ensures component_of [] v n == [v])
  = vertices_in_component_empty v n 0

/// Helper: vertex j is not in component_of [] i n when i <> j and both < n
let not_in_different_component_empty (i j: nat) (n: nat)
  : Lemma (requires i < n /\ j < n /\ i <> j)
          (ensures ~(mem j (component_of [] i n)))
  = component_of_empty i n

/// Helper: build_components with empty edges produces n singletons
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec build_components_empty_length (n: nat) (i: nat{i <= n})
                                      (acc: list (list nat))
  : Lemma (requires
             length acc == i /\
             (forall (j: nat{j < i}). mem [j] acc) /\
             (forall (c: list nat). mem c acc ==> (exists (j: nat{j < i}). c == [j])) /\
             (forall (c: list nat). mem c acc ==> ~(mem i c)))
          (ensures length (build_components [] n i acc) == n)
          (decreases (n - i))
  = if i >= n then ()
    else begin
      component_of_empty i n;
      in_some_component_false i acc;
      assert (in_some_component i acc = false);
      let new_comp = component_of [] i n in
      assert (new_comp == [i]);
      let acc' = new_comp :: acc in
      assert (length acc' == i + 1);
      // Part 1: forall j < i+1, [j] in acc'
      let aux1 (j: nat{j < i + 1}) : Lemma (mem [j] acc')
        = if j = i then () else ()
      in
      FStar.Classical.forall_intro aux1;
      // Part 2: all elements of acc' are singletons for vertices < i+1
      let aux2 (c: list nat) : Lemma (requires mem c acc') 
                                     (ensures exists (j: nat{j < i + 1}). c == [j])
        = if c = [i] then ()
          else begin
            assert (mem c acc);
            eliminate exists (j: nat{j < i}). c == [j]
            returns exists (j: nat{j < i + 1}). c == [j]
            with _. ()
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux2);
      // Part 3: i+1 is not in any component in acc'
      if i + 1 <= n then begin
        let aux3 (c: list nat) : Lemma (requires mem c acc')
                                       (ensures ~(mem (i + 1) c))
          = if c = [i] then ()
            else begin
              assert (mem c acc);
              eliminate exists (j: nat{j < i}). c == [j]
              returns ~(mem (i + 1) c)
              with _. ()
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux3)
      end;
      build_components_empty_length n (i + 1) acc'
    end
#pop-options

// Initially n components (each vertex is its own component)
let lemma_initial_components (n: nat)
  : Lemma (requires n > 0)
          (ensures length (components [] n) = n)
  = build_components_empty_length n 0 []

// Final spanning tree has 1 component
let lemma_spanning_tree_one_component (g: graph) (t: list edge)
  : Lemma (requires is_spanning_tree g t)
          (ensures length (components t g.n) = 1)
  = admit()

// With n vertices and 1 component, need exactly n-1 edges for tree
let lemma_tree_edge_count (n: nat) (t: list edge)
  : Lemma (requires n > 0 /\
                    is_forest t n /\
                    length (components t n) = 1)
          (ensures length t = n - 1)
  = admit()
