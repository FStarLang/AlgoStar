(*
   CLRS Chapter 23: Kruskal's Algorithm - Connected Components
   
   This module provides BFS-based connected component computation and
   related graph reachability lemmas used by Kruskal's algorithm.
   Key components:
   1. Forest/acyclic edge set definition
   2. Same-component relation and path properties
   3. BFS reachability computation (soundness and completeness)
   4. Component building and structural properties
*)

module CLRS.Ch23.Kruskal.Components

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
#push-options "--fuel 3 --ifuel 1 --z3rlimit 5"
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
#push-options "--fuel 3 --ifuel 1 --z3rlimit 5"
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

// Helper: forall version of mem_append
let mem_append_forall (#a: eqtype) (l1 l2: list a)
  : Lemma (forall (x:a). mem x (l1 @ l2) <==> (mem x l1 \/ mem x l2))
  = let aux (x:a) : Lemma (mem x (l1 @ l2) <==> (mem x l1 \/ mem x l2))
              [SMTPat (mem x (l1 @ l2))]
    = mem_append x l1 l2
    in
    ()

// Helper lemma: if u is a neighbor of v and u reaches w, then v reaches w
let neighbor_reaches (edges: list edge) (v u w: nat)
  : Lemma (requires mem u (edge_neighbors edges v) /\ reachable edges u w)
          (ensures reachable edges v w)
  =
    edge_neighbors_sound edges v u;
    eliminate exists e. mem_edge e edges /\ ((e.u = v /\ e.v = u) \/ (e.v = v /\ e.u = u))
    returns reachable edges v w
    with _. (
      edge_gives_reachability edges v u e;
      reachability_transitive edges v u w
    )

// Key lemma: BFS soundness - every vertex in result is either in visited or reachable from frontier  
#push-options "--fuel 1 --ifuel 1 --z3rlimit 5"
let rec bfs_reach_list_sound (edges: list edge) (frontier: list nat) (visited: list nat) (fuel: nat) (w: nat)
  : Lemma (requires mem w (bfs_reach_list edges frontier visited fuel))
          (ensures mem w visited \/ (exists u. mem u frontier /\ reachable edges u w))
          (decreases %[fuel; List.Tot.length frontier])
  = if fuel = 0 then ()  
    else match frontier with
    | [] -> ()  
    | v :: rest ->
      if mem v visited then
        bfs_reach_list_sound edges rest visited fuel w
      else (
        let visited' = v :: visited in
        let new_neighbors = edge_neighbors edges v in
        let new_frontier = List.Tot.append rest new_neighbors in
        
        bfs_reach_list_sound edges new_frontier visited' (fuel - 1) w;
        
        // After IH: mem w visited' \/ (exists u. mem u new_frontier /\ reachable edges u w)
        // Split new_frontier
        mem_append_forall rest new_neighbors;
        
        // Case analysis
        if w = v then (
          same_component_reflexive edges v
        ) else (
          // w ≠ v
          // For u in new_neighbors: if u reaches w, then v reaches w
          let aux (u:nat) : Lemma 
            (requires mem u new_neighbors /\ reachable edges u w)
            (ensures reachable edges v w)
            [SMTPat (mem u new_neighbors); SMTPat (reachable edges u w)]
          =
            neighbor_reaches edges v u w
          in
          ()
        )
      )
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

(*** BFS Completeness ***)

// All vertices returned by edge_neighbors have index ≤ max_vertex_in_edges
let rec edge_neighbors_bounded (edges: list edge) (v w: nat)
  : Lemma (requires mem w (edge_neighbors edges v))
          (ensures w <= max_vertex_in_edges edges)
          (decreases edges)
  = match edges with
    | [] -> ()
    | e :: rest ->
      let ns = edge_neighbors rest v in
      if e.u = v then
        (if w = e.v then () else edge_neighbors_bounded rest v w)
      else if e.v = v then
        (if w = e.u then () else edge_neighbors_bounded rest v w)
      else
        edge_neighbors_bounded rest v w

// All vertices returned by edge_neighbors are endpoints of edges containing v
let edge_neighbors_are_adjacent (edges: list edge) (v w: nat)
  : Lemma (requires mem w (edge_neighbors edges v))
          (ensures exists (e: edge). mem_edge e edges /\
                    ((e.u = v /\ e.v = w) \/ (e.v = v /\ e.u = w)))
  = edge_neighbors_sound edges v w

// BFS visited elements always remain in the result
let rec bfs_visited_in_result
    (edges: list edge) (frontier: list nat) (visited: list nat) (fuel: nat) (w: nat)
  : Lemma (requires mem w visited)
          (ensures mem w (bfs_reach_list edges frontier visited fuel))
          (decreases %[fuel; List.Tot.length frontier])
  = if fuel = 0 then ()
    else match frontier with
    | [] -> ()
    | v :: rest ->
      if mem v visited then
        bfs_visited_in_result edges rest visited fuel w
      else
        bfs_visited_in_result edges (List.Tot.append rest (edge_neighbors edges v)) (v :: visited) (fuel - 1) w

// Pigeonhole helper: noRepeats list with bounded elements has bounded length
let rec noRepeats_bounded_length (l: list nat) (max: nat)
  : Lemma (requires noRepeats l /\ (forall (v:nat). mem v l ==> v <= max))
          (ensures length l <= max + 1)
          (decreases max)
  = match l with
    | [] -> ()
    | _ ->
      if max = 0 then begin
        let hd :: tl = l in
        assert (hd = 0);
        match tl with
        | [] -> ()
        | v :: _ -> assert (v <= 0); assert (v = 0); assert (mem 0 tl)
          // contradicts noRepeats (hd :: tl) since hd = 0
      end else if not (mem max l) then begin
        // All elements ≤ max but none = max, so all ≤ max - 1
        let aux (v:nat) : Lemma (requires mem v l) (ensures v <= max - 1) = () in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
        noRepeats_bounded_length l (max - 1)
      end else begin
        // max ∈ l. Remove first occurrence.
        let rec remove_first_props (l: list nat) (x: nat)
          : Lemma (requires noRepeats l /\ mem x l)
                  (ensures (let l' = List.Tot.filter (fun v -> v <> x) l in
                            noRepeats l' /\
                            length l' = length l - 1 /\
                            ~(mem x l') /\
                            (forall (v:nat). mem v l' ==> mem v l)))
                  (decreases l)
          = match l with
            | [] -> ()
            | hd :: tl ->
              if hd = x then begin
                // x = hd, not (mem hd tl) from noRepeats
                // filter removes hd, rest of filter is filter on tl
                // but since hd ∉ tl, filter on tl doesn't remove anything more
                assert (not (mem x tl));
                // filter (fun v -> v <> x) (hd :: tl) = filter (fun v -> v <> x) tl
                // Since no element of tl = x = hd, filter is identity on tl
                let rec filter_identity (tl: list nat) (x: nat)
                  : Lemma (requires ~(mem x tl))
                          (ensures List.Tot.filter (fun v -> v <> x) tl == tl)
                          (decreases tl)
                  = match tl with
                    | [] -> ()
                    | h :: t -> filter_identity t x
                in
                filter_identity tl x;
                assert (List.Tot.filter (fun v -> v <> x) l == tl)
              end else begin
                remove_first_props tl x;
                let tl' = List.Tot.filter (fun v -> v <> x) tl in
                assert (List.Tot.filter (fun v -> v <> x) l == hd :: tl');
                assert (noRepeats tl');
                // hd ∉ tl, and tl' ⊆ tl, so hd ∉ tl'
                assert (~(mem hd tl));
                let rec filter_mem_sub (l: list nat) (f: nat -> bool) (x: nat)
                  : Lemma (requires mem x (List.Tot.filter f l))
                          (ensures mem x l)
                          (decreases l)
                  = match l with
                    | [] -> ()
                    | _ :: t -> if mem x (List.Tot.filter f t) then filter_mem_sub t f x
                in
                let aux () : Lemma (~(mem hd tl'))
                  = if mem hd tl' then filter_mem_sub tl (fun v -> v <> x) hd
                in
                aux ()
              end
        in
        remove_first_props l max;
        let l' = List.Tot.filter (fun v -> v <> max) l in
        // l' has all elements ≤ max - 1 (they're ≤ max and ≠ max)
        let aux (v:nat) : Lemma (requires mem v l') (ensures v <= max - 1) = () in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
        noRepeats_bounded_length l' (max - 1)
        // length l' ≤ max, so length l = length l' + 1 ≤ max + 1 ✓
      end

// Helper: filter for inequality preserves noRepeats
let rec filter_neq_noRepeats (l: list nat) (x: nat)
  : Lemma (requires noRepeats l)
          (ensures noRepeats (List.Tot.filter (fun v -> v <> x) l))
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      filter_neq_noRepeats tl x;
      if hd <> x then begin
        // Need: not (mem hd (filter (fun v -> v <> x) tl))
        // From noRepeats: not (mem hd tl)
        // filter ⊆ tl membership-wise
        let rec filter_mem_sub2 (l: list nat) (f: nat -> bool) (y: nat)
          : Lemma (requires mem y (List.Tot.filter f l))
                  (ensures mem y l)
                  (decreases l)
          = match l with
            | [] -> ()
            | _ :: t -> if mem y (List.Tot.filter f t) then filter_mem_sub2 t f y
        in
        if mem hd (List.Tot.filter (fun v -> v <> x) tl) then
          filter_mem_sub2 tl (fun v -> v <> x) hd
      end

// Helper: filter for inequality removes exactly one element when present with noRepeats
let rec filter_neq_length (l: list nat) (x: nat)
  : Lemma (requires noRepeats l /\ mem x l)
          (ensures length (List.Tot.filter (fun v -> v <> x) l) = length l - 1)
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      if hd = x then begin
        // filter removes hd, and since hd ∉ tl, filter is identity on tl
        let rec filter_identity_when_absent (tl: list nat) (x: nat)
          : Lemma (requires ~(mem x tl))
                  (ensures List.Tot.filter (fun v -> v <> x) tl == tl)
                  (decreases tl)
          = match tl with
            | [] -> ()
            | _ :: t -> filter_identity_when_absent t x
        in
        filter_identity_when_absent tl x
      end else
        filter_neq_length tl x

// Helper: filter membership
let rec filter_neq_mem (l: list nat) (x y: nat)
  : Lemma (ensures mem y (List.Tot.filter (fun v -> v <> x) l) <==>
                   (mem y l /\ y <> x))
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: tl -> filter_neq_mem tl x y

// Pigeonhole consequence: all values in range are covered
let rec noRepeats_covers_all (visited: list nat) (max: nat) (w: nat)
  : Lemma (requires noRepeats visited /\ length visited > max /\
                    (forall (v:nat). mem v visited ==> v <= max) /\
                    w <= max)
          (ensures mem w visited)
          (decreases max)
  = if max = 0 then begin
      // w = 0. length > 0, so visited is non-empty. All elements ≤ 0 = 0.
      let hd :: _ = visited in
      assert (hd = 0)
    end else begin
      if w = max then begin
        // Need mem max visited. Prove by contradiction.
        if not (mem max visited) then begin
          let aux (v:nat) : Lemma (requires mem v visited) (ensures v <= max - 1) = () in
          FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
          noRepeats_bounded_length visited (max - 1)
          // length visited ≤ max, but length visited > max. Contradiction.
        end
      end else begin
        // w < max. 
        assert (w <= max - 1);
        if not (mem max visited) then begin
          // All elements < max, so ≤ max - 1. IH applies.
          let aux (v:nat) : Lemma (requires mem v visited) (ensures v <= max - 1) = () in
          FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
          noRepeats_covers_all visited (max - 1) w
        end else begin
          // max ∈ visited. Filter it out.
          let visited' = List.Tot.filter (fun (v:nat) -> v <> max) visited in
          filter_neq_noRepeats visited max;
          filter_neq_length visited max;
          // length visited' = length visited - 1 > max - 1
          // All elements of visited' ≤ max and ≠ max, so ≤ max - 1
          let aux (v:nat) : Lemma (requires mem v visited') (ensures v <= max - 1) =
            filter_neq_mem visited max v
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
          noRepeats_covers_all visited' (max - 1) w;
          // w ∈ visited'. Since visited' ⊆ visited: w ∈ visited.
          filter_neq_mem visited max w
        end
      end
    end

// BFS well-formedness: every visited vertex has its neighbors in visited ∪ frontier
let bfs_well_formed (edges: list edge) (frontier visited: list nat) : prop =
  forall (v: nat). mem v visited ==>
    forall (w: nat). mem w (edge_neighbors edges v) ==>
      mem w visited \/ mem w frontier

// Main BFS completeness invariant:
// If well-formed, noRepeats, bounded, and sufficient fuel,
// then the result is neighbor-closed and contains all frontier + visited.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 5"
let rec bfs_complete_invariant
    (edges: list edge) (frontier: list nat) (visited: list nat) (fuel: nat)
  : Lemma
    (requires
      bfs_well_formed edges frontier visited /\
      noRepeats visited /\
      (forall (v: nat). mem v visited ==> v <= max_vertex_in_edges edges) /\
      (forall (v: nat). mem v frontier ==> v <= max_vertex_in_edges edges) /\
      fuel + length visited >= max_vertex_in_edges edges + 1)
    (ensures
      (let result = bfs_reach_list edges frontier visited fuel in
       // Result contains all visited and frontier elements
       (forall (v: nat). mem v visited ==> mem v result) /\
       (forall (v: nat). mem v frontier ==> mem v result) /\
       // Result is neighbor-closed
       (forall (v: nat). mem v result ==>
         forall (w: nat). mem w (edge_neighbors edges v) ==> mem w result)))
    (decreases %[fuel; List.Tot.length frontier])
  = if fuel = 0 then begin
      let max = max_vertex_in_edges edges in
      assert (length visited >= max + 1);
      introduce forall (v: nat). mem v visited ==>
        (forall (w: nat). mem w (edge_neighbors edges v) ==> mem w visited)
      with introduce _ ==> _ with _. begin
        introduce forall (w: nat). mem w (edge_neighbors edges v) ==> mem w visited
        with introduce _ ==> _ with _. begin
          edge_neighbors_bounded edges v w;
          noRepeats_covers_all visited max w
        end
      end;
      introduce forall (v: nat). mem v frontier ==> mem v visited
      with introduce _ ==> _ with _.
        noRepeats_covers_all visited max v
    end
    else match frontier with
    | [] -> ()
    | v :: rest ->
      if mem v visited then begin
        assert (bfs_well_formed edges rest visited);
        bfs_complete_invariant edges rest visited fuel;
        // v ∈ visited ⊆ result by IH. Elements of rest ⊆ result by IH.
        // So all of (v :: rest) ⊆ result.
        ()
      end else begin
        let visited' = v :: visited in
        let new_neighbors = edge_neighbors edges v in
        let frontier' = List.Tot.append rest new_neighbors in

        assert (noRepeats visited');

        let aux_bounded (u: nat)
          : Lemma (requires mem u visited')
                  (ensures u <= max_vertex_in_edges edges)
          = ()
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_bounded);

        let aux_frontier (u: nat)
          : Lemma (requires mem u frontier')
                  (ensures u <= max_vertex_in_edges edges)
          = mem_append u rest new_neighbors;
            if mem u rest then ()
            else edge_neighbors_bounded edges v u
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_frontier);

        introduce forall (u: nat). mem u visited' ==>
          (forall (w: nat). mem w (edge_neighbors edges u) ==> (mem w visited' \/ mem w frontier'))
        with introduce _ ==> _ with _. begin
          introduce forall (w: nat). mem w (edge_neighbors edges u) ==> (mem w visited' \/ mem w frontier')
          with introduce _ ==> _ with _. begin
            if u = v then
              mem_append w rest new_neighbors
            else if mem w visited then ()
            else if w = v then ()
            else mem_append w rest new_neighbors
          end
        end;
        assert (bfs_well_formed edges frontier' visited');

        assert (fuel - 1 + length visited' >= max_vertex_in_edges edges + 1);

        bfs_complete_invariant edges frontier' visited' (fuel - 1);
        // By IH: visited' ⊆ result, frontier' ⊆ result, neighbor-closed
        // v ∈ visited' ⊆ result. ✓
        // For w ∈ rest: w ∈ frontier' ⊆ result. mem_append gives this.
        let aux_rest (w: nat)
          : Lemma (requires mem w rest)
                  (ensures mem w (bfs_reach_list edges frontier' visited' (fuel - 1)))
          = mem_append w rest new_neighbors
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_rest)
      end
#pop-options

// Helper: if there's an edge (x,y) in edges, then y ∈ edge_neighbors edges x
let rec edge_neighbors_complete (edges_list: list edge) (x y: nat) (e: edge)
  : Lemma (requires mem_edge e edges_list /\ ((e.u = x /\ e.v = y) \/ (e.v = x /\ e.u = y)))
          (ensures mem y (edge_neighbors edges_list x))
          (decreases edges_list)
  = match edges_list with
    | [] -> ()
    | hd :: tl ->
      if hd.u = x && hd.v = y then ()
      else if hd.v = x && hd.u = y then ()
      else begin
        if edge_eq e hd then begin
          edge_eq_endpoints e hd
        end else
          edge_neighbors_complete tl x y e
      end

// Path through neighbor-closed set: if x is in the set, so is y
let rec path_in_closed_set
    (edges: list edge) (path: list edge) (x y: nat)
    (s: list nat)
  : Lemma
    (requires
      is_path_from_to path x y /\
      subset_edges path edges /\
      mem x s /\
      (forall (v: nat). mem v s ==>
        forall (w: nat). mem w (edge_neighbors edges v) ==> mem w s))
    (ensures mem y s)
    (decreases path)
  = match path with
    | [] -> ()
    | e :: rest ->
      let next = if e.u = x then e.v else e.u in
      assert (mem_edge e edges);
      edge_neighbors_complete edges x next e;
      assert (mem next s);
      path_in_closed_set edges rest next y s

// Helper: endpoints of edges in the list are bounded by max_vertex_in_edges
let rec mem_edge_max_vertex (e: edge) (edges: list edge)
  : Lemma (requires mem_edge e edges)
          (ensures e.u <= max_vertex_in_edges edges /\ e.v <= max_vertex_in_edges edges)
          (decreases edges)
  = match edges with
    | [] -> ()
    | hd :: tl ->
      if edge_eq e hd then
        edge_eq_endpoints e hd
      else
        mem_edge_max_vertex e tl

// BFS completeness: reachable vertices are found
let same_component_dec_complete (edges: list edge) (u v: nat)
  : Lemma (requires same_component edges u v)
          (ensures same_component_dec edges u v = true)
  = if u = v then ()
    else begin
      let fuel = max_vertex_in_edges edges + 1 in
      let result = bfs_reach_list edges [u] [] fuel in
      eliminate exists (path: list edge). subset_edges path edges /\ is_path_from_to path u v
        returns same_component_dec edges u v = true
        with _. begin
          let e :: _ = path in
          assert (mem_edge e edges);
          assert (e.u = u \/ e.v = u);
          mem_edge_max_vertex e edges;
          assert (u <= max_vertex_in_edges edges);
          assert (bfs_well_formed edges [u] []);
          bfs_complete_invariant edges [u] [] fuel;
          // u ∈ frontier [u] ⊆ result
          assert (mem u result);
          // result is neighbor-closed, so path from u to v gives v ∈ result
          path_in_closed_set edges path u v result
        end
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

