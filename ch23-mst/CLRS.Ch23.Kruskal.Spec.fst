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
#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
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
#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
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

//SNIPPET_START: kruskal_step
// Single step of Kruskal: try to add next edge if it connects different components
// This is a pure specification function - the is_forest check is implicit
let kruskal_step (e: edge) (forest: list edge) (n: nat) : list edge =
  if e.u < n && e.v < n && 
     not (same_component_dec forest e.u e.v) &&
     not (mem_edge e forest)
  then e :: forest
  else forest
//SNIPPET_END: kruskal_step

// Process all edges in order
let rec kruskal_process (sorted_edges: list edge) (forest: list edge) (n: nat) 
  : Tot (list edge) (decreases sorted_edges)
  = match sorted_edges with
    | [] -> forest
    | e :: rest ->
      let forest' = kruskal_step e forest n in
      kruskal_process rest forest' n

(*** Pure Kruskal Algorithm ***)

//SNIPPET_START: pure_kruskal
// Main Kruskal algorithm: sort edges, then greedily add safe edges
let pure_kruskal (g: graph) : list edge =
  let sorted = sort_edges g.edges in
  kruskal_process sorted [] g.n
//SNIPPET_END: pure_kruskal

(*** Correctness Properties ***)

// Property 1: Kruskal maintains forest invariant
let lemma_kruskal_step_preserves_forest (e: edge) (forest: list edge) (n: nat)
  : Lemma (requires is_forest forest n)
          (ensures is_forest (kruskal_step e forest n) n)
  = // kruskal_step adds e only when conditions hold; otherwise returns forest
    if e.u < n && e.v < n &&
       not (same_component_dec forest e.u e.v) &&
       not (mem_edge e forest)
    then begin
      // same_component_dec = false => ~(same_component forest e.u e.v)
      // by contrapositive of same_component_dec_complete
      let cp () : Lemma (requires same_component forest e.u e.v)
                        (ensures same_component_dec forest e.u e.v = true)
        = same_component_dec_complete forest e.u e.v
      in
      FStar.Classical.move_requires cp ();
      assert (~(same_component forest e.u e.v));
      assert (~(reachable forest e.u e.v));
      // Use acyclic_when_unreachable from MST.Spec
      acyclic_when_unreachable n forest e
    end

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
    // same_component_dec forest e.u e.u = true (by definition, since u = u)
    // ~(same_component forest e.u e.v) => same_component_dec forest e.u e.v = false
    // (by contrapositive of same_component_dec_sound)
    let cp_sound () : Lemma (requires same_component_dec forest e.u e.v = true)
                            (ensures same_component forest e.u e.v)
      = same_component_dec_sound forest e.u e.v
    in
    FStar.Classical.move_requires cp_sound ();
    assert (same_component_dec forest e.u e.v = false);
    assert (same_component_dec forest e.u e.u = true);
    assert (crosses_cut e s);
    
    // The cut respects forest A
    // For each edge e' in forest: e' connects two vertices that are
    // reachable from each other via forest edges, hence in the same component.
    // So same_component_dec forest e.u (e'.u) = same_component_dec forest e.u (e'.v)
    // meaning e' doesn't cross the cut.
    let rec lemma_forest_respects_own_cut (f: list edge) (forest_full: list edge) (u: nat)
      : Lemma (requires subset_edges f forest_full)
              (ensures respects f (fun v -> same_component_dec forest_full u v))
              (decreases f)
      = match f with
        | [] -> ()
        | hd :: tl ->
          lemma_forest_respects_own_cut tl forest_full u;
          // hd is in forest_full. hd connects hd.u and hd.v.
          // So same_component forest_full hd.u hd.v (via the single edge hd)
          assert (mem_edge hd forest_full);
          edge_gives_reachability forest_full hd.u hd.v hd;
          // same_component_dec forest_full u hd.u and same_component_dec forest_full u hd.v
          // must have the same truth value (since hd.u and hd.v are connected):
          // Case 1: both true (u reaches hd.u and hd.v)
          // Case 2: both false (u reaches neither hd.u nor hd.v)
          // In either case, crosses_cut hd s = false
          if same_component_dec forest_full u hd.u then begin
            // u reaches hd.u. hd.u reaches hd.v. So u reaches hd.v.
            same_component_dec_sound forest_full u hd.u;
            same_component_transitive forest_full u hd.u hd.v;
            same_component_dec_complete forest_full u hd.v
          end else begin
            // u doesn't reach hd.u.
            // If u reached hd.v, then u reaches hd.u (via hd.v -> hd.u), contradiction
            if same_component_dec forest_full u hd.v then begin
              same_component_dec_sound forest_full u hd.v;
              same_component_symmetric forest_full hd.u hd.v;
              same_component_transitive forest_full u hd.v hd.u;
              same_component_dec_complete forest_full u hd.u
              // Now same_component_dec forest_full u hd.u = true, contradicting the else branch
            end
          end
    in
    subset_edges_reflexive forest;
    lemma_forest_respects_own_cut forest forest e.u;
    
    // Edge e is light: since cut respects forest, no forest edge crosses the cut.
    // Combined with precondition that e.w <= e'.w for all non-forest edges crossing
    // the cut, e is a light edge.
    // is_light_edge requires: forall e'. mem_edge e' g.edges /\ crosses_cut e' s ==> e.w <= e'.w
    // For e' in forest: ~(crosses_cut e' s) (from respects), so vacuously true
    // For e' not in forest: e.w <= e'.w from precondition
    //   But precondition uses ~(same_component forest e'.u e'.v), not crosses_cut e' s
    //   Need: crosses_cut e' s => ~(same_component forest e'.u e'.v) when e' ∉ forest
    //   Actually not exactly... the precondition says:
    //   e.w <= e'.w when e' ∈ g.edges, e' ∉ forest, ~(same_component forest e'.u e'.v)
    //   For light_edge we need: e.w <= e'.w when e' ∈ g.edges, crosses_cut e' s
    //   crosses_cut e' s means same_component_dec forest e.u (e'.u) ≠ same_component_dec forest e.u (e'.v)
    //   Case: e' in forest => doesn't cross cut, vacuous ✓
    //   Case: e' not in forest, crosses cut:
    //     same_component_dec forest e.u (e'.u) ≠ same_component_dec forest e.u (e'.v)
    //     so ~(same_component forest e'.u e'.v):
    //     If same_component forest e'.u e'.v, then 
    //       same_component_dec_complete => same_component_dec forest e.u (e'.u) = true iff same_component_dec forest e.u (e'.v) = true
    //       contradicting the crossing. So ~(same_component forest e'.u e'.v).
    //     Then precondition gives e.w <= e'.w. ✓
    introduce forall (e': edge). mem_edge e' g.edges /\ crosses_cut e' s ==> e.w <= e'.w
    with introduce _ ==> _ with _. begin
      if mem_edge e' forest then begin
        // e' in forest => doesn't cross cut (from respects)
        let rec respects_implies (f: list edge) (e': edge) (s: cut)
          : Lemma (requires respects f s /\ mem_edge e' f)
                  (ensures not (crosses_cut e' s))
                  (decreases f)
          = match f with
            | [] -> ()
            | hd :: tl ->
              if edge_eq e' hd then begin
                edge_eq_endpoints e' hd;
                assert (not (crosses_cut hd s))
              end else
                respects_implies tl e' s
        in
        respects_implies forest e' s
        // e' doesn't cross cut, contradicting precondition crosses_cut e' s = true
      end else begin
        // e' not in forest, crosses cut
        // Need: ~(same_component forest e'.u e'.v)
        // crosses_cut e' s => same_component_dec forest e.u e'.u ≠ same_component_dec forest e.u e'.v
        // If same_component forest e'.u e'.v were true, by same_component_dec_complete
        // we'd have same_component_dec forest e.u e'.u = same_component_dec forest e.u e'.v
        // (both true or both false, since transitivity), contradicting crossing.
        let cp ()
          : Lemma (requires same_component forest e'.u e'.v) (ensures False)
          = if same_component_dec forest e.u e'.u then begin
              same_component_dec_sound forest e.u e'.u;
              same_component_transitive forest e.u e'.u e'.v;
              same_component_dec_complete forest e.u e'.v
            end else begin
              if same_component_dec forest e.u e'.v then begin
                same_component_dec_sound forest e.u e'.v;
                same_component_symmetric forest e'.u e'.v;
                same_component_transitive forest e.u e'.v e'.u;
                same_component_dec_complete forest e.u e'.u
              end
            end
        in
        FStar.Classical.move_requires cp ()
      end
    end;
    assert (is_light_edge e s g);
    // Apply cut property: A ∪ {e} ⊆ some MST
    cut_property g forest e s

(*** Main Correctness Theorem ***)

// Helper: same_component is monotone — adding edges preserves reachability
let same_component_mono (edges: list edge) (e: edge) (u v: nat)
  : Lemma (requires same_component edges u v)
          (ensures same_component (e :: edges) u v)
  = eliminate exists (path: list edge). subset_edges path edges /\ is_path_from_to path u v
    returns same_component (e :: edges) u v
    with _. begin
      subset_edges_cons path e edges
    end

// Kruskal process maintains: every graph edge with valid endpoints either is in forest
// or has its endpoints in the same component of the forest
let rec lemma_kruskal_process_maximal_forest
    (sorted_edges all_sorted: list edge) (forest: list edge) (n: nat)
  : Lemma (requires is_forest forest n /\
                    (forall (e: edge). mem_edge e all_sorted /\ ~(mem_edge e sorted_edges) /\
                      e.u < n /\ e.v < n ==>
                      mem_edge e forest \/ same_component forest e.u e.v) /\
                    (exists (prefix: list edge). all_sorted == prefix @ sorted_edges))
          (ensures (let result = kruskal_process sorted_edges forest n in
                    (forall (e: edge). mem_edge e all_sorted /\ e.u < n /\ e.v < n ==>
                      mem_edge e result \/ same_component result e.u e.v)))
          (decreases sorted_edges)
  = match sorted_edges with
    | [] -> ()
    | e :: rest ->
      let forest' = kruskal_step e forest n in
      lemma_kruskal_step_preserves_forest e forest n;
      
      if e.u < n && e.v < n && 
         not (same_component_dec forest e.u e.v) &&
         not (mem_edge e forest) then begin
        assert (forest' == e :: forest);
        introduce forall (e': edge). mem_edge e' all_sorted /\ ~(mem_edge e' rest) /\
                            e'.u < n /\ e'.v < n ==>
                    mem_edge e' forest' \/ same_component forest' e'.u e'.v
        with introduce _ ==> _ with _. begin
          if edge_eq e' e then ()
          else if mem_edge e' forest then ()
          else begin
            assert (~(mem_edge e' sorted_edges));
            assert (same_component forest e'.u e'.v);
            same_component_mono forest e e'.u e'.v
          end
        end;
        
        eliminate exists (prefix: list edge). all_sorted == prefix @ (e :: rest)
          returns (exists (prefix': list edge). all_sorted == prefix' @ rest)
          with _. begin
            List.Tot.Properties.append_assoc prefix [e] rest;
            assert (all_sorted == (prefix @ [e]) @ rest)
          end;
        
        lemma_kruskal_process_maximal_forest rest all_sorted forest' n
      end else begin
        assert (forest' == forest);
        introduce forall (e': edge). mem_edge e' all_sorted /\ ~(mem_edge e' rest) /\
                            e'.u < n /\ e'.v < n ==>
                    mem_edge e' forest' \/ same_component forest' e'.u e'.v
        with introduce _ ==> _ with _. begin
          if edge_eq e' e then begin
            edge_eq_endpoints e' e;
            if mem_edge e forest then begin
              edge_eq_symmetric e' e;
              mem_edge_eq e e' forest
            end
            else if not (e.u < n && e.v < n) then ()
            else if same_component_dec forest e.u e.v then begin
              same_component_dec_sound forest e.u e.v;
              assert ((e'.u = e.u /\ e'.v = e.v) \/ (e'.u = e.v /\ e'.v = e.u));
              if e'.u = e.u && e'.v = e.v then ()
              else same_component_symmetric forest e.u e.v
            end else ()
          end else begin
            assert (~(mem_edge e' sorted_edges));
            ()
          end
        end;
        
        eliminate exists (prefix: list edge). all_sorted == prefix @ (e :: rest)
          returns (exists (prefix': list edge). all_sorted == prefix' @ rest)
          with _. begin
            List.Tot.Properties.append_assoc prefix [e] rest;
            assert (all_sorted == (prefix @ [e]) @ rest)
          end;
        
        lemma_kruskal_process_maximal_forest rest all_sorted forest' n
      end

// MST invariant: kruskal_process maintains "forest is subset of some MST"
// This needs the "minimum weight among unused cross-component edges" property
// which follows from processing edges in sorted order.
let rec lemma_kruskal_process_mst_invariant
    (g: graph) (sorted_edges: list edge) (forest: list edge)
  : Lemma (requires 
            is_forest forest g.n /\
            subset_edges forest g.edges /\
            (exists (mst: list edge). is_mst g mst /\ subset_edges forest mst) /\
            subset_edges sorted_edges g.edges /\
            is_sorted_by_weight sorted_edges /\
            // All graph edges have valid endpoints
            (forall (e': edge). mem_edge e' g.edges ==> e'.u < g.n /\ e'.v < g.n) /\
            // Every graph edge not in sorted_edges with valid endpoints
            // is either in the forest or connects same-component vertices
            (forall (e': edge). mem_edge e' g.edges /\ ~(mem_edge e' sorted_edges) /\
              ~(mem_edge e' forest) ==>
              same_component forest e'.u e'.v))
          (ensures (let result = kruskal_process sorted_edges forest g.n in
            (exists (mst: list edge). is_mst g mst /\ subset_edges result mst)))
          (decreases sorted_edges)
  = match sorted_edges with
    | [] -> ()
    | e :: rest ->
      let forest' = kruskal_step e forest g.n in
      lemma_kruskal_step_preserves_forest e forest g.n;
      
      if e.u < g.n && e.v < g.n && 
         not (same_component_dec forest e.u e.v) &&
         not (mem_edge e forest) then begin
        // e was added. Need to show: forest' = e :: forest is subset of some MST
        // Use lemma_kruskal_step_safe_edge
        
        // Establish: e has minimum weight among unused cross-component edges
        // For any e' in g.edges that's not in forest and crosses different components:
        //   - If e' is in sorted_edges (i.e., in rest): e.w <= e'.w (from sorted order)
        //   - If e' is not in sorted_edges: from precondition, same_component forest e'.u e'.v
        //     So ~(same_component forest e'.u e'.v) is false, vacuously true.
        introduce forall (e': edge). 
          mem_edge e' g.edges /\ not (mem_edge e' forest) /\ ~(same_component forest e'.u e'.v) ==>
          e.w <= e'.w
        with introduce _ ==> _ with _. begin
          // e' is in g.edges, not in forest, different components
          if mem_edge e' (e :: rest) then begin
            // e' is in sorted_edges = e :: rest
            if edge_eq e' e then begin
              edge_eq_endpoints e' e
            end else begin
              // e' is in rest. Since sorted_edges is sorted and e is the head:
              // e.w <= rest head.w <= ... <= e'.w
              assert (mem_edge e' rest);
              // Need: first element of sorted list ≤ any element
              let rec sorted_head_le_all (hd: edge) (tl: list edge) (e': edge)
                : Lemma (requires is_sorted_by_weight (hd :: tl) /\ mem_edge e' tl)
                        (ensures hd.w <= e'.w)
                        (decreases tl)
                = match tl with
                  | [] -> ()
                  | hd2 :: tl2 ->
                    if edge_eq e' hd2 then edge_eq_endpoints e' hd2
                    else begin
                      sorted_head_le_all hd2 tl2 e';
                      ()
                    end
              in
              sorted_head_le_all e rest e'
            end
          end else begin
            // e' is not in sorted_edges, not in forest, in g.edges.
            // From precondition: same_component forest e'.u e'.v.
            // But ~(same_component forest e'.u e'.v) from outer. Contradiction.
            assert (same_component forest e'.u e'.v)
          end
        end;
        
        // Apply safe edge lemma
        // Establish ~(same_component forest e.u e.v) from same_component_dec = false
        let dec_complete_contra () 
          : Lemma (requires same_component forest e.u e.v)
                  (ensures same_component_dec forest e.u e.v = true)
          = same_component_dec_complete forest e.u e.v
        in
        FStar.Classical.move_requires dec_complete_contra ();
        assert (~(same_component forest e.u e.v));
        assert (e.u < g.n /\ e.v < g.n);
        assert (mem_edge e g.edges);
        assert (is_forest forest g.n);
        assert (subset_edges forest g.edges);
        lemma_kruskal_step_safe_edge g e forest;
        // Now: exists mst. is_mst g mst /\ subset_edges (e :: forest) mst
        
        // For the IH: we need the "already processed" edges to satisfy the invariant
        // For e' not in rest, not in forest', with valid endpoints:
        //   same_component forest' e'.u e'.v
        // Case 1: e' not in (e :: rest) => e' not in sorted_edges =>
        //   same_component forest e'.u e'.v (from precondition) =>
        //   same_component forest' e'.u e'.v (monotone, forest ⊆ forest')
        // Case 2: e' = e (edge_eq) => e is in forest' = e :: forest. So mem_edge e' forest' (via edge_eq).
        //   But we need ~(mem_edge e' forest') to trigger the precondition, so vacuously true.
        
        // Establish IH precondition
        assert (forest' == e :: forest);
        introduce forall (e': edge). mem_edge e' g.edges /\ ~(mem_edge e' rest) /\
          ~(mem_edge e' forest') ==>
          same_component forest' e'.u e'.v
        with introduce _ ==> _ with _. begin
          // e' is not in rest and not in forest'
          // If edge_eq e' e: then e' is in forest' (since e is head of forest'). Contradiction.
          if edge_eq e' e then begin
            edge_eq_symmetric e' e;
            mem_edge_eq e e' (e :: forest);
            assert (mem_edge e' forest')
            // contradicts ~(mem_edge e' forest')
          end else begin
            // e' is not e, and e' is not in rest
            // So e' is not in (e :: rest) = sorted_edges
            assert (~(mem_edge e' sorted_edges));
            // From precondition (if not in forest): same_component forest e'.u e'.v
            if mem_edge e' forest then begin
              // e' in forest but not in forest' = e :: forest? Impossible.
              assert (mem_edge e' (e :: forest))
            end else begin
              assert (same_component forest e'.u e'.v);
              same_component_mono forest e e'.u e'.v
            end
          end
        end;
        
        // subset_edges
        lemma_kruskal_step_edges_from_graph e forest g.edges g.n;
        
        // sorted rest
        assert (is_sorted_by_weight rest);
        
        lemma_kruskal_process_mst_invariant g rest forest'
      end else begin
        // e was NOT added. forest' = forest. MST invariant preserved trivially.
        
        // For the IH: processed edges invariant
        introduce forall (e': edge). mem_edge e' g.edges /\ ~(mem_edge e' rest) /\
          ~(mem_edge e' forest') ==>
          same_component forest' e'.u e'.v
        with introduce _ ==> _ with _. begin
          if edge_eq e' e then begin
            edge_eq_endpoints e' e;
            if mem_edge e forest then begin
              edge_eq_symmetric e' e;
              mem_edge_eq e e' forest
            end else if not (e.u < g.n && e.v < g.n) then begin
              // e'.u < g.n /\ e'.v < g.n (from valid endpoints precondition)
              // but e endpoints = e' endpoints (from edge_eq). Contradiction.
              assert (mem_edge e' g.edges);
              assert (e'.u < g.n /\ e'.v < g.n)
            end else if same_component_dec forest e.u e.v then begin
              same_component_dec_sound forest e.u e.v;
              if e'.u = e.u && e'.v = e.v then ()
              else same_component_symmetric forest e.u e.v
            end else ()
          end else begin
            assert (~(mem_edge e' sorted_edges));
            ()
          end
        end;
        
        assert (is_sorted_by_weight rest);
        
        lemma_kruskal_process_mst_invariant g rest forest'
      end

// ==========================================
// Simple path extraction for main theorems
// ==========================================

// Helper: path traversal connectivity
let rec path_edges_connected_implies_endpoints_connected
    (path: list edge) (result: list edge) (u v: nat)
  : Lemma (requires is_path_from_to path u v /\
                    (forall (e: edge). mem_edge e path ==>
                      mem_edge e result \/ same_component result e.u e.v))
          (ensures same_component result u v)
          (decreases path)
  = match path with
    | [] -> same_component_reflexive result u
    | e :: rest ->
      if e.u = u then begin
        path_edges_connected_implies_endpoints_connected rest result e.v v;
        if mem_edge e result then begin
          edge_gives_reachability result u e.v e;
          same_component_transitive result u e.v v
        end else begin
          assert (e.u = u);
          same_component_transitive result u e.v v
        end
      end else begin
        assert (e.v = u);
        path_edges_connected_implies_endpoints_connected rest result e.u v;
        if mem_edge e result then begin
          edge_gives_reachability result u e.u e;
          same_component_transitive result u e.u v
        end else begin
          same_component_symmetric result e.u e.v;
          same_component_transitive result u e.u v
        end
      end

let rec subset_edges_valid_endpoints (path: list edge) (g_edges: list edge) (n: nat)
  : Lemma (requires subset_edges path g_edges /\
                    (forall (e: edge). mem_edge e g_edges ==> e.u < n /\ e.v < n))
          (ensures (forall (e: edge). mem_edge e path ==> e.u < n /\ e.v < n))
          (decreases path)
  = match path with
    | [] -> ()
    | e :: rest -> subset_edges_valid_endpoints rest g_edges n

let path_next (e: edge) (current: nat) : nat =
  if e.u = current then e.v else e.u

let rec vertex_visited (path: list edge) (current target: nat) : Tot bool (decreases path)
  = current = target ||
    (match path with
     | [] -> false
     | e :: rest -> vertex_visited rest (path_next e current) target)

let rec path_skip_to (path: list edge) (current target: nat) 
  : Tot (list edge) (decreases path)
  = if current = target then path
    else match path with
      | [] -> []
      | e :: rest -> path_skip_to rest (path_next e current) target

let rec path_skip_to_valid (path: list edge) (current target finish: nat)
  : Lemma (requires is_path_from_to path current finish /\
                    vertex_visited path current target)
          (ensures is_path_from_to (path_skip_to path current target) target finish)
          (decreases path)
  = if current = target then ()
    else match path with
      | e :: rest -> path_skip_to_valid rest (path_next e current) target finish

let rec path_skip_to_subset (path: list edge) (current target: nat) (es: list edge)
  : Lemma (requires subset_edges path es)
          (ensures subset_edges (path_skip_to path current target) es)
          (decreases path)
  = if current = target then ()
    else match path with
      | [] -> ()
      | e :: rest -> path_skip_to_subset rest (path_next e current) target es

let rec path_skip_to_shorter (path: list edge) (current target: nat)
  : Lemma (requires current <> target /\ vertex_visited path current target)
          (ensures length (path_skip_to path current target) < length path)
          (decreases path)
  = match path with
    | e :: rest ->
      let next = path_next e current in
      if next = target then ()
      else path_skip_to_shorter rest next target

// Remove revisits to start vertex u
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec remove_start_revisit (path: list edge) (es: list edge) (u v: nat)
  : Pure (list edge)
         (requires is_path_from_to path u v /\ subset_edges path es /\ u <> v)
         (ensures fun path' -> is_path_from_to path' u v /\ subset_edges path' es /\ 
                               Cons? path' /\ length path' <= length path /\
                               ~(vertex_visited (List.Tot.tl path') 
                                 (path_next (List.Tot.hd path') u) u))
         (decreases length path)
  = let hd :: tl = path in
    let next = path_next hd u in
    if next = u then
      remove_start_revisit tl es u v
    else if vertex_visited tl next u then begin
      path_skip_to_valid tl next u v;
      path_skip_to_subset tl next u es;
      path_skip_to_shorter tl next u;
      remove_start_revisit (path_skip_to tl next u) es u v
    end else
      path
#pop-options

// After remove_start_revisit, all edges in tl have endpoints ≠ u
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec no_visit_means_no_u_endpoints (path: list edge) (current u finish: nat)
  : Lemma (requires is_path_from_to path current finish /\
                    current <> u /\ ~(vertex_visited path current u))
          (ensures forall (e: edge). mem_edge e path ==> e.u <> u /\ e.v <> u)
          (decreases path)
  = match path with
    | [] -> ()
    | hd :: tl ->
      let next = path_next hd current in
      // vertex_visited (hd::tl) current u = (current = u) || vertex_visited tl next u
      // current <> u, so ~(vertex_visited tl next u)
      // Also: next <> u (since vertex_visited tl next u starts with next=u check)
      assert (next <> u);
      assert (hd.u <> u /\ hd.v <> u);
      if Cons? tl then
        no_visit_means_no_u_endpoints tl next u finish
      else ()
#pop-options

// Edge with u-endpoint not mem_edge of edges without u-endpoints
let rec edge_with_u_not_in_no_u_list (e: edge) (path: list edge) (u: nat)
  : Lemma (requires (e.u = u \/ e.v = u) /\
                    (forall (e': edge). mem_edge e' path ==> e'.u <> u /\ e'.v <> u))
          (ensures ~(mem_edge e path))
          (decreases path)
  = match path with
    | [] -> ()
    | hd :: tl ->
      // edge_eq e hd checks {e.u,e.v} = {hd.u,hd.v} (same weight)
      // e has u endpoint, hd has no u endpoint. So can't match.
      edge_with_u_not_in_no_u_list e tl u

// mem_edge subset: if e in A and subset_edges A B then e in B
let rec mem_edge_of_subset (e: edge) (a b: list edge)
  : Lemma (requires mem_edge e a /\ subset_edges a b)
          (ensures mem_edge e b)
          (decreases a)
  = match a with
    | hd :: tl ->
      if edge_eq e hd then begin
        // mem_edge hd b (from subset_edges)
        // edge_eq e hd => edge_eq hd e (symmetric)
        // mem_edge hd b /\ edge_eq hd e => mem_edge e b
        edge_eq_symmetric e hd;
        mem_edge_eq hd e b
      end else mem_edge_of_subset e tl b

// Simple path extraction: guaranteed to produce edges from the original path
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec extract_simple_path (path: list edge) (u v: nat)
  : Lemma (requires is_path_from_to path u v /\ u <> v)
          (ensures exists (path': list edge). is_path_from_to path' u v /\ 
                    subset_edges path' path /\ all_edges_distinct path' /\ Cons? path')
          (decreases length path)
  = // Phase 1: remove revisits to u
    subset_edges_reflexive path;
    let path_nr = remove_start_revisit path path u v in
    assert (is_path_from_to path_nr u v);
    assert (subset_edges path_nr path);
    let hd :: tl = path_nr in
    let next = path_next hd u in
    assert (~(vertex_visited tl next u));
    // hd has u as endpoint
    assert ((hd.u = u /\ next = hd.v) \/ (hd.v = u /\ next = hd.u));
    if next = v then begin
      // Single edge path
      assert (is_path_from_to [hd] u v);
      assert (all_edges_distinct [hd]);
      assert (subset_edges [hd] path_nr);
      subset_edges_transitive [hd] path_nr path
    end else begin
      // tl: path from next to v, next <> u, next <> v
      // All edges in tl have endpoints <> u
      no_visit_means_no_u_endpoints tl next u v;
      // Recursively extract simple path from tl
      assert (length tl < length path_nr);
      assert (length path_nr <= length path);
      extract_simple_path tl next v;
      // IH gives: exists path_tl. simple path from next to v, subset_edges path_tl tl
      // Since subset_edges path_tl tl and all edges in tl have endpoints <> u:
      //   all edges in path_tl have endpoints <> u
      // Since hd has u as endpoint: ~(mem_edge hd path_tl)
      // So hd :: path_tl is all_edges_distinct
      // And is_path_from_to (hd :: path_tl) u v
      
      // We need to work with the existential witness. Use classical logic.
      FStar.Classical.exists_elim 
        (exists (path': list edge). is_path_from_to path' u v /\
          subset_edges path' path /\ all_edges_distinct path' /\ Cons? path')
        #_
        #(fun (path_tl: list edge) -> 
          is_path_from_to path_tl next v /\
          subset_edges path_tl tl /\ all_edges_distinct path_tl /\ Cons? path_tl) ()
        (fun (path_tl: list edge{
          is_path_from_to path_tl next v /\
          subset_edges path_tl tl /\ all_edges_distinct path_tl /\ Cons? path_tl}) ->
          // All edges in path_tl are from tl, hence have endpoints <> u
          let rec path_tl_no_u (p: list edge)
            : Lemma (requires subset_edges p tl /\
                              (forall (e: edge). mem_edge e tl ==> e.u <> u /\ e.v <> u))
                    (ensures forall (e: edge). mem_edge e p ==> e.u <> u /\ e.v <> u)
                    (decreases p)
            = match p with
              | [] -> ()
              | e :: rest -> path_tl_no_u rest
          in
          path_tl_no_u path_tl;
          // hd has u as endpoint, path_tl has no u-endpoint edges
          edge_with_u_not_in_no_u_list hd path_tl u;
          assert (~(mem_edge hd path_tl));
          // hd :: path_tl is simple
          assert (all_edges_distinct (hd :: path_tl));
          // hd :: path_tl is a valid path from u to v
          assert (is_path_from_to (hd :: path_tl) u v);
          // subset: path_tl ⊆ tl, tl ⊆ path_nr = hd :: tl ⊆ path
          subset_edges_reflexive tl;
          subset_edges_cons tl hd tl;
          subset_edges_transitive path_tl tl (hd :: tl);
          subset_edges_transitive path_tl path_nr path;
          assert (subset_edges (hd :: path_tl) path)
        )
    end
#pop-options

// Now we can prove: adding edge between reachable vertices creates cycle
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let reachable_means_not_acyclic (n: nat) (t: list edge) (e: edge)
  : Lemma (requires acyclic n t /\ reachable t e.u e.v /\ 
                    e.u < n /\ e.v < n /\ e.u <> e.v /\ ~(mem_edge e t))
          (ensures ~(acyclic n (e :: t)))
  = // Get a simple path from e.u to e.v in t
    FStar.Classical.exists_elim
      (~(acyclic n (e :: t)))
      #_
      #(fun (path: list edge) -> subset_edges path t /\ is_path_from_to path e.u e.v) ()
      (fun (path: list edge{subset_edges path t /\ is_path_from_to path e.u e.v}) ->
        extract_simple_path path e.u e.v;
        FStar.Classical.exists_elim
          (~(acyclic n (e :: t)))
          #_
          #(fun (sp: list edge) -> is_path_from_to sp e.u e.v /\
              subset_edges sp path /\ all_edges_distinct sp /\ Cons? sp) ()
          (fun (sp: list edge{is_path_from_to sp e.u e.v /\
              subset_edges sp path /\ all_edges_distinct sp /\ Cons? sp}) ->
            // sp: simple path from e.u to e.v, edges from path ⊆ t
            subset_edges_transitive sp path t;
            // Form cycle: sp @ [e] from e.u to e.u
            is_path_append_edge sp e.u e.v e.u e;
            // sp @ [e] subset of e :: t
            subset_edges_cons sp e t;
            subset_edges_append_single sp e (e :: t);
            // all_edges_distinct (sp @ [e]): 
            // - all_edges_distinct sp ✓
            // - e ∉ sp (since sp ⊆ t and e ∉ t)
            let rec e_not_in_sp (p: list edge) 
              : Lemma (requires subset_edges p t /\ ~(mem_edge e t))
                      (ensures ~(mem_edge e p))
                      (decreases p)
              = match p with
                | [] -> ()
                | hd :: tl -> 
                  if edge_eq e hd then begin
                    // edge_eq e hd and mem_edge hd t (from subset_edges)
                    // => mem_edge e t (via edge_eq_symmetric + mem_edge_eq)
                    edge_eq_symmetric e hd;
                    mem_edge_eq hd e t
                    // But ~(mem_edge e t). Contradiction.
                  end else e_not_in_sp tl
            in
            e_not_in_sp sp;
            // all_edges_distinct on append
            let rec distinct_append_single (p: list edge) (e0: edge)
              : Lemma (requires all_edges_distinct p /\ ~(mem_edge e0 p))
                      (ensures all_edges_distinct (p @ [e0]))
                      (decreases p)
              = match p with
                | [] -> ()
                | hd :: tl ->
                  distinct_append_single tl e0;
                  // Need: ~(mem_edge hd (tl @ [e0]))
                  mem_edge_append hd tl [e0];
                  // mem_edge hd (tl @ [e0]) <==> mem_edge hd tl || mem_edge hd [e0]
                  // ~(mem_edge hd tl) from all_edges_distinct (hd :: tl)
                  // mem_edge hd [e0] = edge_eq hd e0
                  // If edge_eq hd e0: mem_edge e0 p (since hd ∈ p). Contradicts ~(mem_edge e0 p).
                  if edge_eq hd e0 then begin
                    mem_edge_hd hd tl;
                    mem_edge_eq hd e0 (hd :: tl)
                  end else ()
            in
            distinct_append_single sp e;
            // Now we have a simple cycle in e :: t
            let cycle = sp @ [e] in
            assert (is_path_from_to cycle e.u e.u);
            assert (Cons? cycle);
            assert (subset_edges cycle (e :: t));
            assert (all_edges_distinct cycle);
            // This contradicts acyclic n (e :: t)
            assert (e.u < n);
            // acyclic n (e :: t) says: for all v < n, cycle ⊆ (e::t), Cons? cycle, 
            //   all_edges_distinct cycle ==> ~(is_path_from_to cycle v v)
            // Instantiate with v = e.u: gives ~(is_path_from_to cycle e.u e.u)
            // But we have is_path_from_to cycle e.u e.u. Contradiction.
            ()
          )
      )
#pop-options

// Connected subset of spanning tree equals the spanning tree
// If result ⊆ mst and result connects all vertices, then all mst edges are in result
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let connected_subset_of_tree_is_tree (g: graph) (result mst: list edge)
  : Lemma (requires is_spanning_tree g mst /\
                    subset_edges result mst /\
                    all_connected g.n result /\
                    acyclic g.n result /\
                    (forall (e: edge). mem_edge e mst ==> e.u < g.n /\ e.v < g.n) /\
                    (forall (e: edge). mem_edge e mst ==> e.u <> e.v))
          (ensures forall (e: edge). mem_edge e mst ==> mem_edge e result)
  = introduce forall (e: edge). mem_edge e mst ==> mem_edge e result
    with introduce _ ==> _ with _. begin
      // Suppose e ∈ mst. We want e ∈ result.
      // By contradiction: suppose e ∉ result.
      if not (mem_edge e result) then begin
        assert (e.u < g.n /\ e.v < g.n);
        same_component_symmetric result 0 e.u;
        same_component_transitive result e.u 0 e.v;
        assert (reachable result e.u e.v);
        // result is acyclic, e has valid endpoints, e ∉ result, e.u <> e.v
        // => ~(acyclic g.n (e :: result))
        reachable_means_not_acyclic g.n result e;
        // But result ⊆ mst and e ∈ mst, so e :: result ⊆ mst (up to ordering)
        // Actually: subset_edges (e :: result) mst since e ∈ mst and result ⊆ mst
        assert (subset_edges (e :: result) mst);
        // And mst is acyclic (from is_spanning_tree)
        // acyclic n mst and (e :: result) ⊆ mst
        // Any cycle in (e :: result) is also a cycle in mst (by subset)
        // So acyclic n mst => acyclic n (e :: result)
        // This is the key: acyclicity is downward-closed for subsets
        let rec acyclic_subset (a b: list edge) (n: nat)
          : Lemma (requires acyclic n b /\ subset_edges a b)
                  (ensures acyclic n a)
          = introduce forall (v: nat) (cycle: list edge).
              v < n /\ subset_edges cycle a /\ Cons? cycle /\ all_edges_distinct cycle ==>
              ~(is_path_from_to cycle v v)
            with introduce _ ==> _ with _. begin
              subset_edges_transitive cycle a b
            end
        in
        acyclic_subset (e :: result) mst g.n;
        // Now: acyclic g.n (e :: result) AND ~(acyclic g.n (e :: result))
        // Contradiction!
        assert (acyclic g.n (e :: result));
        assert (~(acyclic g.n (e :: result)));
        ()
      end else ()
    end
#pop-options

// No duplicate edges in a list (using edge_eq)
let rec noRepeats_edge (l: list edge) : bool =
  match l with
  | [] -> true
  | hd :: tl -> not (mem_edge hd tl) && noRepeats_edge tl

// Kruskal result has no duplicate edges
let rec lemma_kruskal_process_no_repeats (sorted_edges: list edge) (forest: list edge) (n: nat)
  : Lemma (requires noRepeats_edge forest)
          (ensures noRepeats_edge (kruskal_process sorted_edges forest n))
          (decreases sorted_edges)
  = match sorted_edges with
    | [] -> ()
    | e :: rest ->
      if e.u < n && e.v < n && not (same_component_dec forest e.u e.v) && not (mem_edge e forest) then
        lemma_kruskal_process_no_repeats rest (e :: forest) n
      else
        lemma_kruskal_process_no_repeats rest forest n

// Remove first occurrence of edge from list
let rec remove_edge_first (e: edge) (l: list edge) : list edge =
  match l with
  | [] -> []
  | hd :: tl -> if edge_eq e hd then tl else hd :: remove_edge_first e tl

// Length decreases by 1 when removing present edge
let rec remove_edge_first_length (e: edge) (l: list edge)
  : Lemma (requires mem_edge e l)
          (ensures length (remove_edge_first e l) = length l - 1)
          (decreases l)
  = match l with
    | hd :: tl ->
      if edge_eq e hd then ()
      else remove_edge_first_length e tl

// If e' ∈ l and ~(edge_eq e' e), then e' ∈ remove_edge_first e l
let rec mem_remove_edge_first_other (e' e: edge) (l: list edge)
  : Lemma (requires mem_edge e' l /\ ~(edge_eq e' e))
          (ensures mem_edge e' (remove_edge_first e l))
          (decreases l)
  = match l with
    | hd :: tl ->
      if edge_eq e hd then begin
        if edge_eq e' hd then begin
          edge_eq_symmetric e hd;
          assert (edge_eq e' e)
        end else ()
      end else begin
        if edge_eq e' hd then ()
        else mem_remove_edge_first_other e' e tl
      end

// noRepeats_edge a ∧ subset_edges a b ⟹ length a ≤ length b
let rec subset_noRepeats_length_le (a b: list edge)
  : Lemma (requires noRepeats_edge a /\ subset_edges a b)
          (ensures length a <= length b)
          (decreases a)
  = match a with
    | [] -> ()
    | hd :: tl ->
      assert (mem_edge hd b);
      let b' = remove_edge_first hd b in
      remove_edge_first_length hd b;
      let rec prove_subset_tl (p: list edge)
        : Lemma (requires (forall (e:edge). mem_edge e p ==> mem_edge e tl) /\
                          noRepeats_edge (hd :: tl) /\
                          subset_edges (hd :: tl) b)
                (ensures subset_edges p b')
                (decreases p)
        = match p with
          | [] -> ()
          | e :: rest ->
            assert (mem_edge e tl);
            mem_edge_of_subset e (hd :: tl) b;
            (if edge_eq e hd then begin
              edge_eq_symmetric e hd;
              mem_edge_eq hd e tl
            end else ());
            mem_remove_edge_first_other e hd b;
            prove_subset_tl rest
      in
      prove_subset_tl tl;
      subset_noRepeats_length_le tl b'

// Kruskal's algorithm produces a spanning tree
let theorem_kruskal_produces_spanning_tree (g: graph)
  : Lemma (requires g.n > 0 /\ 
                    all_connected g.n g.edges /\
                    (exists (mst: list edge). is_mst g mst) /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n) /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u <> e.v))
          (ensures (let result = pure_kruskal g in
                    is_spanning_tree g result))
  = let result = pure_kruskal g in
    let sorted = sort_edges g.edges in
    
    // Part 1: Result is a forest (acyclic)
    lemma_kruskal_process_preserves_forest sorted [] g.n;
    assert (acyclic g.n result);
    
    // Part 2: All edges from graph
    sort_edges_subset g.edges;
    lemma_kruskal_process_edges_from_graph sorted [] g.edges g.n;
    assert (subset_edges result g.edges);
    
    // Part 3: Result connects all vertices
    lemma_kruskal_process_maximal_forest sorted sorted [] g.n;
    introduce forall (v: nat). v < g.n ==> reachable result 0 v
    with introduce _ ==> _ with _. begin
      FStar.Classical.exists_elim (reachable result 0 v)
        #_ 
        #(fun (path: list edge) -> subset_edges path g.edges /\ is_path_from_to path 0 v) ()
        (fun (path: list edge{subset_edges path g.edges /\ is_path_from_to path 0 v}) ->
          introduce forall (e: edge). mem_edge e path ==> 
            mem_edge e result \/ same_component result e.u e.v
          with introduce _ ==> _ with _. begin
            mem_edge_of_subset e path g.edges;
            assert (e.u < g.n /\ e.v < g.n);
            sort_edges_mem e g.edges
          end;
          path_edges_connected_implies_endpoints_connected path result 0 v
        )
    end;
    assert (all_connected g.n result);
    
    // Part 4: Result has g.n - 1 edges
    // Use MST invariant to show result ⊆ some MST
    sort_edges_sorted g.edges;
    introduce forall (e': edge). mem_edge e' g.edges /\ ~(mem_edge e' sorted) /\
      ~(mem_edge e' ([] #edge)) ==> same_component ([] #edge) e'.u e'.v
    with introduce _ ==> _ with _. begin
      sort_edges_mem e' g.edges
    end;
    lemma_kruskal_process_mst_invariant g sorted [];
    // Now: exists mst'. is_mst g mst' /\ subset_edges result mst'
    FStar.Classical.exists_elim (is_spanning_tree g result)
      #_
      #(fun (mst': list edge) -> is_mst g mst' /\ subset_edges result mst') ()
      (fun (mst': list edge{is_mst g mst' /\ subset_edges result mst'}) ->
        // result ⊆ mst'
        assert (subset_edges result mst');
        // result is connected and acyclic
        assert (all_connected g.n result);
        assert (acyclic g.n result);
        // mst' is a spanning tree
        assert (is_spanning_tree g mst');
        // mst' edges have valid endpoints (from g.edges)
        assert (subset_edges mst' g.edges);
        // mst' edges inherit valid endpoints and no self-loops from g.edges
        introduce forall (e: edge). mem_edge e mst' ==> e.u < g.n /\ e.v < g.n
        with introduce _ ==> _ with _. mem_edge_of_subset e mst' g.edges;
        introduce forall (e: edge). mem_edge e mst' ==> e.u <> e.v
        with introduce _ ==> _ with _. mem_edge_of_subset e mst' g.edges;
        // All mst' edges are in result (connected_subset_of_tree_is_tree)
        connected_subset_of_tree_is_tree g result mst';
        // forall e ∈ mst'. mem_edge e result
        // noRepeats_edge result (from kruskal_process)
        lemma_kruskal_process_no_repeats sorted [] g.n;
        assert (noRepeats_edge result);
        // |result| ≤ |mst'| from subset + noRepeats
        subset_noRepeats_length_le result mst';
        assert (length result <= length mst');
        assert (length mst' = g.n - 1);
        // |mst'| ≤ |result| from ∀ e ∈ mst'. e ∈ result + noRepeats result
        // Actually: we need to prove this direction too
        // For each e ∈ mst': mem_edge e result. So mst' ⊂_edge result.
        // Since noRepeats_edge result: |mst'| ≤ |result|
        // We use subset_noRepeats_length_le on mst' and result
        // But we need subset_edges mst' result (not just ∀ e ∈ mst'. e ∈ result)
        introduce forall (e: edge). mem_edge e mst' ==> mem_edge e result
        with introduce _ ==> _ with ht. ();
        // Now we can derive subset_edges mst' result
        let rec build_subset (l: list edge)
          : Lemma (requires forall (e: edge). mem_edge e l ==> mem_edge e result)
                  (ensures subset_edges l result)
                  (decreases l)
          = match l with
            | [] -> ()
            | hd :: tl -> build_subset tl
        in
        build_subset mst';
        subset_noRepeats_length_le mst' result;
        assert (length mst' <= length result);
        // Together: length result = length mst' = g.n - 1
        assert (length result = g.n - 1)
      )

// total_weight of remove_edge_first
let rec total_weight_remove (e: edge) (l: list edge)
  : Lemma (requires mem_edge e l)
          (ensures total_weight (remove_edge_first e l) = total_weight l - e.w)
          (decreases l)
  = match l with
    | hd :: tl ->
      if edge_eq e hd then ()
      else total_weight_remove e tl

// Helper: if mem_edge e (remove_edge_first x l), then mem_edge e l
let rec mem_remove_edge_first_mem (e x: edge) (l: list edge)
  : Lemma (requires mem_edge e (remove_edge_first x l))
          (ensures mem_edge e l)
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      if edge_eq x hd then ()
      else if edge_eq e hd then ()
      else mem_remove_edge_first_mem e x tl

// total_weight equality for mutual edge subsets with noRepeats on one side and same length
let rec total_weight_mutual_eq (a b: list edge)
  : Lemma (requires noRepeats_edge a /\ subset_edges a b /\
                    (forall (e: edge). mem_edge e b ==> mem_edge e a) /\
                    length a = length b)
          (ensures total_weight a = total_weight b)
          (decreases a)
  = match a with
    | [] -> (match b with | [] -> ())
    | hd :: tl ->
      assert (mem_edge hd b);
      let b' = remove_edge_first hd b in
      remove_edge_first_length hd b;
      total_weight_remove hd b;
      // total_weight b = total_weight b' + hd.w
      // Need: noRepeats_edge tl, subset_edges tl b'
      // Need: ∀ e ∈ b'. e ∈ tl
      // Need: length tl = length b'
      
      // subset_edges tl b':
      let rec prove_tl_subset (p: list edge)
        : Lemma (requires (forall (e:edge). mem_edge e p ==> mem_edge e tl) /\
                          noRepeats_edge (hd :: tl) /\
                          subset_edges (hd :: tl) b)
                (ensures subset_edges p b')
                (decreases p)
        = match p with
          | [] -> ()
          | e :: rest ->
            assert (mem_edge e tl);
            mem_edge_of_subset e (hd :: tl) b;
            (if edge_eq e hd then begin
              edge_eq_symmetric e hd;
              mem_edge_eq hd e tl
            end else ());
            mem_remove_edge_first_other e hd b;
            prove_tl_subset rest
      in
      prove_tl_subset tl;
      
      // ∀ e ∈ b'. e ∈ tl:
      // Strategy: use the fact that length tl = length b' and subset_edges tl b' 
      // and noRepeats tl. If some e ∈ b' is NOT in tl, then by pigeonhole,
      // tl maps into b' \ {e}, which has length b' - 1, but tl has length b' edges
      // with noRepeats — contradiction with pigeonhole.
      // 
      // More directly: ∀ e ∈ b'. e ∈ b (from mem_remove). e ∈ b ⟹ e ∈ (hd :: tl).
      // So either edge_eq e hd or e ∈ tl.
      // If edge_eq e hd for ALL such e, then all elements of b' are equivalent to hd.
      // But tl ⊆ b' and tl has no element equivalent to hd (noRepeats).
      // So if tl is non-empty, tl has an element not equivalent to hd in b'. Contradiction.
      // If tl is empty, length b' = 0, so b' = []. Fine, vacuously true.
      //
      // Actually the simpler approach: prove it by counting.
      // subset_noRepeats_length_le tl b' gives length tl ≤ length b'.
      // We know length tl = length b'.
      // Every element of b' that's in tl "uses up" one slot.
      // If any element of b' is NOT in tl, then b' has >length tl elements 
      // that need "distinct" matches, but... we need noRepeats on b' for that.
      //
      // Let me try the direct approach:
      introduce forall (e: edge). mem_edge e b' ==> mem_edge e tl
      with introduce _ ==> _ with _. begin
        mem_remove_edge_first_mem e hd b;
        assert (mem_edge e b);
        assert (mem_edge e (hd :: tl));
        // e ∈ (hd :: tl) means edge_eq e hd \/ e ∈ tl
        if mem_edge e tl then ()
        else begin
          // e ∉ tl, so edge_eq e hd
          assert (edge_eq e hd);
          // e ∈ b', e is edge_eq to hd, and e ∉ tl
          // But then: tl maps into b' via subset_edges tl b'.
          // Each edge of tl is NOT edge_eq to hd (from noRepeats).
          // And e IS edge_eq to hd and e ∈ b'.
          // So tl maps into b' minus the positions holding hd-equivalents.
          // But we need a contradiction. 
          // 
          // Consider: if e ∈ b' and edge_eq e hd, then there are ≥2 copies of hd in b
          // (one was removed by remove_edge_first, one remains as e).
          // From subset_edges tl b': length tl ≤ length b' 
          //   (we proved this in subset_noRepeats_length_le).
          // We know length tl = length b'.
          // But tl has no hd-equivalents, so each edge of tl maps to a non-hd-equivalent in b'.
          // If e (which IS hd-equivalent) is in b', then b' has at most (length b' - 1) non-hd-equivalents.
          // So tl can have at most (length b' - 1) edges (pigeonhole into non-hd-equivalents of b').
          // But length tl = length b'. Contradiction!
          //
          // This pigeonhole requires showing the injection maps tl to non-hd-equivalents only.
          // Let me formalize using subset_noRepeats_length_le:
          // Define b'' = remove_edge_first e b' (removing the hd-equivalent from b').
          // Then each edge of tl is in b'' (since tl edges are in b' and not edge_eq hd).
          // So subset_edges tl b''.
          // subset_noRepeats_length_le tl b'' gives length tl ≤ length b''.
          // But length b'' = length b' - 1 = length tl - 1. Contradiction!
          let b'' = remove_edge_first e b' in
          remove_edge_first_length e b';
          let rec tl_subset_b'' (p: list edge)
            : Lemma (requires (forall (x:edge). mem_edge x p ==> mem_edge x tl) /\
                              noRepeats_edge (hd :: tl) /\
                              subset_edges (hd :: tl) b /\
                              mem_edge e b' /\ edge_eq e hd)
                    (ensures subset_edges p b'')
                    (decreases p)
            = match p with
              | [] -> ()
              | x :: rest ->
                assert (mem_edge x tl);
                mem_edge_of_subset x (hd :: tl) b;
                (if edge_eq x hd then begin
                  edge_eq_symmetric x hd;
                  mem_edge_eq hd x tl
                end else ());
                mem_remove_edge_first_other x hd b;
                assert (mem_edge x b');
                // x ∈ b' and ~(edge_eq x hd) and edge_eq e hd
                // Need: ~(edge_eq x e)
                (if edge_eq x e then begin
                  // edge_eq x e and edge_eq e hd ⟹ edge_eq x hd (transitivity via SMT)
                  edge_eq_symmetric e hd;
                  assert (edge_eq hd e);
                  assert (edge_eq x e);
                  // x.u=e.u∧x.v=e.v or x.u=e.v∧x.v=e.u
                  // e.u=hd.u∧e.v=hd.v or e.u=hd.v∧e.v=hd.u  (from edge_eq e hd)
                  // These combine to give edge_eq x hd
                  assert (edge_eq x hd) // should follow from SMT
                end else ());
                mem_remove_edge_first_other x e b';
                tl_subset_b'' rest
          in
          tl_subset_b'' tl;
          subset_noRepeats_length_le tl b'';
          // length tl ≤ length b'' = length b' - 1 = length tl - 1. Contradiction!
          assert false
        end
      end;
      
      total_weight_mutual_eq tl b'

//SNIPPET_START: theorem_kruskal_mst
// Kruskal's algorithm produces a minimum spanning tree
let theorem_kruskal_produces_mst (g: graph)
  : Lemma (requires g.n > 0 /\ 
                    all_connected g.n g.edges /\
                    (exists (mst: list edge). is_mst g mst) /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u < g.n /\ e.v < g.n) /\
                    (forall (e: edge). mem_edge e g.edges ==> e.u <> e.v))
          (ensures (let result = pure_kruskal g in
                    is_mst g result))
//SNIPPET_END: theorem_kruskal_mst
  = theorem_kruskal_produces_spanning_tree g;
    
    let result = pure_kruskal g in
    let sorted = sort_edges g.edges in
    
    // result is a spanning tree
    assert (is_spanning_tree g result);
    
    // MST invariant: result ⊆ some MST
    sort_edges_sorted g.edges;
    sort_edges_subset g.edges;
    introduce forall (e': edge). mem_edge e' g.edges /\ ~(mem_edge e' sorted) /\
      ~(mem_edge e' ([] #edge)) ==> same_component ([] #edge) e'.u e'.v
    with introduce _ ==> _ with _. begin
      sort_edges_mem e' g.edges
    end;
    lemma_kruskal_process_mst_invariant g sorted [];
    // exists mst'. is_mst g mst' /\ subset_edges result mst'
    FStar.Classical.exists_elim (is_mst g result)
      #_
      #(fun (mst': list edge) -> is_mst g mst' /\ subset_edges result mst') ()
      (fun (mst': list edge{is_mst g mst' /\ subset_edges result mst'}) ->
        connected_subset_of_tree_is_tree g result mst';
        // forall e in mst'. mem_edge e result
        
        // Prove total_weight result = total_weight mst'
        lemma_kruskal_process_no_repeats sorted [] g.n;
        assert (noRepeats_edge result);
        
        // Build subset_edges mst' result from the forall
        let rec build_subset_mst (l: list edge)
          : Lemma (requires forall (e: edge). mem_edge e l ==> mem_edge e result)
                  (ensures subset_edges l result)
                  (decreases l)
          = match l with | [] -> () | _ :: tl -> build_subset_mst tl
        in
        build_subset_mst mst';

        assert (length result = g.n - 1);
        assert (length mst' = g.n - 1);
        
        total_weight_mutual_eq result mst';
        assert (total_weight result = total_weight mst');
        
        introduce forall (t: list edge). is_spanning_tree g t ==> total_weight result <= total_weight t
        with introduce _ ==> _ with _. ()
      )

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
  = // all_connected g.n t: forall v < g.n. reachable t 0 v
    // So same_component t 0 v for all v < g.n
    // By BFS completeness: same_component_dec t 0 v = true for all v < g.n
    let n = g.n in
    assert (n > 0);
    assert (all_connected n t);

    // Step 1: same_component_dec t 0 v = true for all v < n
    let aux_dec (v: nat)
      : Lemma (requires v < n) (ensures same_component_dec t 0 v = true)
      = assert (reachable t 0 v);
        same_component_dec_complete t 0 v
    in

    // Step 2: vertices_in_component t 0 n i includes all vertices from i to n-1
    let rec all_in_component (i: nat{i <= n})
      : Lemma (ensures forall (v: nat). i <= v /\ v < n ==>
                        mem v (vertices_in_component t 0 n i))
              (decreases (n - i))
      = if i >= n then ()
        else begin
          aux_dec i;
          assert (same_component_dec t 0 i = true);
          all_in_component (i + 1);
          // vertices_in_component t 0 n i = i :: vertices_in_component t 0 n (i+1)
          // All v with i+1 <= v < n are in the tail (by IH)
          // And i itself is the head
          ()
        end
    in
    all_in_component 0;
    // component_of t 0 n contains all vertices 0..n-1
    assert (forall (v: nat). v < n ==> mem v (component_of t 0 n));

    // Step 3: in_some_component returns true for all v < n when acc = [component_of t 0 n]
    let in_comp_of_0 (v: nat)
      : Lemma (requires v < n)
              (ensures in_some_component v [component_of t 0 n] = true)
      = assert (mem v (component_of t 0 n))
    in

    // Step 4: build_components with i=0 creates exactly [component_of t 0 n]
    // At i=0: 0 is not in acc=[]. Creates component_of t 0 n. acc = [component_of t 0 n].
    // For i=1..n-1: i is in component_of t 0 n, so in_some_component i acc = true. Skip.
    let rec build_one_comp (i: nat{i <= n})
      : Lemma (requires i > 0)
              (ensures build_components t n i [component_of t 0 n] == [component_of t 0 n])
              (decreases (n - i))
      = if i >= n then ()
        else begin
          in_comp_of_0 i;
          assert (in_some_component i [component_of t 0 n] = true);
          build_one_comp (i + 1)
        end
    in

    // At i=0: 0 is not in [], creates component_of t 0 n
    in_some_component_false 0 ([] #(list nat));
    assert (in_some_component 0 ([] #(list nat)) = false);
    // build_components t n 0 [] = build_components t n 1 [component_of t 0 n]
    if n > 1 then build_one_comp 1
    else ()
    // Result: [component_of t 0 n], length = 1

// With n vertices and 1 component, need exactly n-1 edges for tree
let lemma_tree_edge_count (n: nat) (t: list edge)
  : Lemma (requires n > 0 /\
                    is_forest t n /\
                    length (components t n) = 1)
          (ensures length t = n - 1)
  = admit()
