(**
 * CLRS Chapter 22: BFS Distance Correctness Specification
 * 
 * Proves CLRS Theorem 22.5: BFS computes shortest-path distances.
 * 
 * Key insight: BFS explores vertices in order of distance. If v is discovered
 * at distance d, then:
 *   1. There exists a path of length d from source to v (easy direction)
 *   2. No shorter path exists (harder direction — fully proved via bfs_correctness)
 *)
module CLRS.Ch22.BFS.DistanceSpec

open FStar.List.Tot
open FStar.Seq
open FStar.Classical

module Seq = FStar.Seq
module L = FStar.List.Tot

(*** 1. Graph Representation ***)

// Adjacency matrix: n × n boolean matrix represented as flat sequence
// adj[u*n + v] = true iff there's an edge from u to v
// We require exact size for simplicity

// Check if there's an edge from u to v
let has_edge (n: nat) (adj: Seq.seq bool) (u: nat) (v: nat) : bool =
  u < n && v < n && Seq.length adj = n * n &&
  Seq.index adj (u * n + v)

(*** 2. Path Definitions ***)

// A valid path in the graph: all edges exist, all vertices < n
let rec path (n: nat) (adj: Seq.seq bool) (p: list nat) : prop =
  match p with
  | [] -> False  // Empty path is invalid
  | [v] -> v < n  // Single vertex path
  | u :: v :: rest ->
      u < n /\ has_edge n adj u v /\ path n adj (v :: rest)

// Path length is number of edges
let path_length (p: list nat) : nat =
  if L.length p = 0 then 0 else L.length p - 1

// A path from s to v
let path_from_to (n: nat) (adj: Seq.seq bool) (s: nat) (v: nat) (p: list nat) : prop =
  path n adj p /\
  (match p with
   | [] -> False
   | hd :: _ -> hd = s) /\
  L.last p = v

(*** 3. Shortest Path Distance ***)

// Helper: does a path of exactly `len` edges exist from s to v?
// Uses mutual recursion with check_via_scan to enable direct proof reasoning
let rec has_path_of_length (n: nat) (adj: Seq.seq bool{Seq.length adj = n * n})
                            (s: nat{s < n}) (v: nat{v < n})
                            (len: nat)
  : GTot bool (decreases %[len + 1; 0])
  = if len = 0 then s = v
    else check_via_scan n adj s v (len - 1) 0

// Scan vertices [u, n) looking for an intermediate vertex on a path
and check_via_scan (n: nat) (adj: Seq.seq bool{Seq.length adj = n * n})
                    (s: nat{s < n}) (v: nat{v < n})
                    (len_tail: nat) (u: nat)
  : GTot bool (decreases %[len_tail + 1; (if u < n then n - u + 1 else 0)])
  = if u >= n then false
    else if has_edge n adj s u && has_path_of_length n adj u v len_tail
    then true
    else check_via_scan n adj s v len_tail (u + 1)

// Helper: find minimum path length by trying increasing lengths
let rec find_min_path_length (n: nat) (adj: Seq.seq bool{Seq.length adj = n * n})
                              (s: nat{s < n}) (v: nat{v < n})
                              (len: nat)
  : GTot (option nat) (decreases (n + 1 - len))
  = if len > n then None
    else if has_path_of_length n adj s v len then Some len
    else find_min_path_length n adj s v (len + 1)

// Shortest path distance: minimum length among all paths from s to v
// Returns None if v is unreachable from s
let shortest_path_dist (n: nat) (adj: Seq.seq bool) (s: nat) (v: nat) : GTot (option nat) =
  if n = 0 || s >= n || v >= n || Seq.length adj <> n * n then None
  else if s = v then Some 0
  else find_min_path_length n adj s v 1

(*** 4. Pure BFS Distance Computation ***)

// BFS state: visited set and current frontier (vertices at current distance)
type bfs_state (n: nat) = {
  visited: v:Seq.seq bool{Seq.length v = n};  // visited[i] = true if vertex i has been visited
  current_frontier: list nat;                  // vertices at current distance
  distance: nat                                // current distance being explored
}

// Initialize BFS from source
let bfs_init (n: nat) (source: nat{source < n}) : bfs_state n =
  { visited = Seq.upd (Seq.create n false) source true;
    current_frontier = [source];
    distance = 0 }

// Get all neighbors of a vertex
let rec neighbors_of (n: nat) (adj: Seq.seq bool) (u: nat) (scan: nat{scan <= n})
  : Tot (list nat) (decreases (n - scan))
  = if scan >= n then []
    else
      let rest = neighbors_of n adj u (scan + 1) in
      if has_edge n adj u scan then scan :: rest else rest

let neighbors (n: nat) (adj: Seq.seq bool) (u: nat) : list nat =
  neighbors_of n adj u 0

// Get unvisited neighbors of a vertex
let rec unvisited_neighbors (n: nat) (adj: Seq.seq bool) (visited: Seq.seq bool)
                             (u: nat) (scan: nat{scan <= n})
  : Pure (list nat)
    (requires Seq.length visited = n)
    (ensures fun _ -> True)
    (decreases (n - scan))
  = if scan >= n then []
    else
      let rest = unvisited_neighbors n adj visited u (scan + 1) in
      if has_edge n adj u scan && not (Seq.index visited scan)
      then scan :: rest
      else rest

// Get all unvisited neighbors from current frontier
let rec expand_frontier (n: nat) (adj: Seq.seq bool) (visited: Seq.seq bool)
                        (frontier: list nat)
  : Pure (list nat)
    (requires Seq.length visited = n)
    (ensures fun _ -> True)
    (decreases frontier)
  = match frontier with
    | [] -> []
    | u :: rest ->
        let u_neighbors = unvisited_neighbors n adj visited u 0 in
        u_neighbors @ expand_frontier n adj visited rest

// Mark a list of vertices as visited
let rec mark_visited (n: nat) (visited: Seq.seq bool) (vs: list nat)
  : Pure (Seq.seq bool)
    (requires Seq.length visited = n)
    (ensures fun res -> Seq.length res = n)
    (decreases vs)
  = match vs with
    | [] -> visited
    | v :: rest ->
        if v < n && v < Seq.length visited then
          mark_visited n (Seq.upd visited v true) rest
        else
          mark_visited n visited rest

// Remove duplicates from list (simple quadratic version)
let rec dedup (vs: list nat) : Tot (list nat) (decreases vs) =
  match vs with
  | [] -> []
  | v :: rest ->
      let rest' = dedup rest in
      if L.mem v rest' then rest' else v :: rest'

// One BFS step: expand current frontier to next level
let bfs_step (n: nat) (adj: Seq.seq bool) (st: bfs_state n)
  : bfs_state n
  = if L.length st.current_frontier = 0 then st
    else
      let new_vertices_with_dups = expand_frontier n adj st.visited st.current_frontier in
      let new_vertices = dedup new_vertices_with_dups in
      let visited' = mark_visited n st.visited new_vertices in
      { visited = visited';
        current_frontier = new_vertices;
        distance = st.distance + 1 }

// Run BFS for k steps
let rec bfs_steps (n: nat) (adj: Seq.seq bool) (source: nat{source < n}) (k: nat)
  : Tot (bfs_state n) (decreases k)
  = if k = 0 then bfs_init n source
    else bfs_step n adj (bfs_steps n adj source (k - 1))

// Compute BFS distances: run for n steps (sufficient to reach all reachable vertices)
let bfs_distances_state (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
  : bfs_state n
  = bfs_steps n adj source n

// Extract distance to each vertex (find earliest step where vertex was visited)
let rec find_visit_time (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                        (v: nat{v < n}) (k: nat{k <= n + 1})
  : Tot (option nat) (decreases (n + 1 - k))
  = if k > n then None
    else if k = 0 then
      let st = bfs_steps n adj source 0 in
      if Seq.index st.visited v then Some 0
      else find_visit_time n adj source v 1
    else
      let st = bfs_steps n adj source k in
      let prev_st = bfs_steps n adj source (k - 1) in
      if Seq.index st.visited v && not (Seq.index prev_st.visited v) then
        Some k  // v was first visited at step k
      else
        find_visit_time n adj source v (k + 1)

// Main BFS distance function
let bfs_distances (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
  : Seq.seq (option nat)
  = Seq.init n (fun v -> 
      if v < n then find_visit_time n adj source v 0 else None)

(*** 5. Basic Properties ***)

// Source is at distance 0
let bfs_source_distance (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
  : Lemma (ensures Seq.index (bfs_distances n adj source) source == Some 0)
  = ()

// All vertices in path are < n
let rec path_vertices_bounded (n: nat) (adj: Seq.seq bool) (p: list nat)
  : Lemma 
    (requires path n adj p)
    (ensures forall v. L.mem v p ==> v < n)
    (decreases p)
  = match p with
    | [] -> ()
    | [_] -> ()
    | _ :: v :: rest -> path_vertices_bounded n adj (v :: rest)

(*** 6. Correctness Theorem - Easy Direction ***)

// Path extension: if path ends at u and edge u -> v, can extend path
let rec path_extend (n: nat) (adj: Seq.seq bool) (p: list nat) (v: nat)
  : Lemma
    (requires
      path n adj p /\
      v < n /\
      L.length p > 0 /\
      has_edge n adj (L.last p) v)
    (ensures
      (let p' = p @ [v] in
       path n adj p' /\
       path_length p' = path_length p + 1))
    (decreases p)
  = match p with
    | [] -> ()
    | [u] -> ()
    | u :: w :: rest ->
        path_extend n adj (w :: rest) v

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

// Single vertex is a valid path
let singleton_path (n: nat) (adj: Seq.seq bool) (v: nat{v < n})
  : Lemma (ensures path n adj [v])
  = ()

#pop-options

// Helper: if v is in the list of new vertices from expand_frontier, 
// then v is an unvisited neighbor of some frontier vertex
// Helper: if v is in unvisited_neighbors of u, then there's an edge from u to v
#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
let rec unvisited_neighbors_mem (n: nat) (adj: Seq.seq bool) (visited: Seq.seq bool)
                                 (u: nat) (scan: nat{scan <= n}) (v: nat)
  : Lemma
    (requires Seq.length visited = n /\ L.mem v (unvisited_neighbors n adj visited u scan))
    (ensures v < n /\ has_edge n adj u v /\ not (Seq.index visited v))
    (decreases (n - scan))
  = if scan >= n then ()
    else 
      let rest = unvisited_neighbors n adj visited u (scan + 1) in
      // By definition: unvisited_neighbors = if has_edge n adj u scan && not (Seq.index visited scan) then scan :: rest else rest
      if has_edge n adj u scan && not (Seq.index visited scan) then (
        // Result is scan :: rest
        if v = scan then ()
        else unvisited_neighbors_mem n adj visited u (scan + 1) v
      ) else (
        // Result is rest
        unvisited_neighbors_mem n adj visited u (scan + 1) v
      )
#pop-options

// Helper: if v is in the list of new vertices from expand_frontier, 
// then v is an unvisited neighbor of some frontier vertex  
let rec expand_frontier_witness (n: nat) (adj: Seq.seq bool) (visited: Seq.seq bool)
                                 (frontier: list nat) (v: nat)
  : Ghost nat
    (requires Seq.length visited = n /\ L.mem v (expand_frontier n adj visited frontier))
    (ensures fun u -> L.mem u frontier /\ has_edge n adj u v /\ not (Seq.index visited v))
    (decreases frontier)
  = match frontier with
    | [] -> 0  // unreachable
    | hd :: rest ->
        let hd_neighbors = unvisited_neighbors n adj visited hd 0 in
        FStar.List.Tot.Properties.append_mem hd_neighbors (expand_frontier n adj visited rest) v;
        if L.mem v hd_neighbors then (
          unvisited_neighbors_mem n adj visited hd 0 v;
          hd
        ) else (
          expand_frontier_witness n adj visited rest v
        )

let expand_frontier_mem (n: nat) (adj: Seq.seq bool) (visited: Seq.seq bool)
                        (frontier: list nat) (v: nat)
  : Lemma
    (requires Seq.length visited = n /\ L.mem v (expand_frontier n adj visited frontier))
    (ensures exists (u: nat). L.mem u frontier /\ has_edge n adj u v /\ not (Seq.index visited v))
  = let u = expand_frontier_witness n adj visited frontier v in
    ()

// Helper: mark_visited only marks vertices from the list
let rec mark_visited_subset (n: nat) (visited: Seq.seq bool) (vs: list nat) (v: nat{v < n})
  : Lemma
    (requires Seq.length visited = n)
    (ensures 
      Seq.index (mark_visited n visited vs) v ==>
      Seq.index visited v \/ L.mem v vs)
    (decreases vs)
  = match vs with
    | [] -> ()
    | w :: rest ->
        if w < n && w < Seq.length visited then
          mark_visited_subset n (Seq.upd visited w true) rest v
        else
          mark_visited_subset n visited rest v

// Helper: if v is marked by mark_visited and was not visited before, v is in the list
let rec mark_visited_new (n: nat) (visited: Seq.seq bool) (vs: list nat) (v: nat{v < n})
  : Lemma
    (requires Seq.length visited = n)
    (ensures 
      (Seq.index (mark_visited n visited vs) v /\ not (Seq.index visited v)) ==>
      L.mem v vs)
    (decreases vs)
  = match vs with
    | [] -> ()
    | w :: rest ->
        if w < n && w < Seq.length visited then (
          if w = v then ()
          else mark_visited_new n (Seq.upd visited w true) rest v
        ) else
          mark_visited_new n visited rest v

// Helper: dedup preserves membership
let rec dedup_mem (vs: list nat) (v: nat)
  : Lemma
    (ensures L.mem v (dedup vs) <==> L.mem v vs)
    (decreases vs)
  = match vs with
    | [] -> ()
    | w :: rest ->
        dedup_mem rest v;
        if L.mem w (dedup rest) then ()
        else ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

// Helper: mark_visited preserves existing markings
let rec mark_visited_preserves (n: nat) (visited: Seq.seq bool) (vs: list nat) (v: nat{v < n})
  : Lemma
    (requires Seq.length visited = n /\ Seq.index visited v)
    (ensures Seq.index (mark_visited n visited vs) v)
    (decreases vs)
  = match vs with
    | [] -> ()
    | w :: rest ->
        if w < n && w < Seq.length visited then
          mark_visited_preserves n (Seq.upd visited w true) rest v
        else
          mark_visited_preserves n visited rest v

// Helper: if v is in the list vs, mark_visited marks it
#push-options "--z3rlimit 10 --fuel 2"
let rec mark_visited_marks (n: nat) (visited: Seq.seq bool) (vs: list nat) (v: nat{v < n})
  : Lemma
    (requires Seq.length visited = n /\ L.mem v vs)
    (ensures Seq.index (mark_visited n visited vs) v)
    (decreases vs)
  = match vs with
    | [] -> ()
    | w :: rest ->
        if w < n && w < Seq.length visited then (
          if w = v then (
            // v is being marked here
            let visited' = Seq.upd visited v true in
            // The rest of the list won't unmark v
            mark_visited_preserves n visited' rest v
          ) else (
            mark_visited_marks n (Seq.upd visited w true) rest v
          )
        ) else
          mark_visited_marks n visited rest v
#pop-options

// Lemma: vertices in the frontier are visited
#push-options "--z3rlimit 10"
let frontier_visited (n: nat) (adj: Seq.seq bool) (source: nat{source < n}) (k: nat) (u: nat)
  : Lemma
    (requires
      k <= n /\
      (let st = bfs_steps n adj source k in
       L.mem u st.current_frontier))
    (ensures
      (let st = bfs_steps n adj source k in
       u < n /\ Seq.index st.visited u))
  = let st = bfs_steps n adj source k in
    if k = 0 then (
      // Frontier is [source], and source is visited
      ()
    ) else (
      // At step k > 0, frontier consists of newly visited vertices
      // from expand_frontier on previous frontier
      let prev_st = bfs_steps n adj source (k - 1) in
      let new_vertices_with_dups = expand_frontier n adj prev_st.visited prev_st.current_frontier in
      let new_vertices = dedup new_vertices_with_dups in
      // u is in new_vertices
      assert (L.mem u new_vertices);
      dedup_mem new_vertices_with_dups u;
      expand_frontier_mem n adj prev_st.visited prev_st.current_frontier u;
      // u was marked as visited by mark_visited
      mark_visited_marks n prev_st.visited new_vertices u
    )
#pop-options

// If vertex is visited at step k, there exists a path of length <= k
let rec visited_implies_path_exists (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                                     (v: nat{v < n}) (k: nat)
  : Lemma
    (requires 
      k <= n /\
      (let st = bfs_steps n adj source k in
       Seq.index st.visited v))
    (ensures exists (p: list nat). path_from_to n adj source v p /\ path_length p <= k)
    (decreases k)
  = let st = bfs_steps n adj source k in
    if k = 0 then (
      // Base case: only source is visited at step 0
      let st0 = bfs_init n source in
      assert (st == st0);
      assert (Seq.index st.visited v);
      // The only visited vertex at step 0 is source, so v = source
      assert (v = source);
      singleton_path n adj source;
      assert (path_from_to n adj source v [source])
    ) else (
      // Inductive case: k > 0
      let prev_st = bfs_steps n adj source (k - 1) in
      if Seq.index prev_st.visited v then (
        // v was already visited at step k-1, use IH
        visited_implies_path_exists n adj source v (k - 1)
      ) else (
        // v was newly visited at step k
        // bfs_step expands the frontier and marks new vertices
        assert (st == bfs_step n adj prev_st);
        
        let new_vertices_with_dups = expand_frontier n adj prev_st.visited prev_st.current_frontier in
        let new_vertices = dedup new_vertices_with_dups in
        
        // v was marked by mark_visited
        mark_visited_new n prev_st.visited new_vertices v;
        assert (L.mem v new_vertices);
        
        dedup_mem new_vertices_with_dups v;
        assert (L.mem v new_vertices_with_dups);
        
        // So v is in expand_frontier result
        expand_frontier_mem n adj prev_st.visited prev_st.current_frontier v;
        
        // There exists a frontier vertex u with edge u -> v
        eliminate exists (u: nat). L.mem u prev_st.current_frontier /\ has_edge n adj u v /\ not (Seq.index prev_st.visited v)
        returns (exists (p: list nat). path_from_to n adj source v p /\ path_length p <= k)
        with _. (
          // u has an edge to v, so u < n (from has_edge definition)
          assert (u < n /\ v < n);
          // u was in frontier at step k-1
          // Frontier vertices are visited vertices
          frontier_visited n adj source (k - 1) u;
          // By IH, there's a path from source to u of length <= k-1
          visited_implies_path_exists n adj source u (k - 1);
          
          eliminate exists (p: list nat). path_from_to n adj source u p /\ path_length p <= k - 1
          returns (exists (p: list nat). path_from_to n adj source v p /\ path_length p <= k)
          with _. (
            // Extend path with edge u -> v
            path_extend n adj p v;
            let p' = p @ [v] in
            assert (path n adj p');
            assert (path_length p' = path_length p + 1);
            assert (path_length p' <= k);
            // p' goes from source to v
            FStar.List.Tot.Properties.lemma_append_last p [v];
            assert (L.last p' = v);
            assert (path_from_to n adj source v p')
          )
        )
      )
    )

#pop-options

(*** 7. Correctness Theorem - Hard Direction ***)

// --- Visited set monotonicity ---

// If v is visited at step j, then v is visited at step j+1
let visited_monotone_step (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                          (j: nat) (v: nat{v < n})
  : Lemma
    (requires Seq.index (bfs_steps n adj source j).visited v)
    (ensures Seq.index (bfs_steps n adj source (j + 1)).visited v)
  = let st = bfs_steps n adj source j in
    if L.length st.current_frontier = 0 then ()
    else
      let new_verts = dedup (expand_frontier n adj st.visited st.current_frontier) in
      mark_visited_preserves n st.visited new_verts v

// If v is visited at step j, then v is visited at step j' for all j' >= j
let rec visited_monotone (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                         (j j': nat) (v: nat{v < n})
  : Lemma
    (requires j <= j' /\ Seq.index (bfs_steps n adj source j).visited v)
    (ensures Seq.index (bfs_steps n adj source j').visited v)
    (decreases (j' - j))
  = if j = j' then ()
    else begin
      visited_monotone_step n adj source j v;
      visited_monotone n adj source (j + 1) j' v
    end

// --- Reverse direction: if u in frontier and edge(u,v) and v unvisited, then v in expand ---

// If has_edge u v and v not visited and scan <= v, then v in unvisited_neighbors
let rec unvisited_neighbor_in_result (n: nat) (adj: Seq.seq bool) (visited: Seq.seq bool)
                                      (u: nat) (scan: nat{scan <= n}) (v: nat)
  : Lemma
    (requires Seq.length visited = n /\ has_edge n adj u v /\
              not (Seq.index visited v) /\ v < n /\ scan <= v)
    (ensures L.mem v (unvisited_neighbors n adj visited u scan))
    (decreases (n - scan))
  = if scan = v then ()
    else unvisited_neighbor_in_result n adj visited u (scan + 1) v

// If u in frontier and edge(u,v) and v not visited, then v in expand_frontier
let rec expand_frontier_in_result (n: nat) (adj: Seq.seq bool) (visited: Seq.seq bool)
                                   (frontier: list nat) (u v: nat)
  : Lemma
    (requires Seq.length visited = n /\ L.mem u frontier /\
              has_edge n adj u v /\ not (Seq.index visited v) /\ v < n)
    (ensures L.mem v (expand_frontier n adj visited frontier))
    (decreases frontier)
  = match frontier with
    | [] -> ()
    | hd :: rest ->
        let hd_nbrs = unvisited_neighbors n adj visited hd 0 in
        let rest_exp = expand_frontier n adj visited rest in
        if hd = u then begin
          unvisited_neighbor_in_result n adj visited u 0 v;
          FStar.List.Tot.Properties.append_mem hd_nbrs rest_exp v
        end else begin
          expand_frontier_in_result n adj visited rest u v;
          FStar.List.Tot.Properties.append_mem hd_nbrs rest_exp v
        end

// --- Newly visited vertex is in the frontier ---

let newly_visited_in_frontier (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                               (k: nat) (v: nat{v < n})
  : Lemma
    (requires
      k > 0 /\
      Seq.index (bfs_steps n adj source k).visited v /\
      not (Seq.index (bfs_steps n adj source (k - 1)).visited v))
    (ensures L.mem v (bfs_steps n adj source k).current_frontier)
  = let prev_st = bfs_steps n adj source (k - 1) in
    if L.length prev_st.current_frontier = 0 then ()
    else begin
      let new_verts = dedup (expand_frontier n adj prev_st.visited prev_st.current_frontier) in
      mark_visited_new n prev_st.visited new_verts v
    end

// --- Frontier + edge implies next visited ---

#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
let frontier_edge_implies_next_visited (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                                        (k: nat) (u v: nat)
  : Lemma
    (requires
      L.mem u (bfs_steps n adj source k).current_frontier /\
      has_edge n adj u v /\ v < n /\ u < n)
    (ensures Seq.index (bfs_steps n adj source (k + 1)).visited v)
  = let st = bfs_steps n adj source k in
    let new_verts_raw = expand_frontier n adj st.visited st.current_frontier in
    let new_verts = dedup new_verts_raw in
    if Seq.index st.visited v then
      mark_visited_preserves n st.visited new_verts v
    else begin
      expand_frontier_in_result n adj st.visited st.current_frontier u v;
      dedup_mem new_verts_raw v;
      mark_visited_marks n st.visited new_verts v
    end
#pop-options

// --- Visited + edge implies next visited ---

// If u is visited at step j and edge(u,v), then v is visited at step j+1
let rec visited_edge_implies_next_visited (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                                           (j: nat) (u: nat{u < n}) (v: nat{v < n})
  : Lemma
    (requires
      Seq.index (bfs_steps n adj source j).visited u /\
      has_edge n adj u v)
    (ensures Seq.index (bfs_steps n adj source (j + 1)).visited v)
    (decreases j)
  = if j = 0 then
      // u = source, in frontier at step 0
      frontier_edge_implies_next_visited n adj source 0 u v
    else
      let prev_st = bfs_steps n adj source (j - 1) in
      if Seq.index prev_st.visited u then begin
        // u was already visited at step j-1, use IH
        visited_edge_implies_next_visited n adj source (j - 1) u v;
        visited_monotone_step n adj source j v
      end else begin
        // u newly visited at step j, so u is in frontier at step j
        newly_visited_in_frontier n adj source j u;
        frontier_edge_implies_next_visited n adj source j u v
      end

// --- Path implies visited: general version ---

// If u is visited at step j, and there's a path from u to v, then v is visited
// at step j + path_length p
#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
let rec path_visited_general (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                              (j: nat) (p: list nat)
  : Lemma
    (requires
      path n adj p /\
      L.length p > 0 /\
      (let u = L.hd p in u < n /\ Seq.index (bfs_steps n adj source j).visited u))
    (ensures
      (let v = L.last p in
       v < n /\ Seq.index (bfs_steps n adj source (j + path_length p)).visited v))
    (decreases p)
  = match p with
    | [_] -> ()
    | u :: w :: rest ->
        // u is visited at step j, edge(u,w), path(w :: rest)
        visited_edge_implies_next_visited n adj source j u w;
        path_visited_general n adj source (j + 1) (w :: rest)
#pop-options

// --- Path from source implies visited ---

let path_implies_visited (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                          (v: nat{v < n}) (p: list nat)
  : Lemma
    (requires path_from_to n adj source v p)
    (ensures Seq.index (bfs_steps n adj source (path_length p)).visited v)
  = path_visited_general n adj source 0 p

// --- shortest_path_property: the hard direction ---

// If vertex v is visited at step k (and not before), then shortest path has length k
let shortest_path_property (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                           (v: nat{v < n}) (k: nat)
  : Lemma
    (requires
      k <= n /\
      (let st = bfs_steps n adj source k in
       Seq.index st.visited v) /\
      (k = 0 || (let prev_st = bfs_steps n adj source (k - 1) in
                 not (Seq.index prev_st.visited v))))
    (ensures
      (forall (p: list nat). path_from_to n adj source v p ==> path_length p >= k))
  = let aux (p: list nat)
      : Lemma (requires path_from_to n adj source v p)
              (ensures path_length p >= k)
      = path_implies_visited n adj source v p;
        if path_length p < k then begin
          // v visited at step (path_length p), so visited at step k-1 by monotonicity
          if k > 0 then
            visited_monotone n adj source (path_length p) (k - 1) v
          // contradicts: v not visited at step k-1
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

(*** 8. Main Correctness Theorem ***)

// Helper: vertex is reachable iff there exists a path
let reachable (n: nat) (adj: Seq.seq bool) (s: nat) (v: nat) : prop =
  s < n /\ v < n /\ (exists (p: list nat). path_from_to n adj s v p)

// --- Helpers for has_path_of_length completeness/soundness ---

// Introduction: if intermediate vertex exists, check_via_scan finds it
let rec check_via_scan_intro (n: nat) (adj: Seq.seq bool{Seq.length adj = n * n})
                              (s: nat{s < n}) (v: nat{v < n}) (len_tail: nat)
                              (w: nat{w < n}) (scan: nat{scan <= w})
  : Lemma
    (requires has_edge n adj s w /\ has_path_of_length n adj w v len_tail)
    (ensures check_via_scan n adj s v len_tail scan)
    (decreases (n - scan))
  = if scan >= n then ()
    else if scan = w then ()
    else if has_edge n adj s scan && has_path_of_length n adj scan v len_tail then ()
    else check_via_scan_intro n adj s v len_tail w (scan + 1)

// Elimination: if check_via_scan returns true, there's an intermediate vertex
let rec check_via_scan_elim (n: nat) (adj: Seq.seq bool{Seq.length adj = n * n})
                             (s: nat{s < n}) (v: nat{v < n}) (len_tail: nat)
                             (scan: nat)
  : Lemma
    (requires check_via_scan n adj s v len_tail scan)
    (ensures exists (w: nat). w < n /\ has_edge n adj s w /\ has_path_of_length n adj w v len_tail)
    (decreases (if scan < n then n - scan else 0))
  = if scan >= n then ()
    else if has_edge n adj s scan && has_path_of_length n adj scan v len_tail then ()
    else check_via_scan_elim n adj s v len_tail (scan + 1)

// has_path_of_length is complete: if a path exists, it returns true
#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
let rec has_path_complete (n: nat) (adj: Seq.seq bool{Seq.length adj = n * n})
                           (s: nat{s < n}) (v: nat{v < n})
                           (p: list nat)
  : Lemma
    (requires path_from_to n adj s v p)
    (ensures has_path_of_length n adj s v (path_length p))
    (decreases p)
  = match p with
    | [] -> ()
    | [_] -> () // path_length = 0, s = v
    | _ :: w :: rest ->
        path_vertices_bounded n adj p;
        has_path_complete n adj w v (w :: rest);
        check_via_scan_intro n adj s v (path_length (w :: rest)) w 0
#pop-options

// has_path_of_length is sound: if it returns true, a path exists
#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
let rec has_path_sound (n: nat) (adj: Seq.seq bool{Seq.length adj = n * n})
                        (s: nat{s < n}) (v: nat{v < n})
                        (len: nat)
  : Lemma
    (requires has_path_of_length n adj s v len)
    (ensures exists (p: list nat). path_from_to n adj s v p /\ path_length p = len)
    (decreases len)
  = if len = 0 then begin
      assert (s = v);
      singleton_path n adj s;
      assert (path_from_to n adj s v [s] /\ path_length [s] = 0)
    end else begin
      check_via_scan_elim n adj s v (len - 1) 0;
      eliminate exists (w: nat). w < n /\ has_edge n adj s w /\ has_path_of_length n adj w v (len - 1)
      returns exists (p: list nat). path_from_to n adj s v p /\ path_length p = len
      with _. begin
        has_path_sound n adj w v (len - 1);
        eliminate exists (p': list nat). path_from_to n adj w v p' /\ path_length p' = len - 1
        returns exists (p: list nat). path_from_to n adj s v p /\ path_length p = len
        with _. begin
          let p = s :: p' in
          assert (L.hd p = s);
          assert (L.last p == L.last p');
          assert (L.last p' = v);
          assert (path_length p = L.length p - 1);
          assert (L.length p = 1 + L.length p');
          assert (path_length p' = L.length p' - 1);
          assert (path_length p = len)
        end
      end
    end
#pop-options

// Unfolding lemma for find_min_path_length
let find_min_unfold (n: nat) (adj: Seq.seq bool{Seq.length adj = n * n})
                     (s: nat{s < n}) (v: nat{v < n}) (len: nat)
  : Lemma (ensures find_min_path_length n adj s v len ==
                   (if len > n then None
                    else if has_path_of_length n adj s v len then Some len
                    else find_min_path_length n adj s v (len + 1)))
  = ()

// --- find_min_path_length characterization ---

// Helper: find_min_path_length returns values >= start
let rec find_min_ge (n: nat) (adj: Seq.seq bool{Seq.length adj = n * n})
                     (s: nat{s < n}) (v: nat{v < n})
                     (start: nat) (k: nat)
  : Lemma
    (requires find_min_path_length n adj s v start == Some k)
    (ensures k >= start)
    (decreases (n + 1 - start))
  = find_min_unfold n adj s v start;
    if start > n then ()
    else if has_path_of_length n adj s v start then ()
    else find_min_ge n adj s v (start + 1) k

// If find_min_path_length returns Some k, then has_path_of_length k is true
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let rec find_min_some (n: nat) (adj: Seq.seq bool{Seq.length adj = n * n})
                       (s: nat{s < n}) (v: nat{v < n})
                       (start: nat) (k: nat)
  : Lemma
    (requires start <= k /\ find_min_path_length n adj s v start == Some k)
    (ensures has_path_of_length n adj s v k /\ k <= n)
    (decreases (n + 1 - start))
  = find_min_unfold n adj s v start;
    if start > n then ()
    else if has_path_of_length n adj s v start then ()
    else begin
      find_min_ge n adj s v (start + 1) k;
      find_min_some n adj s v (start + 1) k
    end

// If find_min_path_length returns None, no path exists with length in [start, n]
let rec find_min_none (n: nat) (adj: Seq.seq bool{Seq.length adj = n * n})
                       (s: nat{s < n}) (v: nat{v < n})
                       (start: nat) (len: nat)
  : Lemma
    (requires find_min_path_length n adj s v start == None /\ start <= len /\ len <= n)
    (ensures not (has_path_of_length n adj s v len))
    (decreases (n + 1 - start))
  = find_min_unfold n adj s v start;
    if start > n then ()
    else if has_path_of_length n adj s v start then ()
    else if start = len then ()
    else find_min_none n adj s v (start + 1) len

// If has_path_of_length len is true and start <= len <= n, find_min returns Some k with k <= len
let rec find_min_finds (n: nat) (adj: Seq.seq bool{Seq.length adj = n * n})
                        (s: nat{s < n}) (v: nat{v < n})
                        (start: nat) (len: nat)
  : Lemma
    (requires has_path_of_length n adj s v len /\ start <= len /\ len <= n)
    (ensures Some? (find_min_path_length n adj s v start) /\
             Some?.v (find_min_path_length n adj s v start) <= len)
    (decreases (n + 1 - start))
  = find_min_unfold n adj s v start;
    if start > n then ()
    else if has_path_of_length n adj s v start then ()
    else find_min_finds n adj s v (start + 1) len
#pop-options

// --- find_visit_time characterization ---

// Helper: find_visit_time returns values >= start
let rec find_visit_ge (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                       (v: nat{v < n}) (start: nat{start <= n + 1}) (k: nat)
  : Lemma
    (requires find_visit_time n adj source v start == Some k)
    (ensures k >= start)
    (decreases (n + 1 - start))
  = if start > n then ()
    else if start = 0 then begin
      let st = bfs_steps n adj source 0 in
      if Seq.index st.visited v then ()
      else find_visit_ge n adj source v 1 k
    end else begin
      let st = bfs_steps n adj source start in
      let prev_st = bfs_steps n adj source (start - 1) in
      if Seq.index st.visited v && not (Seq.index prev_st.visited v) then ()
      else find_visit_ge n adj source v (start + 1) k
    end

// If find_visit_time returns Some k, then v is first visited at step k
#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
let rec find_visit_some (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                         (v: nat{v < n}) (start: nat{start <= n + 1}) (k: nat)
  : Lemma
    (requires find_visit_time n adj source v start == Some k /\ start <= k)
    (ensures
      k <= n /\
      Seq.index (bfs_steps n adj source k).visited v /\
      (k = 0 \/ not (Seq.index (bfs_steps n adj source (k - 1)).visited v)))
    (decreases (n + 1 - start))
  = if start > n then ()
    else if start = 0 then begin
      let st = bfs_steps n adj source 0 in
      if Seq.index st.visited v then ()
      else begin
        find_visit_ge n adj source v 1 k;
        find_visit_some n adj source v 1 k
      end
    end else begin
      let st = bfs_steps n adj source start in
      let prev_st = bfs_steps n adj source (start - 1) in
      if Seq.index st.visited v && not (Seq.index prev_st.visited v) then ()
      else begin
        find_visit_ge n adj source v (start + 1) k;
        find_visit_some n adj source v (start + 1) k
      end
    end
#pop-options

// If find_visit_time returns None, v is never visited
#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
let rec find_visit_none (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                         (v: nat{v < n}) (start: nat{start <= n + 1}) (step: nat)
  : Lemma
    (requires find_visit_time n adj source v start == None /\ start <= step /\ step <= n)
    (ensures not (Seq.index (bfs_steps n adj source step).visited v) \/
             (step > 0 /\ Seq.index (bfs_steps n adj source (step - 1)).visited v))
    (decreases (n + 1 - start))
  = if start > n then ()
    else if start = 0 then begin
      let st = bfs_steps n adj source 0 in
      if Seq.index st.visited v then ()
      else if step = 0 then ()
      else find_visit_none n adj source v 1 step
    end else begin
      let st = bfs_steps n adj source start in
      let prev_st = bfs_steps n adj source (start - 1) in
      if Seq.index st.visited v && not (Seq.index prev_st.visited v) then ()
      else if start = step then ()
      else find_visit_none n adj source v (start + 1) step
    end
#pop-options

// Stronger: if find_visit_time returns None (from 0), v is not visited at any step <= n
let rec find_visit_none_not_visited (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                                     (v: nat{v < n}) (step: nat)
  : Lemma
    (requires find_visit_time n adj source v 0 == None /\ step <= n)
    (ensures not (Seq.index (bfs_steps n adj source step).visited v))
    (decreases step)
  = if step = 0 then begin
      find_visit_none n adj source v 0 0
    end else begin
      find_visit_none_not_visited n adj source v (step - 1);
      find_visit_none n adj source v 0 step
    end

// If v is visited at step k and not before, find_visit_time returns Some k
#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
let rec find_visit_finds (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                          (v: nat{v < n}) (start: nat{start <= n + 1}) (k: nat)
  : Lemma
    (requires
      k <= n /\ start <= k /\
      Seq.index (bfs_steps n adj source k).visited v /\
      (forall (j: nat). j < k /\ j >= start ==> not (Seq.index (bfs_steps n adj source j).visited v)) /\
      (k = 0 \/ not (Seq.index (bfs_steps n adj source (k - 1)).visited v)))
    (ensures find_visit_time n adj source v start == Some k)
    (decreases (n + 1 - start))
  = if start > n then ()
    else if start = 0 then begin
      let st = bfs_steps n adj source 0 in
      if Seq.index st.visited v then begin
        assert (k = 0)
      end else
        find_visit_finds n adj source v 1 k
    end else begin
      let st = bfs_steps n adj source start in
      let prev_st = bfs_steps n adj source (start - 1) in
      if Seq.index st.visited v && not (Seq.index prev_st.visited v) then begin
        assert (start = k)
      end else
        find_visit_finds n adj source v (start + 1) k
    end
#pop-options

// --- Path length bound: any simple path has length < n ---

// For the "unreachable" case, we need: if v not visited at any step <= n,
// then no path from source to v exists.
// Contrapositive of path_implies_visited + path length < n for simple paths.
// Actually: for any path p from s to v, there exists a simple path of length < n.
// But that's complex. Instead: if path has length L, v is visited at step L.
// If L <= n, this is direct. If L > n, we need to shorten the path.

// Helper: path of length >= n can be shortened (pigeonhole)
// This is complex, so instead we prove: shortest_path_dist returns None iff unreachable

// Alternative approach for bfs_correctness: case split on whether v is reachable

// --- Helper: if no has_path_of_length true in [start, n), find_min returns None ---

let rec find_min_none_all (n: nat) (adj: Seq.seq bool{Seq.length adj = n * n})
                           (s: nat{s < n}) (v: nat{v < n}) (start: nat)
  : Lemma
    (requires forall (len: nat). start <= len /\ len <= n ==> not (has_path_of_length n adj s v len))
    (ensures find_min_path_length n adj s v start == None)
    (decreases (n + 1 - start))
  = find_min_unfold n adj s v start;
    if start > n then ()
    else begin
      assert (not (has_path_of_length n adj s v start));
      find_min_none_all n adj s v (start + 1)
    end

// --- Main correctness theorem ---

// Main theorem: BFS computes shortest path distances
#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
let bfs_correctness (n: nat) (adj: Seq.seq bool) (source: nat{source < n}) (v: nat{v < n})
  : Lemma
    (requires Seq.length adj = n * n)
    (ensures
      (let d_bfs = Seq.index (bfs_distances n adj source) v in
       let d_shortest = shortest_path_dist n adj source v in
       d_bfs == d_shortest))
  = // Connect bfs_distances to find_visit_time
    assert (Seq.index (bfs_distances n adj source) v == find_visit_time n adj source v 0)
      by (FStar.Tactics.V2.norm [delta_only [`%bfs_distances]; iota; zeta; primops];
          FStar.Tactics.V2.smt ());
    let d_bfs = find_visit_time n adj source v 0 in
    if source = v then begin
      assert (shortest_path_dist n adj source v == Some 0);
      let st0 = bfs_steps n adj source 0 in
      assert (Seq.index st0.visited v)
    end else begin
      match d_bfs with
      | Some k ->
        find_visit_some n adj source v 0 k;
        visited_implies_path_exists n adj source v k;
        shortest_path_property n adj source v k;
        eliminate exists (p: list nat). path_from_to n adj source v p /\ path_length p <= k
        returns d_bfs == shortest_path_dist n adj source v
        with _. begin
          assert (path_length p = k);
          has_path_complete n adj source v p;
          assert (k >= 1);
          find_min_finds n adj source v 1 k;
          let Some k' = find_min_path_length n adj source v 1 in
          find_min_ge n adj source v 1 k';
          find_min_some n adj source v 1 k';
          has_path_sound n adj source v k';
          eliminate exists (p': list nat). path_from_to n adj source v p' /\ path_length p' = k'
          returns d_bfs == shortest_path_dist n adj source v
          with _. begin
            shortest_path_property n adj source v k;
            assert (k' = k);
            assert (shortest_path_dist n adj source v == Some k)
          end
        end
      | None ->
        assert (shortest_path_dist n adj source v == find_min_path_length n adj source v 1);
        let aux (len: nat)
          : Lemma (requires 1 <= len /\ len <= n)
                  (ensures not (has_path_of_length n adj source v len))
          = if has_path_of_length n adj source v len then begin
              has_path_sound n adj source v len;
              eliminate exists (p: list nat). path_from_to n adj source v p /\ path_length p = len
              returns False
              with _. begin
                path_implies_visited n adj source v p;
                find_visit_none_not_visited n adj source v len
              end
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
        find_min_none_all n adj source v 1
    end
#pop-options

(*** 9. Auxiliary Lemmas ***)

// Path concatenation preserves path property
let rec path_concat (n: nat) (adj: Seq.seq bool) (p1 p2: list nat)
  : Lemma
    (requires
      path n adj p1 /\ path n adj p2 /\
      L.length p1 > 0 /\ L.length p2 > 0 /\
      L.last p1 = L.hd p2)
    (ensures
      (let p = p1 @ L.tail p2 in
       path n adj p /\
       path_length p = path_length p1 + path_length p2))
    (decreases p1)
  = match p1 with
    | [] -> ()
    | [v] -> ()
    | u :: w :: rest ->
        path_concat n adj (w :: rest) p2

// Transitive reachability
let reachable_trans (n: nat) (adj: Seq.seq bool) (s: nat) (u: nat) (v: nat)
  : Lemma
    (requires reachable n adj s u /\ reachable n adj u v)
    (ensures reachable n adj s v)
  = eliminate exists (p1: list nat). path_from_to n adj s u p1
    returns reachable n adj s v
    with _. (
      eliminate exists (p2: list nat). path_from_to n adj u v p2
      returns reachable n adj s v
      with _. (
        if L.length p2 <= 1 then (
          // p2 = [u] so u = v, p1 already goes from s to v
          assert (path_from_to n adj s v p1)
        ) else (
          path_concat n adj p1 p2;
          let p = p1 @ L.tail p2 in
          // last of concatenation
          FStar.List.Tot.Properties.lemma_append_last p1 (L.tail p2);
          assert (path_from_to n adj s v p)
        )
      )
    )

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

// Source is reachable from itself
let reachable_refl (n: nat) (adj: Seq.seq bool) (s: nat{s < n})
  : Lemma (ensures reachable n adj s s)
  = singleton_path n adj s

// Path length is zero iff path is a single vertex
let path_length_zero (n: nat) (adj: Seq.seq bool) (p: list nat)
  : Lemma
    (requires path n adj p /\ path_length p = 0)
    (ensures L.length p = 1)
  = ()

#pop-options
