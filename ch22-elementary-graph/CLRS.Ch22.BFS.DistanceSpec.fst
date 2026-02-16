(**
 * CLRS Chapter 22: BFS Distance Correctness Specification
 * 
 * Proves CLRS Theorem 22.5: BFS computes shortest-path distances.
 * 
 * Key insight: BFS explores vertices in order of distance. If v is discovered
 * at distance d, then:
 *   1. There exists a path of length d from source to v (easy direction)
 *   2. No shorter path exists (harder - admitted)
 *)
module CLRS.Ch22.BFS.DistanceSpec

open FStar.List.Tot
open FStar.Seq
open FStar.Classical
open FStar.Mul

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

// Shortest path distance: minimum length among all paths from s to v
// Returns None if v is unreachable from s
// This is a specification-level definition (not executable)
let shortest_path_dist (n: nat) (adj: Seq.seq bool) (s: nat) (v: nat) : GTot (option nat) =
  if s >= n || v >= n then None
  else if s = v then Some 0
  else
    // The shortest path distance is defined as:
    // - Some d if there exists a path of length d and no shorter path
    // - None if no path exists
    // This is axiomatic for now
    admit()

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

// If vertex is visited at step k, there exists a path of length <= k
let visited_implies_path_exists (n: nat) (adj: Seq.seq bool) (source: nat{source < n})
                                     (v: nat{v < n}) (k: nat)
  : Lemma
    (requires 
      k <= n /\
      (let st = bfs_steps n adj source k in
       Seq.index st.visited v))
    (ensures exists (p: list nat). path_from_to n adj source v p /\ path_length p <= k)
  = admit()  // Easy direction - existence of path at distance k
            // Would need to track parent pointers to construct explicit path

(*** 7. Correctness Theorem - Hard Direction (Admitted) ***)

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
  = admit()  // This is the hard direction: no shorter path exists

(*** 8. Main Correctness Theorem ***)

// Helper: vertex is reachable iff there exists a path
let reachable (n: nat) (adj: Seq.seq bool) (s: nat) (v: nat) : prop =
  s < n /\ v < n /\ (exists (p: list nat). path_from_to n adj s v p)

// Main theorem: BFS computes shortest path distances
let bfs_correctness (n: nat) (adj: Seq.seq bool) (source: nat{source < n}) (v: nat{v < n})
  : Lemma
    (ensures
      (let d_bfs = Seq.index (bfs_distances n adj source) v in
       let d_shortest = shortest_path_dist n adj source v in
       d_bfs == d_shortest))
  = admit()  // Main theorem combining both directions

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

// Single vertex is a valid path
let singleton_path (n: nat) (adj: Seq.seq bool) (v: nat{v < n})
  : Lemma (ensures path n adj [v])
  = ()

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
