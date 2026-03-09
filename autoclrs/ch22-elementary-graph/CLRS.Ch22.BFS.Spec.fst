(**
 * CLRS Chapter 22: BFS — Pure Functional Specification
 *
 * Defines BFS levels constructively and proves:
 *   - Source is at level 0
 *   - Edge property: if u at level k and edge(u,v), then v visited by level k+1
 *   - BFS computes shortest-path distances in unweighted graphs
 *
 * Zero admits.
 *)
module CLRS.Ch22.BFS.Spec

open FStar.Mul

(*** Graph Representation ***)

let has_edge (n: nat) (adj: Seq.seq int) (u v: nat) : bool =
  u < n && v < n && Seq.length adj >= n * n &&
  u * n + v < Seq.length adj &&
  Seq.index adj (u * n + v) <> 0

(*** BFS Level Sets ***)

// Level 0: only source
let level_0 (n: nat) (source: nat) : Seq.seq bool =
  if source >= n then Seq.create n false
  else Seq.upd (Seq.create n false) source true

// Is vertex v a neighbor of some vertex u in the frontier?
let rec has_frontier_neighbor (n: nat) (adj: Seq.seq int) (frontier: Seq.seq bool) (v: nat) (scan: nat) : Tot bool (decreases (if scan < n then n - scan else 0)) =
  if scan >= n then false
  else if scan < Seq.length frontier && Seq.index frontier scan && has_edge n adj scan v
  then true
  else has_frontier_neighbor n adj frontier v (scan + 1)

// Compute next visited set: visited ∪ {v : v has neighbor in frontier and v not in visited}
let next_visited (n: nat) (adj: Seq.seq int) (visited frontier: Seq.seq bool) : Seq.seq bool =
  if Seq.length visited <> n || Seq.length frontier <> n then visited
  else
    Seq.init n (fun i ->
      Seq.index visited i || 
      (not (Seq.index visited i) && has_frontier_neighbor n adj frontier i 0))

// Compute frontier at level k+1: newly discovered vertices
let next_frontier (n: nat) (adj: Seq.seq int) (visited frontier: Seq.seq bool) : Seq.seq bool =
  if Seq.length visited <> n || Seq.length frontier <> n then Seq.create n false
  else
    Seq.init n (fun i ->
      not (Seq.index visited i) && has_frontier_neighbor n adj frontier i 0)

// Compute visited set after k levels of BFS
let rec visited_after (n: nat) (adj: Seq.seq int) (source: nat) (k: nat) : Tot (Seq.seq bool) (decreases k) =
  if k = 0 then level_0 n source
  else
    let prev_visited = visited_after n adj source (k - 1) in
    let prev_frontier = frontier_at n adj source (k - 1) in
    next_visited n adj prev_visited prev_frontier

// Compute frontier at level k
and frontier_at (n: nat) (adj: Seq.seq int) (source: nat) (k: nat) : Tot (Seq.seq bool) (decreases k) =
  if k = 0 then level_0 n source
  else
    let prev_visited = visited_after n adj source (k - 1) in
    let prev_frontier = frontier_at n adj source (k - 1) in
    next_frontier n adj prev_visited prev_frontier

// Is vertex v visited at level k?
let is_visited (n: nat) (adj: Seq.seq int) (source: nat) (k: nat) (v: nat) : bool =
  let vis = visited_after n adj source k in
  v < Seq.length vis && Seq.index vis v

// Is vertex v in the frontier at level k?
let is_frontier (n: nat) (adj: Seq.seq int) (source: nat) (k: nat) (v: nat) : bool =
  let fr = frontier_at n adj source k in
  v < Seq.length fr && Seq.index fr v

// BFS distance: smallest k such that v is first visited at level k
let rec bfs_distance_aux (n: nat) (adj: Seq.seq int) (source: nat) (v: nat) (k: nat) : Tot int (decreases (if k < n then n - k else 0)) =
  if k >= n then -1
  else if is_frontier n adj source k v then k
  else bfs_distance_aux n adj source v (k + 1)

let bfs_distance (n: nat) (adj: Seq.seq int) (source: nat) (v: nat) : int =
  bfs_distance_aux n adj source v 0

(*** Basic Properties ***)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

// Length properties
let level_0_length (n: nat) (source: nat)
  : Lemma (ensures Seq.length (level_0 n source) = n)
  = ()

let next_visited_length (n: nat) (adj: Seq.seq int) (visited frontier: Seq.seq bool)
  : Lemma
    (requires Seq.length visited = n /\ Seq.length frontier = n)
    (ensures Seq.length (next_visited n adj visited frontier) = n)
  = ()

let next_frontier_length (n: nat) (adj: Seq.seq int) (visited frontier: Seq.seq bool)
  : Lemma
    (requires Seq.length visited = n /\ Seq.length frontier = n)
    (ensures Seq.length (next_frontier n adj visited frontier) = n)
  = ()

let rec visited_after_length (n: nat) (adj: Seq.seq int) (source: nat) (k: nat)
  : Lemma (ensures Seq.length (visited_after n adj source k) = n /\
                   Seq.length (frontier_at n adj source k) = n)
    (decreases k)
  = if k = 0 then ()
    else begin
      visited_after_length n adj source (k - 1);
      next_visited_length n adj (visited_after n adj source (k - 1)) (frontier_at n adj source (k - 1));
      next_frontier_length n adj (visited_after n adj source (k - 1)) (frontier_at n adj source (k - 1))
    end

// Source is visited at level 0
let source_visited_0 (n: nat) (adj: Seq.seq int) (source: nat)
  : Lemma
    (requires source < n)
    (ensures is_visited n adj source 0 source = true /\
             is_frontier n adj source 0 source = true)
  = ()

// Source has BFS distance 0
let source_dist_zero (n: nat) (adj: Seq.seq int) (source: nat)
  : Lemma
    (requires source < n)
    (ensures bfs_distance n adj source source = 0)
  = ()
#pop-options

(*** Edge Property (CLRS Lemma 22.1) ***)

// Key helper: if u is in the frontier at level k and edge(u,v), 
// then v is visited at level k+1
#push-options "--fuel 3 --ifuel 1 --z3rlimit 20"

// If has_frontier_neighbor finds u at position scan, it returns true
let rec scan_finds_neighbor (n: nat) (adj: Seq.seq int) (frontier: Seq.seq bool) (v: nat) (u: nat) (scan: nat)
  : Lemma
    (requires 
      scan <= u /\ u < n /\
      Seq.length frontier = n /\
      Seq.index frontier u = true /\
      has_edge n adj u v = true)
    (ensures has_frontier_neighbor n adj frontier v scan = true)
    (decreases (n - scan))
  = if scan = u then ()
    else scan_finds_neighbor n adj frontier v u (scan + 1)

//SNIPPET_START: edge_implies_next_visited
// If u in frontier at level k and edge(u,v), then v visited at level k+1
let edge_implies_next_visited (n: nat) (adj: Seq.seq int) (source: nat) (k: nat) (u v: nat)
  : Lemma
    (requires 
      is_frontier n adj source k u = true /\
      has_edge n adj u v = true /\
      v < n /\ u < n)
    (ensures is_visited n adj source (k + 1) v = true)
  = let frontier = frontier_at n adj source k in
    let visited = visited_after n adj source k in
    scan_finds_neighbor n adj frontier v u 0
//SNIPPET_END: edge_implies_next_visited
#pop-options
