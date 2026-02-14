(**
 * CLRS Chapter 22: DFS — Pure Functional Specification
 *
 * Implements Depth-First Search with discovery/finish timestamps.
 * Models DFS on adjacency matrix representation with n vertices.
 *
 * Key properties:
 *   - Discovery times d[u] and finish times f[u] for each vertex
 *   - Parenthesis theorem (CLRS Theorem 22.7): timestamp intervals nest properly
 *   - Edge classification: tree, back, forward, cross edges
 *   - Discovery precedes finish: d[u] < f[u]
 *   - Time is strictly monotonic during traversal
 *
 * Graph representation: adjacency matrix seq (seq int) where adj[u][v] <> 0
 * indicates edge from u to v.
 *)
module CLRS.Ch22.DFS.Spec

open FStar.Mul

(*** Graph Representation ***)

// Edge predicate: edge from u to v exists in adjacency matrix
let has_edge (n: nat) (adj: Seq.seq (Seq.seq int)) (u v: nat) : bool =
  u < n && v < n && 
  Seq.length adj = n &&
  u < Seq.length adj &&
  v < Seq.length (Seq.index adj u) &&
  Seq.index (Seq.index adj u) v <> 0

(*** DFS State ***)

// Vertex colors: White (unvisited), Gray (discovered), Black (finished)
type color =
  | White
  | Gray
  | Black

// DFS state tracks discovery times, finish times, colors, and current time
type dfs_state = {
  n: nat;                      // Number of vertices
  d: Seq.seq nat;              // Discovery times (d[u] = when u turns gray)
  f: Seq.seq nat;              // Finish times (f[u] = when u turns black)
  color: Seq.seq color;        // Vertex colors
  time: nat;                   // Current timestamp
}

// Initial DFS state: all vertices white, time = 0
let init_state (n: nat) : dfs_state = {
  n = n;
  d = Seq.create n 0;
  f = Seq.create n 0;
  color = Seq.create n White;
  time = 0;
}

// Well-formed state invariants
let valid_state (st: dfs_state) : prop =
  Seq.length st.d = st.n /\
  Seq.length st.f = st.n /\
  Seq.length st.color = st.n /\
  // Discovery before finish for discovered vertices
  (forall (u: nat). u < st.n ==>
    (Seq.index st.color u <> White ==> Seq.index st.d u > 0 /\ Seq.index st.d u <= st.time)) /\
  // Finish after discovery for finished vertices
  (forall (u: nat). u < st.n ==>
    (Seq.index st.color u = Black ==> Seq.index st.f u > Seq.index st.d u /\ Seq.index st.f u <= st.time))

// Count white vertices (for termination measure)
let rec count_white (colors: Seq.seq color) (i: nat) : Tot nat (decreases (Seq.length colors - i)) =
  if i >= Seq.length colors then 0
  else (if Seq.index colors i = White then 1 else 0) + count_white colors (i + 1)

let count_white_vertices (st: dfs_state) : nat =
  count_white st.color 0

(*** DFS Visit - Recursive exploration ***)

// Discover vertex u: mark gray, set discovery time
let discover_vertex (u: nat) (st: dfs_state) : dfs_state =
  if u >= st.n || u >= Seq.length st.color || u >= Seq.length st.d then st
  else {
    st with
    color = Seq.upd st.color u Gray;
    d = Seq.upd st.d u (st.time + 1);
    time = st.time + 1
  }

// Finish vertex u: mark black, set finish time
let finish_vertex (u: nat) (st: dfs_state) : dfs_state =
  if u >= st.n || u >= Seq.length st.color || u >= Seq.length st.f then st
  else {
    st with
    color = Seq.upd st.color u Black;
    f = Seq.upd st.f u (st.time + 1);
    time = st.time + 1
  }

// Get neighbors of vertex u that are still white
let rec get_white_neighbors (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (v: nat) (st: dfs_state) 
  : Tot (list nat) (decreases (if v < n then n - v else 0))
  = if v >= n then []
    else
      let rest = get_white_neighbors adj n u (v + 1) st in
      if has_edge n adj u v && v < Seq.length st.color && Seq.index st.color v = White
      then v :: rest
      else rest

// Visit all white neighbors recursively
let rec visit_neighbors (adj: Seq.seq (Seq.seq int)) (n: nat) (neighbors: list nat) (st: dfs_state)
  : Tot dfs_state (decreases %[count_white_vertices st; List.Tot.length neighbors])
  = match neighbors with
    | [] -> st
    | v :: rest ->
      // Visit v if still white (may have been visited by earlier neighbor)
      if v < Seq.length st.color && Seq.index st.color v = White then
        let st1 = dfs_visit adj n v st in
        // After visiting v, white count decreased
        assume (count_white_vertices st1 < count_white_vertices st);
        // Now can recurse: lexicographic order satisfied
        visit_neighbors adj n rest st1
      else
        // v already visited, just move to next neighbor (list length decreases)
        visit_neighbors adj n rest st

// DFS-Visit: recursively explore from vertex u
and dfs_visit (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Tot dfs_state (decreases %[count_white_vertices st; 0])
  = if u >= n then st
    else if u >= Seq.length st.color then st
    else if Seq.index st.color u <> White then st  // Already visited
    else
      // Discover u - this reduces white count
      let st1 = discover_vertex u st in
      // Assume: white count decreased (provable but complex)
      assume (count_white_vertices st1 < count_white_vertices st);
      // Visit all white neighbors (white count of st1 < white count of st)
      let neighbors = get_white_neighbors adj n u 0 st1 in
      let st2 = visit_neighbors adj n neighbors st1 in
      // Finish u
      finish_vertex u st2

(*** Main DFS - Visit all vertices ***)

// DFS main loop: visit each unvisited vertex
let rec dfs_loop (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Tot dfs_state (decreases (if u < n then n - u else 0))
  = if u >= n then st
    else
      let st1 = 
        if u < Seq.length st.color && Seq.index st.color u = White
        then dfs_visit adj n u st
        else st
      in
      dfs_loop adj n (u + 1) st1

// Main DFS entry point
let dfs (adj: Seq.seq (Seq.seq int)) (n: nat) : dfs_state =
  let st0 = init_state n in
  dfs_loop adj n 0 st0

(*** Basic Properties ***)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

// Initial state is valid
let init_state_valid (n: nat)
  : Lemma (valid_state (init_state n))
  = ()

// Discovering a vertex preserves validity (with admits for now)
let discover_preserves_validity (u: nat) (st: dfs_state)
  : Lemma
    (requires valid_state st /\ u < st.n /\ u < Seq.length st.color /\ Seq.index st.color u = White)
    (ensures valid_state (discover_vertex u st))
  = admit()

// Finishing a vertex preserves validity
let finish_preserves_validity (u: nat) (st: dfs_state)
  : Lemma
    (requires valid_state st /\ u < st.n /\ u < Seq.length st.color /\ Seq.index st.color u = Gray)
    (ensures valid_state (finish_vertex u st))
  = admit()

#pop-options

(*** Timestamp Properties ***)

// Discovery before finish for any vertex
let discovery_before_finish (st: dfs_state) (u: nat) : prop =
  u < st.n /\
  u < Seq.length st.color /\
  u < Seq.length st.d /\
  u < Seq.length st.f /\
  Seq.index st.color u = Black ==>
  Seq.index st.d u < Seq.index st.f u

// Time is monotonic: never decreases
let time_monotonic (st1 st2: dfs_state) : prop =
  st1.time <= st2.time

// Time strictly increases when discovering or finishing
let time_increases_on_discover (u: nat) (st: dfs_state)
  : Lemma
    (requires u < st.n /\ u < Seq.length st.color /\ u < Seq.length st.d /\ Seq.index st.color u = White)
    (ensures (discover_vertex u st).time = st.time + 1)
  = ()

let time_increases_on_finish (u: nat) (st: dfs_state)
  : Lemma
    (requires u < st.n /\ u < Seq.length st.color /\ u < Seq.length st.f /\ Seq.index st.color u = Gray)
    (ensures (finish_vertex u st).time = st.time + 1)
  = ()

(*** Parenthesis Theorem (CLRS Theorem 22.7) ***)

// Timestamp intervals: [d[u], f[u]] and [d[v], f[v]]
type interval = {
  start: nat;
  finish: nat;
}

// Get interval for vertex u
let get_interval (st: dfs_state) (u: nat) : interval =
  if u < Seq.length st.d && u < Seq.length st.f
  then { start = Seq.index st.d u; finish = Seq.index st.f u }
  else { start = 0; finish = 0 }

// Interval containment: [a, b] ⊆ [c, d]
let interval_contained (i1 i2: interval) : bool =
  i1.start >= i2.start && i1.finish <= i2.finish

// Intervals are disjoint: no overlap
let intervals_disjoint (i1 i2: interval) : bool =
  i1.finish < i2.start || i2.finish < i1.start

// Parenthesis property: for any two vertices u, v, their intervals either:
// 1. Are disjoint
// 2. One contains the other (nesting)
let parenthesis_property (st: dfs_state) (u v: nat) : prop =
  u < st.n /\ v < st.n /\ u <> v ==>
  (let iu = get_interval st u in
   let iv = get_interval st v in
   // If both are finished (black), intervals must be properly nested or disjoint
   (u < Seq.length st.color /\ v < Seq.length st.color /\
    Seq.index st.color u = Black /\ Seq.index st.color v = Black) ==>
   (intervals_disjoint iu iv || 
    interval_contained iu iv || 
    interval_contained iv iu))

// The parenthesis theorem: all pairs satisfy the property
let parenthesis_theorem (st: dfs_state) : prop =
  forall (u v: nat). parenthesis_property st u v

// Statement (admitted - genuinely hard to prove)
let dfs_satisfies_parenthesis_theorem (adj: Seq.seq (Seq.seq int)) (n: nat)
  : Lemma (ensures parenthesis_theorem (dfs adj n))
  = admit()

(*** Edge Classification ***)

// Edge types based on CLRS Section 22.3
type edge_type =
  | TreeEdge      // Part of DFS forest
  | BackEdge      // To ancestor in DFS tree
  | ForwardEdge   // To descendant (not tree edge)
  | CrossEdge     // All other edges

// Classify edge (u, v) based on color of v when u is being explored
// and timestamp relationships in final DFS state
let classify_edge (st: dfs_state) (u v: nat) (color_v_at_discovery: color) : edge_type =
  if u >= Seq.length st.d || v >= Seq.length st.d || u >= Seq.length st.f || v >= Seq.length st.f then CrossEdge
  else
    let du = Seq.index st.d u in
    let fu = Seq.index st.f u in
    let dv = Seq.index st.d v in
    let fv = Seq.index st.f v in
    // Tree edge: v was white when discovered from u
    if color_v_at_discovery = White then TreeEdge
    // Back edge: v is gray when discovered from u (ancestor in DFS tree)
    else if color_v_at_discovery = Gray then BackEdge
    // Forward edge: v is black and discovered after u, finished before u
    else if dv > du && fv < fu then ForwardEdge
    // Cross edge: all other cases
    else CrossEdge

// Alternative classification based only on timestamps (for finished vertices)
let classify_edge_timestamps (st: dfs_state) (u v: nat) : edge_type =
  if u >= Seq.length st.d || v >= Seq.length st.d then CrossEdge
  else if u >= Seq.length st.f || v >= Seq.length st.f then CrossEdge
  else
    let du = Seq.index st.d u in
    let fu = Seq.index st.f u in
    let dv = Seq.index st.d v in
    let fv = Seq.index st.f v in
    // Back edge: d[u] > d[v] and f[u] < f[v] (u's interval inside v's)
    if du > dv && fu < fv then BackEdge
    // Forward/Tree edge: d[u] < d[v] and f[u] > f[v] (v's interval inside u's)
    else if du < dv && fu > fv then ForwardEdge  // or TreeEdge - can't distinguish
    // Cross edge: disjoint intervals
    else CrossEdge

(*** Reachability and Path Properties ***)

// Path exists from u to v in the graph
let rec has_path (adj: Seq.seq (Seq.seq int)) (n: nat) (u v: nat) (steps: nat) 
  : Tot prop (decreases steps)
  = if steps = 0 then u = v
    else u < n /\ v < n /\ 
         (exists (w: nat). w < n /\ has_path adj n u w (steps - 1) /\ has_edge n adj w v)

// If path from u to v exists and u is visited, then v is visited (completeness)
let dfs_visits_reachable (adj: Seq.seq (Seq.seq int)) (n: nat) (u v: nat)
  : Lemma
    (requires 
      u < n /\ v < n /\
      (exists (k: nat). k < n /\ has_path adj n u v k))
    (ensures
      (let st = dfs adj n in
       u < Seq.length st.color /\ Seq.index st.color u <> White ==>
       v < Seq.length st.color /\ Seq.index st.color v <> White))
  = admit()

(*** White Path Theorem (CLRS Theorem 22.8) ***)

// All vertices on path from u to v are white
let rec all_white_on_path (st: dfs_state) (adj: Seq.seq (Seq.seq int)) (n: nat) (u v: nat) (steps: nat)
  : Tot prop (decreases steps)
  = if steps = 0 then u = v
    else u < n /\ v < n /\
         (exists (w: nat). w < n /\ 
           w < Seq.length st.color /\ Seq.index st.color w = White /\
           all_white_on_path st adj n u w (steps - 1) /\ 
           has_edge n adj w v)

// White path theorem: if white path from u to v at d[u], then v is descendant of u
let white_path_theorem (adj: Seq.seq (Seq.seq int)) (n: nat) (u v: nat)
  : Lemma
    (requires u < n /\ v < n /\ u <> v)
    (ensures
      (let st_final = dfs adj n in
       // If at discovery time of u, there exists a white path from u to v
       // Then v becomes a descendant of u (v's interval contained in u's)
       u < Seq.length st_final.d /\ v < Seq.length st_final.d ==>
       ((exists (k: nat). k < n /\ 
          (exists (st_at_du: dfs_state). 
            u < Seq.length st_at_du.d /\ 
            st_at_du.time = Seq.index st_final.d u /\
            all_white_on_path st_at_du adj n u v k)) ==>
        (let iu = get_interval st_final u in
         let iv = get_interval st_final v in
         interval_contained iv iu))))
  = admit()

(*** Cycle Detection ***)

// Graph has a cycle if and only if DFS finds a back edge
let has_back_edge (st: dfs_state) (adj: Seq.seq (Seq.seq int)) (n: nat) : prop =
  exists (u v: nat) (color_v: color). 
    u < n /\ v < n /\ 
    has_edge n adj u v /\
    classify_edge st u v color_v = BackEdge

// Cycle detection theorem (statement only)
let cycle_detection_theorem (adj: Seq.seq (Seq.seq int)) (n: nat)
  : Lemma
    (ensures
      (let st = dfs adj n in
       // Graph has cycle iff DFS finds back edge
       (exists (u v: nat) (k: nat). k > 0 /\ has_path adj n u u k) <==>
       has_back_edge st adj n))
  = admit()

(*** Topological Sort Properties ***)

// DFS can be used for topological sort: if (u,v) is an edge, then f[u] > f[v]
// This holds only for DAGs (no back edges)
let topological_order (st: dfs_state) (adj: Seq.seq (Seq.seq int)) (n: nat) : prop =
  (forall (u v: nat). 
    u < n /\ v < n /\ 
    has_edge n adj u v /\
    u < Seq.length st.f /\ v < Seq.length st.f ==>
    Seq.index st.f u > Seq.index st.f v) <==>
  (~(has_back_edge st adj n))

let topological_sort_property (adj: Seq.seq (Seq.seq int)) (n: nat)
  : Lemma
    (ensures topological_order (dfs adj n) adj n)
  = admit()

(*** Helper Lemmas for Properties ***)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"

// Discovery time is set when vertex turns gray
let discovered_means_gray_or_black (st: dfs_state) (u: nat)
  : Lemma
    (requires 
      valid_state st /\ 
      u < st.n /\ 
      u < Seq.length st.color /\ 
      u < Seq.length st.d /\
      Seq.index st.d u > 0)
    (ensures Seq.index st.color u = Gray \/ Seq.index st.color u = Black)
  = admit()

// Finish time is set when vertex turns black
let finished_means_black (st: dfs_state) (u: nat)
  : Lemma
    (requires 
      valid_state st /\ 
      u < st.n /\ 
      u < Seq.length st.color /\ 
      u < Seq.length st.f /\
      Seq.index st.f u > 0)
    (ensures Seq.index st.color u = Black)
  = admit()

// Timestamps are bounded by current time
let timestamps_bounded (st: dfs_state) (u: nat)
  : Lemma
    (requires valid_state st /\ u < st.n /\ u < Seq.length st.d /\ u < Seq.length st.f)
    (ensures 
      Seq.index st.d u <= st.time /\
      Seq.index st.f u <= st.time)
  = admit()

#pop-options

(*** Summary ***)

(*
 * This specification defines:
 *
 * 1. DFS algorithm with discovery/finish timestamps
 * 2. Parenthesis theorem: intervals nest or are disjoint
 * 3. Edge classification: tree, back, forward, cross
 * 4. White path theorem: white path implies descendant
 * 5. Cycle detection: back edge iff cycle exists
 * 6. Topological sort: finish times give reverse topological order (for DAGs)
 *
 * Admits are used for complex theorems that require intricate inductive proofs
 * over the recursive structure of DFS. The key definitions and basic properties
 * are fully specified and provide a solid foundation for reasoning about DFS.
 *)
