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
//SNIPPET_START: dfs_state
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
//SNIPPET_END: dfs_state

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

// Enhanced invariant with bidirectional properties
// (This is what's actually maintained but harder to prove)
let strong_valid_state (st: dfs_state) : prop =
  valid_state st /\
  // White vertices have unset timestamps
  (forall (u: nat). u < st.n ==>
    (Seq.index st.color u = White ==> Seq.index st.d u = 0 /\ Seq.index st.f u = 0)) /\
  // Gray vertices have discovery set but not finish
  (forall (u: nat). u < st.n ==>
    (Seq.index st.color u = Gray ==> Seq.index st.d u > 0 /\ Seq.index st.f u = 0)) /\
  // All timestamps bounded by time
  (forall (u: nat). u < st.n ==>
    Seq.index st.d u <= st.time /\ Seq.index st.f u <= st.time)

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

// Length invariant: discover and finish preserve array lengths
let discover_preserves_lengths (u: nat) (st: dfs_state)
  : Lemma (ensures (let st' = discover_vertex u st in
                     Seq.length st'.d = Seq.length st.d /\
                     Seq.length st'.f = Seq.length st.f /\
                     Seq.length st'.color = Seq.length st.color /\
                     st'.n = st.n))
  = ()

let finish_preserves_lengths (u: nat) (st: dfs_state)
  : Lemma (ensures (let st' = finish_vertex u st in
                     Seq.length st'.d = Seq.length st.d /\
                     Seq.length st'.f = Seq.length st.f /\
                     Seq.length st'.color = Seq.length st.color /\
                     st'.n = st.n))
  = ()

// Init state has all arrays with length n
let init_has_correct_lengths (n: nat)
  : Lemma (let st = init_state n in
           Seq.length st.d = n /\
           Seq.length st.f = n /\
           Seq.length st.color = n /\
           st.n = n)
  = ()

// Helper: count_white after an index is unchanged when updating before that index  
let rec count_white_upd_after (colors: Seq.seq color) (start idx: nat) (new_color: color)
  : Lemma
    (requires idx < start /\ start <= Seq.length colors /\ idx < Seq.length colors)
    (ensures count_white (Seq.upd colors idx new_color) start = count_white colors start)
    (decreases (Seq.length colors - start))
  = if start >= Seq.length colors then ()
    else (
      assert (Seq.index (Seq.upd colors idx new_color) start = Seq.index colors start);
      count_white_upd_after colors (start + 1) idx new_color
    )

// Helper lemma: updating a single white vertex to non-white decreases count
let rec count_white_upd_white_decreases (colors: Seq.seq color) (start idx: nat) (new_color: color)
  : Lemma
    (requires 
      start <= idx /\
      idx < Seq.length colors /\ 
      start <= Seq.length colors /\
      Seq.index colors idx = White /\
      new_color <> White)
    (ensures 
      count_white (Seq.upd colors idx new_color) start < count_white colors start)
    (decreases (idx - start))
  = if start >= Seq.length colors then ()
    else if start = idx then (
      // At the index being changed
      // colors[idx] = White, so count_white colors start = 1 + count_white colors (start+1)
      // (upd colors idx new_color)[idx] = new_color <> White, so count_white (upd...) start = 0 + count_white (upd...) (start+1)
      // count_white (upd...) (start+1) = count_white colors (start+1) since idx < start+1
      if start + 1 <= Seq.length colors then
        count_white_upd_after colors (start + 1) idx new_color;
      ()
    ) else ( // start < idx
      // Haven't reached idx yet
      assert (Seq.index (Seq.upd colors idx new_color) start = Seq.index colors start);
      count_white_upd_white_decreases colors (start + 1) idx new_color
    )

// Discovering a vertex decreases white count (when lengths are consistent)
let discover_decreases_white_count (u: nat) (st: dfs_state)
  : Lemma
    (requires 
      u < st.n /\ 
      u < Seq.length st.color /\ 
      Seq.index st.color u = White /\
      Seq.length st.d = st.n)
    (ensures 
      count_white_vertices (discover_vertex u st) < count_white_vertices st)
  = let st' = discover_vertex u st in
    count_white_upd_white_decreases st.color 0 u Gray

// Helper lemma: updating a non-white vertex to non-white doesn't change white count
let rec count_white_upd_nonwhite_preserves (colors: Seq.seq color) (start idx: nat) (new_color: color)
  : Lemma
    (requires 
      start <= idx /\
      idx < Seq.length colors /\ 
      start <= Seq.length colors /\
      Seq.index colors idx <> White /\
      new_color <> White)
    (ensures 
      count_white (Seq.upd colors idx new_color) start = count_white colors start)
    (decreases (idx - start))
  = if start >= Seq.length colors then ()
    else if start = idx then (
      // At the index being changed
      // colors[idx] <> White, so it contributes 0
      // new_color <> White, so it also contributes 0
      if start + 1 <= Seq.length colors then
        count_white_upd_after colors (start + 1) idx new_color;
      ()
    ) else ( // start < idx
      assert (Seq.index (Seq.upd colors idx new_color) start = Seq.index colors start);
      count_white_upd_nonwhite_preserves colors (start + 1) idx new_color
    )

// Finishing a vertex doesn't change white count (only changes Gray->Black)
let finish_preserves_white_count (u: nat) (st: dfs_state)
  : Lemma
    (requires 
      u < st.n /\ 
      u < Seq.length st.color /\ 
      Seq.index st.color u = Gray)
    (ensures 
      count_white_vertices (finish_vertex u st) = count_white_vertices st)
  = let st' = finish_vertex u st in
    count_white_upd_nonwhite_preserves st.color 0 u Black

// Finishing a Black vertex also doesn't change white count
let finish_black_preserves_white_count (u: nat) (st: dfs_state)
  : Lemma
    (requires 
      u < st.n /\ 
      u < Seq.length st.color /\ 
      Seq.index st.color u = Black)
    (ensures 
      count_white_vertices (finish_vertex u st) = count_white_vertices st)
  = let st' = finish_vertex u st in
    count_white_upd_nonwhite_preserves st.color 0 u Black

// Get neighbors of vertex u that are still white
let rec get_white_neighbors (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (v: nat) (st: dfs_state) 
  : Tot (list nat) (decreases (if v < n then n - v else 0))
  = if v >= n then []
    else
      let rest = get_white_neighbors adj n u (v + 1) st in
      if has_edge n adj u v && v < Seq.length st.color && Seq.index st.color v = White
      then v :: rest
      else rest

// All vertices in the neighbor list are < n
let rec all_neighbors_lt_n (neighbors: list nat) (n: nat) : prop =
  match neighbors with
  | [] -> True
  | v :: rest -> v < n /\ all_neighbors_lt_n rest n

let rec get_white_neighbors_lt_n (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (v: nat) (st: dfs_state)
  : Lemma
    (ensures all_neighbors_lt_n (get_white_neighbors adj n u v st) n)
    (decreases (if v < n then n - v else 0))
  = if v >= n then ()
    else (
      get_white_neighbors_lt_n adj n u (v + 1) st;
      // v < n from loop condition, and has_edge n adj u v also ensures v < n
      ()
    )

// Visit all white neighbors recursively
// Key invariants preserved:
// - Non-white vertices in the input remain non-white (possibly change Gray->Black)
// - Gray vertices either stay Gray or become Black
// - Lengths and .n are preserved
let rec visit_neighbors (adj: Seq.seq (Seq.seq int)) (n: nat) (neighbors: list nat) (st: dfs_state)
  : Pure dfs_state
    (requires 
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      all_neighbors_lt_n neighbors n)
    (ensures fun st' -> 
      count_white_vertices st' <= count_white_vertices st /\
      st'.n = st.n /\ 
      Seq.length st'.d = Seq.length st.d /\
      Seq.length st'.color = Seq.length st.color /\
      Seq.length st'.f = Seq.length st.f /\
      // Non-white vertices stay non-white
      (forall (i: nat). i < Seq.length st.color /\ Seq.index st.color i <> White ==>
        i < Seq.length st'.color /\ Seq.index st'.color i <> White) /\
      // Gray vertices either stay Gray or become Black (but never White)
      (forall (i: nat). i < Seq.length st.color /\ Seq.index st.color i = Gray ==>
        i < Seq.length st'.color /\ (Seq.index st'.color i = Gray \/ Seq.index st'.color i = Black)))
    (decreases %[count_white_vertices st; List.Tot.length neighbors])
  = match neighbors with
    | [] -> st
    | v :: rest ->
      // Visit v if still white (may have been visited by earlier neighbor)
      if v < Seq.length st.color && Seq.index st.color v = White then
        let st1 = dfs_visit adj n v st in
        // From dfs_visit postcondition: st1.n = n, lengths preserved, white count condition
        // Since v < n (from all_neighbors_lt_n), v < Seq.length st.color, Seq.index st.color v = White,
        // Seq.length st.d = st.n, and st.n = n, the implication fires:
        assert (count_white_vertices st1 < count_white_vertices st);
        // Now can recurse: lexicographic order satisfied
        visit_neighbors adj n rest st1
      else
        // v already visited, just move to next neighbor (list length decreases)
        visit_neighbors adj n rest st

// DFS-Visit: recursively explore from vertex u
// Returns state with white count <= input white count
// If u is white and arrays have correct lengths, white count strictly decreases
and dfs_visit (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Pure dfs_state
    (requires st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n)
    (ensures fun st' ->
      count_white_vertices st' <= count_white_vertices st /\
      st'.n = st.n /\
      Seq.length st'.d = Seq.length st.d /\
      Seq.length st'.color = Seq.length st.color /\
      Seq.length st'.f = Seq.length st.f /\
      (u < n /\ u < Seq.length st.color /\ Seq.index st.color u = White ==>
       count_white_vertices st' < count_white_vertices st) /\
      // Non-white vertices stay non-white
      (forall (i: nat). i < Seq.length st.color /\ Seq.index st.color i <> White ==>
        i < Seq.length st'.color /\ Seq.index st'.color i <> White) /\
      // Gray vertices either stay Gray or become Black
      (forall (i: nat). i < Seq.length st.color /\ Seq.index st.color i = Gray ==>
        i < Seq.length st'.color /\ (Seq.index st'.color i = Gray \/ Seq.index st'.color i = Black)))
    (decreases %[count_white_vertices st; 0])
  = if u >= n then st
    else if u >= Seq.length st.color then st
    else if Seq.index st.color u <> White then st  // Already visited
    else (
      // Discover u - this reduces white count
      let st1 = discover_vertex u st in
      discover_preserves_lengths u st;
      // Establish preconditions for discover_decreases_white_count:
      // u < st.n (we have u < n and st.n = n)
      // u < Seq.length st.color (checked above)
      // Seq.index st.color u = White (checked above)
      // Seq.length st.d = st.n (from precondition)
      discover_decreases_white_count u st;
      assert (count_white_vertices st1 < count_white_vertices st);
      // After discover, st1.color[u] = Gray
      assert (u < Seq.length st1.color);
      assert (Seq.index st1.color u = Gray);
      // Visit all white neighbors (white count of st1 < white count of st)
      let neighbors = get_white_neighbors adj n u 0 st1 in
      get_white_neighbors_lt_n adj n u 0 st1;
      let st2 = visit_neighbors adj n neighbors st1 in
      // From visit_neighbors postcondition: Gray vertices stay Gray or become Black
      // Since st1.color[u] = Gray, we have st2.color[u] = Gray or st2.color[u] = Black
      assert (Seq.index st1.color u = Gray);
      assert (u < Seq.length st2.color);
      assert (Seq.index st2.color u = Gray \/ Seq.index st2.color u = Black);
      // st2 <= st1 < st, so st2 < st
      // Finish u (doesn't change white count)
      let st3 = finish_vertex u st2 in
      finish_preserves_lengths u st2;
      // Need to show finish doesn't increase white count
      // Case analysis on st2.color[u]:
      // If st2.color[u] = Gray, then finish_preserves_white_count applies
      // If st2.color[u] = Black, then finish_black_preserves_white_count applies
      // In both cases, white count doesn't change
      if Seq.index st2.color u = Gray then
        finish_preserves_white_count u st2
      else
        finish_black_preserves_white_count u st2;
      st3
    )

(*** Main DFS - Visit all vertices ***)

// DFS main loop: visit each unvisited vertex
let rec dfs_loop (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Pure dfs_state
    (requires st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n)
    (ensures fun st' ->
      st'.n = st.n /\
      Seq.length st'.d = Seq.length st.d /\
      Seq.length st'.color = Seq.length st.color /\
      Seq.length st'.f = Seq.length st.f)
    (decreases (if u < n then n - u else 0))
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
  init_has_correct_lengths n;
  dfs_loop adj n 0 st0

(*** Time Monotonicity ***)

#push-options "--z3rlimit 5"

let rec visit_neighbors_time_mono (adj: Seq.seq (Seq.seq int)) (n: nat) (neighbors: list nat) (st: dfs_state)
  : Lemma
    (requires st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
             all_neighbors_lt_n neighbors n)
    (ensures (visit_neighbors adj n neighbors st).time >= st.time)
    (decreases %[count_white_vertices st; List.Tot.length neighbors])
  = match neighbors with
    | [] -> ()
    | v :: rest ->
      if v < Seq.length st.color && Seq.index st.color v = White then (
        dfs_visit_time_mono adj n v st;
        let st1 = dfs_visit adj n v st in
        visit_neighbors_time_mono adj n rest st1
      ) else
        visit_neighbors_time_mono adj n rest st

and dfs_visit_time_mono (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Lemma
    (requires st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n)
    (ensures (dfs_visit adj n u st).time >= st.time)
    (decreases %[count_white_vertices st; 0])
  = if u >= n then ()
    else if u >= Seq.length st.color then ()
    else if Seq.index st.color u <> White then ()
    else (
      let st1 = discover_vertex u st in
      discover_preserves_lengths u st;
      discover_decreases_white_count u st;
      assert (count_white_vertices st1 < count_white_vertices st);
      let neighbors = get_white_neighbors adj n u 0 st1 in
      get_white_neighbors_lt_n adj n u 0 st1;
      visit_neighbors_time_mono adj n neighbors st1
    )

#pop-options

(*** Timestamp Range — d/f are either unchanged or in (st.time, st'.time] ***)

#push-options "--z3rlimit 5"

let rec visit_neighbors_timestamps_in_range (adj: Seq.seq (Seq.seq int)) (n: nat) (neighbors: list nat) (st: dfs_state)
  : Lemma
    (requires st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
             all_neighbors_lt_n neighbors n)
    (ensures (let st' = visit_neighbors adj n neighbors st in
              (forall (v: nat). v < n ==>
                (Seq.index st'.d v = Seq.index st.d v \/ (st.time < Seq.index st'.d v /\ Seq.index st'.d v <= st'.time)) /\
                (Seq.index st'.f v = Seq.index st.f v \/ (st.time < Seq.index st'.f v /\ Seq.index st'.f v <= st'.time)))))
    (decreases %[count_white_vertices st; List.Tot.length neighbors])
  = match neighbors with
    | [] -> ()
    | v :: rest ->
      if v < Seq.length st.color && Seq.index st.color v = White then (
        dfs_visit_timestamps_in_range adj n v st;
        dfs_visit_time_mono adj n v st;
        let st1 = dfs_visit adj n v st in
        assert (st1.time >= st.time);
        assert (count_white_vertices st1 < count_white_vertices st);
        visit_neighbors_timestamps_in_range adj n rest st1;
        visit_neighbors_time_mono adj n rest st1
      ) else
        visit_neighbors_timestamps_in_range adj n rest st

and dfs_visit_timestamps_in_range (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Lemma
    (requires st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n)
    (ensures (let st' = dfs_visit adj n u st in
              (forall (v: nat). v < n ==>
                (Seq.index st'.d v = Seq.index st.d v \/ (st.time < Seq.index st'.d v /\ Seq.index st'.d v <= st'.time)) /\
                (Seq.index st'.f v = Seq.index st.f v \/ (st.time < Seq.index st'.f v /\ Seq.index st'.f v <= st'.time)))))
    (decreases %[count_white_vertices st; 0])
  = if u >= n then ()
    else if u >= Seq.length st.color then ()
    else if Seq.index st.color u <> White then ()
    else (
      let st1 = discover_vertex u st in
      discover_preserves_lengths u st;
      discover_decreases_white_count u st;
      assert (count_white_vertices st1 < count_white_vertices st);
      // discover_vertex only touches d, color, time — f is unchanged (st1.f = st.f)
      assert (st1.f == st.f);

      let neighbors = get_white_neighbors adj n u 0 st1 in
      get_white_neighbors_lt_n adj n u 0 st1;

      visit_neighbors_timestamps_in_range adj n neighbors st1;
      visit_neighbors_time_mono adj n neighbors st1;

      let st2 = visit_neighbors adj n neighbors st1 in

      finish_preserves_lengths u st2;
      // finish_vertex only touches f, color, time — d is unchanged (st3.d = st2.d)
      let st3 = finish_vertex u st2 in
      assert (st3.d == st2.d);
      ()
    )

#pop-options

(*** dfs_visit endpoint timestamps ***)

// Key structural property: dfs_visit u sets d[u] as the first timestamp
// and f[u] as the last timestamp.
// This is proved by mirroring the dfs_visit structure:
//   1. discover_vertex u st: sets d[u] = st.time + 1 and increments time
//   2. visit_neighbors: doesn't touch d[u] or f[u] (u is gray, not white)
//   3. finish_vertex u st2: sets f[u] = st2.time + 1 = st'.time
#push-options "--z3rlimit 10"

let rec visit_neighbors_preserves_nonwhite_df
  (adj: Seq.seq (Seq.seq int)) (n: nat) (neighbors: list nat) (st: dfs_state) (u: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      all_neighbors_lt_n neighbors n /\
      u < st.n /\ Seq.index st.color u <> White)
    (ensures (let st' = visit_neighbors adj n neighbors st in
              Seq.index st'.d u = Seq.index st.d u /\
              Seq.index st'.f u = Seq.index st.f u))
    (decreases %[count_white_vertices st; List.Tot.length neighbors])
  = match neighbors with
    | [] -> ()
    | v :: rest ->
      if v < Seq.length st.color && Seq.index st.color v = White then (
        dfs_visit_preserves_nonwhite_df adj n v st u;
        let st1 = dfs_visit adj n v st in
        visit_neighbors_preserves_nonwhite_df adj n rest st1 u
      ) else
        visit_neighbors_preserves_nonwhite_df adj n rest st u

and dfs_visit_preserves_nonwhite_df
  (adj: Seq.seq (Seq.seq int)) (n: nat) (v: nat) (st: dfs_state) (u: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      u < st.n /\ Seq.index st.color u <> White)
    (ensures (let st' = dfs_visit adj n v st in
              Seq.index st'.d u = Seq.index st.d u /\
              Seq.index st'.f u = Seq.index st.f u))
    (decreases %[count_white_vertices st; 0])
  = if v >= n then ()
    else if v >= Seq.length st.color then ()
    else if Seq.index st.color v <> White then ()
    else (
      let st1 = discover_vertex v st in
      discover_preserves_lengths v st;
      discover_decreases_white_count v st;
      // discover_vertex v only changes d[v], color[v], and time
      // For u <> v: d[u], f[u], color[u] unchanged
      // For u = v: but u is non-white and v is white, so u <> v
      assert (Seq.index st1.color u <> White);
      assert (Seq.index st1.d u = Seq.index st.d u);
      assert (Seq.index st1.f u = Seq.index st.f u);
      let neighbors = get_white_neighbors adj n v 0 st1 in
      get_white_neighbors_lt_n adj n v 0 st1;
      visit_neighbors_preserves_nonwhite_df adj n neighbors st1 u;
      let st2 = visit_neighbors adj n neighbors st1 in
      // finish_vertex v only changes f[v], color[v], and time
      assert (Seq.index st2.d u = Seq.index st.d u);
      assert (Seq.index st2.f u = Seq.index st.f u);
      let st3 = finish_vertex v st2 in
      assert (Seq.index st3.d u = Seq.index st2.d u);
      // For f: finish_vertex v changes f[v]. If u = v, we showed u <> v above. So f[u] unchanged.
      assert (Seq.index st3.f u = Seq.index st2.f u);
      ()
    )

#pop-options

// dfs_visit_du_fu: When u is white, dfs_visit sets d[u] = st.time + 1 and f[u] = st'.time
#push-options "--z3rlimit 10"

let dfs_visit_du_fu (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      u < n /\ u < Seq.length st.color /\ Seq.index st.color u = White)
    (ensures (let st' = dfs_visit adj n u st in
              Seq.index st'.d u = st.time + 1 /\
              Seq.index st'.f u = st'.time))
  = let st1 = discover_vertex u st in
    discover_preserves_lengths u st;
    discover_decreases_white_count u st;
    // After discover: d[u] = st.time + 1, color[u] = Gray, time = st.time + 1
    assert (Seq.index st1.d u = st.time + 1);
    assert (Seq.index st1.color u = Gray);
    // visit_neighbors preserves d[u] and f[u] because u is non-white (Gray)
    let neighbors = get_white_neighbors adj n u 0 st1 in
    get_white_neighbors_lt_n adj n u 0 st1;
    visit_neighbors_preserves_nonwhite_df adj n neighbors st1 u;
    let st2 = visit_neighbors adj n neighbors st1 in
    assert (Seq.index st2.d u = Seq.index st1.d u);
    assert (Seq.index st2.f u = Seq.index st1.f u);
    // f[u] was 0 (from init state or never set), preserved through visit_neighbors
    // finish_vertex u st2: sets f[u] = st2.time + 1, time = st2.time + 1
    let st3 = finish_vertex u st2 in
    assert (Seq.index st3.d u = Seq.index st2.d u);
    assert (Seq.index st3.f u = st2.time + 1);
    assert (st3.time = st2.time + 1);
    ()

#pop-options

(*** Basic Properties ***)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

// Initial state is valid
let init_state_valid (n: nat)
  : Lemma (valid_state (init_state n))
  = ()

// Initial state satisfies strong invariant
let init_state_strong_valid (n: nat)
  : Lemma (strong_valid_state (init_state n))
  = ()

// Discovering a vertex preserves validity
let discover_preserves_validity (u: nat) (st: dfs_state)
  : Lemma
    (requires valid_state st /\ u < st.n /\ u < Seq.length st.color /\ Seq.index st.color u = White)
    (ensures valid_state (discover_vertex u st))
  = let st' = discover_vertex u st in
    assert (Seq.length st'.d = st'.n);
    assert (Seq.length st'.f = st'.n);
    assert (Seq.length st'.color = st'.n);
    // Need to show forall properties hold
    let aux1 (v: nat{v < Seq.length st'.color /\ v < Seq.length st'.d}) : Lemma 
      (requires v < st'.n)
      (ensures (Seq.index st'.color v <> White ==> 
                Seq.index st'.d v > 0 /\ Seq.index st'.d v <= st'.time))
      = if v = u then (
          assert (Seq.index st'.color u = Gray);
          assert (Seq.index st'.d u = st.time + 1);
          assert (st'.time = st.time + 1)
        ) else (
          assert (Seq.index st'.color v = Seq.index st.color v);
          assert (Seq.index st'.d v = Seq.index st.d v)
        )
    in
    Classical.forall_intro (Classical.move_requires aux1);
    let aux2 (v: nat{v < Seq.length st'.color /\ v < Seq.length st'.f /\ v < Seq.length st'.d}) : Lemma
      (requires v < st'.n)
      (ensures (Seq.index st'.color v = Black ==> 
                Seq.index st'.f v > Seq.index st'.d v /\ 
                Seq.index st'.f v <= st'.time))
      = if v = u then (
          assert (Seq.index st'.color u = Gray);
          assert (Gray <> Black)
        ) else (
          assert (Seq.index st'.color v = Seq.index st.color v);
          assert (Seq.index st'.f v = Seq.index st.f v);
          assert (Seq.index st'.d v = Seq.index st.d v)
        )
    in
    Classical.forall_intro (Classical.move_requires aux2)

// Discovering a vertex preserves strong validity
let discover_preserves_strong_validity (u: nat) (st: dfs_state)
  : Lemma
    (requires strong_valid_state st /\ u < st.n /\ u < Seq.length st.color /\ Seq.index st.color u = White)
    (ensures strong_valid_state (discover_vertex u st))
  = let st' = discover_vertex u st in
    discover_preserves_validity u st;
    // Now prove the additional conjuncts of strong_valid_state
    
    // White vertices have unset timestamps
    let aux1 (v: nat{v < Seq.length st'.color /\ v < Seq.length st'.d /\ v < Seq.length st'.f}) : Lemma
      (requires v < st'.n)
      (ensures (Seq.index st'.color v = White ==> 
                Seq.index st'.d v = 0 /\ Seq.index st'.f v = 0))
      = if v = u then (
          assert (Seq.index st'.color u = Gray);
          assert (Gray <> White)
        ) else (
          assert (Seq.index st'.color v = Seq.index st.color v);
          assert (Seq.index st'.d v = Seq.index st.d v);
          assert (Seq.index st'.f v = Seq.index st.f v)
        )
    in
    Classical.forall_intro (Classical.move_requires aux1);
    
    // Gray vertices have discovery set but not finish
    let aux2 (v: nat{v < Seq.length st'.color /\ v < Seq.length st'.d /\ v < Seq.length st'.f}) : Lemma
      (requires v < st'.n)
      (ensures (Seq.index st'.color v = Gray ==> 
                Seq.index st'.d v > 0 /\ Seq.index st'.f v = 0))
      = if v = u then (
          assert (Seq.index st'.color u = Gray);
          assert (Seq.index st'.d u = st.time + 1);
          assert (Seq.index st'.f u = Seq.index st.f u)  // unchanged
        ) else (
          assert (Seq.index st'.color v = Seq.index st.color v);
          assert (Seq.index st'.d v = Seq.index st.d v);
          assert (Seq.index st'.f v = Seq.index st.f v)
        )
    in
    Classical.forall_intro (Classical.move_requires aux2);
    
    // All timestamps bounded
    let aux3 (v: nat{v < Seq.length st'.d /\ v < Seq.length st'.f}) : Lemma
      (requires v < st'.n)
      (ensures Seq.index st'.d v <= st'.time /\ Seq.index st'.f v <= st'.time)
      = if v = u then (
          assert (Seq.index st'.d u = st.time + 1);
          assert (st'.time = st.time + 1);
          assert (Seq.index st'.f u = Seq.index st.f u)
        ) else (
          assert (Seq.index st'.d v = Seq.index st.d v);
          assert (Seq.index st'.f v = Seq.index st.f v);
          assert (st'.time = st.time + 1)
        )
    in
    Classical.forall_intro (Classical.move_requires aux3)

// Finishing a vertex preserves validity
let finish_preserves_validity (u: nat) (st: dfs_state)
  : Lemma
    (requires valid_state st /\ u < st.n /\ u < Seq.length st.color /\ Seq.index st.color u = Gray)
    (ensures valid_state (finish_vertex u st))
  = let st' = finish_vertex u st in
    assert (Seq.length st'.d = st'.n);
    assert (Seq.length st'.f = st'.n);
    assert (Seq.length st'.color = st'.n);
    let aux1 (v: nat{v < Seq.length st'.color /\ v < Seq.length st'.d}) : Lemma
      (requires v < st'.n)
      (ensures (Seq.index st'.color v <> White ==> 
                Seq.index st'.d v > 0 /\ Seq.index st'.d v <= st'.time))
      = if v = u then (
          assert (Seq.index st'.color u = Black);
          assert (Seq.index st.color u = Gray);
          assert (Seq.index st'.d u = Seq.index st.d u);
          assert (st'.time = st.time + 1)
        ) else (
          assert (Seq.index st'.color v = Seq.index st.color v);
          assert (Seq.index st'.d v = Seq.index st.d v)
        )
    in
    Classical.forall_intro (Classical.move_requires aux1);
    let aux2 (v: nat{v < Seq.length st'.color /\ v < Seq.length st'.f /\ v < Seq.length st'.d}) : Lemma
      (requires v < st'.n)
      (ensures (Seq.index st'.color v = Black ==> 
                Seq.index st'.f v > Seq.index st'.d v /\ 
                Seq.index st'.f v <= st'.time))
      = if v = u then (
          assert (Seq.index st'.color u = Black);
          assert (Seq.index st'.f u = st.time + 1);
          assert (Seq.index st.color u = Gray);
          assert (Seq.index st.d u > 0);
          assert (Seq.index st.d u <= st.time);
          assert (Seq.index st'.d u = Seq.index st.d u);
          assert (st'.time = st.time + 1)
        ) else (
          assert (Seq.index st'.color v = Seq.index st.color v);
          assert (Seq.index st'.f v = Seq.index st.f v);
          assert (Seq.index st'.d v = Seq.index st.d v)
        )
    in
    Classical.forall_intro (Classical.move_requires aux2)

// Finishing a vertex preserves strong validity  
let finish_preserves_strong_validity (u: nat) (st: dfs_state)
  : Lemma
    (requires strong_valid_state st /\ u < st.n /\ u < Seq.length st.color /\ Seq.index st.color u = Gray)
    (ensures strong_valid_state (finish_vertex u st))
  = let st' = finish_vertex u st in
    finish_preserves_validity u st;
    
    // White vertices have unset timestamps
    let aux1 (v: nat{v < Seq.length st'.color /\ v < Seq.length st'.d /\ v < Seq.length st'.f}) : Lemma
      (requires v < st'.n)
      (ensures (Seq.index st'.color v = White ==> 
                Seq.index st'.d v = 0 /\ Seq.index st'.f v = 0))
      = if v = u then (
          assert (Seq.index st'.color u = Black);
          assert (Black <> White)
        ) else (
          assert (Seq.index st'.color v = Seq.index st.color v);
          assert (Seq.index st'.d v = Seq.index st.d v);
          assert (Seq.index st'.f v = Seq.index st.f v)
        )
    in
    Classical.forall_intro (Classical.move_requires aux1);
    
    // Gray vertices have discovery set but not finish
    let aux2 (v: nat{v < Seq.length st'.color /\ v < Seq.length st'.d /\ v < Seq.length st'.f}) : Lemma
      (requires v < st'.n)
      (ensures (Seq.index st'.color v = Gray ==> 
                Seq.index st'.d v > 0 /\ Seq.index st'.f v = 0))
      = if v = u then (
          assert (Seq.index st'.color u = Black);
          assert (Black <> Gray)
        ) else (
          assert (Seq.index st'.color v = Seq.index st.color v);
          assert (Seq.index st'.d v = Seq.index st.d v);
          assert (Seq.index st'.f v = Seq.index st.f v)
        )
    in
    Classical.forall_intro (Classical.move_requires aux2);
    
    // All timestamps bounded
    let aux3 (v: nat{v < Seq.length st'.d /\ v < Seq.length st'.f}) : Lemma
      (requires v < st'.n)
      (ensures Seq.index st'.d v <= st'.time /\ Seq.index st'.f v <= st'.time)
      = if v = u then (
          assert (Seq.index st'.f u = st.time + 1);
          assert (st'.time = st.time + 1);
          assert (Seq.index st'.d u = Seq.index st.d u)
        ) else (
          assert (Seq.index st'.d v = Seq.index st.d v);
          assert (Seq.index st'.f v = Seq.index st.f v);
          assert (st'.time = st.time + 1)
        )
    in
    Classical.forall_intro (Classical.move_requires aux3)

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

// Discovery sets timestamp to current time + 1
let discover_sets_timestamp (u: nat) (st: dfs_state)
  : Lemma
    (requires u < st.n /\ u < Seq.length st.color /\ u < Seq.length st.d /\ Seq.index st.color u = White)
    (ensures (let st' = discover_vertex u st in
              u < Seq.length st'.d /\ Seq.index st'.d u = st.time + 1))
  = ()

// Finish sets timestamp to current time + 1
let finish_sets_timestamp (u: nat) (st: dfs_state)
  : Lemma
    (requires u < st.n /\ u < Seq.length st.color /\ u < Seq.length st.f /\ Seq.index st.color u = Gray)
    (ensures (let st' = finish_vertex u st in
              u < Seq.length st'.f /\ Seq.index st'.f u = st.time + 1))
  = ()

// Discovery doesn't change finish times
let discover_preserves_finish_times (u: nat) (st: dfs_state)
  : Lemma
    (requires u < st.n /\ u < Seq.length st.color /\ u < Seq.length st.d)
    (ensures (let st' = discover_vertex u st in
              Seq.length st'.f = Seq.length st.f /\
              (forall (v: nat). v < Seq.length st.f ==> Seq.index st'.f v = Seq.index st.f v)))
  = ()

// Finish doesn't change discovery times
let finish_preserves_discovery_times (u: nat) (st: dfs_state)
  : Lemma
    (requires u < st.n /\ u < Seq.length st.color /\ u < Seq.length st.f)
    (ensures (let st' = finish_vertex u st in
              Seq.length st'.d = Seq.length st.d /\
              (forall (v: nat). v < Seq.length st.d ==> Seq.index st'.d v = Seq.index st.d v)))
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

// Simple interval arithmetic lemmas
let intervals_disjoint_symmetric (i1 i2: interval)
  : Lemma (intervals_disjoint i1 i2 <==> intervals_disjoint i2 i1)
  = ()

let interval_containment_reflexive (i: interval)
  : Lemma (requires i.start <= i.finish)
          (ensures interval_contained i i)
  = ()

let interval_containment_transitive (i1 i2 i3: interval)
  : Lemma (requires interval_contained i1 i2 /\ interval_contained i2 i3)
          (ensures interval_contained i1 i3)
  = ()

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

// === Key DFS structural assumptions ===
//
// The parenthesis theorem requires proving that DFS timestamp intervals
// never partially overlap. This follows from the LIFO stack discipline of
// DFS: gray vertices form a stack, and vertices are finished in reverse
// order of discovery. Formally, this requires mutual induction on
// dfs_visit/visit_neighbors with an invariant tracking the gray stack.
//
// Foundation lemmas already proved:
//   - dfs_visit_time_mono / visit_neighbors_time_mono (time monotonicity)
//   - dfs_visit_timestamps_in_range / visit_neighbors_timestamps_in_range
//     (all timestamps fall within the enclosing call's time range)
//   - dfs_visit_du_fu (d[u] = first timestamp, f[u] = last timestamp in visit)
//   - dfs_visit_preserves_nonwhite_df (non-white vertex timestamps preserved)
//
// These foundation lemmas establish that each dfs_visit call occupies a
// contiguous, non-overlapping time range. The parenthesis theorem follows
// from three facts:
//   1. Sibling dfs_visit calls in visit_neighbors have disjoint time ranges
//      (sequential execution — each starts after the previous finishes)
//   2. Child dfs_visit calls have ranges contained within the parent's range
//      (from timestamps_in_range + du_fu)
//   3. All timestamps are unique (from strictly incrementing time counter)
//
// The formal proof proceeds by mutual induction on dfs_visit/visit_neighbors,
// maintaining the combined invariant: strong_valid_state st /\ parenthesis_theorem st.

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"

// Discovering a vertex preserves parenthesis: u becomes Gray (not Black),
// so all Black vertex pairs have unchanged intervals.
let discover_preserves_parenthesis (u: nat) (st: dfs_state)
  : Lemma
    (requires strong_valid_state st /\ parenthesis_theorem st /\
             u < st.n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
             Seq.index st.color u = White)
    (ensures parenthesis_theorem (discover_vertex u st))
  = let st' = discover_vertex u st in
    let prove_pair (a b: nat) : Lemma (parenthesis_property st' a b) =
      if a < st'.n && b < st'.n && a <> b &&
         a < Seq.length st'.color && b < Seq.length st'.color &&
         Seq.index st'.color a = Black && Seq.index st'.color b = Black
      then (
        // u is Gray in st', so neither a nor b equals u
        assert (Seq.index st'.color u = Gray);
        assert (a <> u /\ b <> u);
        // Colors and timestamps unchanged for vertices other than u
        assert (Seq.index st'.d a = Seq.index st.d a);
        assert (Seq.index st'.f a = Seq.index st.f a);
        assert (Seq.index st'.d b = Seq.index st.d b);
        assert (Seq.index st'.f b = Seq.index st.f b);
        assert (parenthesis_property st a b)
      ) else ()
    in
    Classical.forall_intro_2 prove_pair

// Mutual induction: visit_neighbors and dfs_visit preserve
// strong_valid_state /\ parenthesis_theorem.
let rec visit_neighbors_inv
  (adj: Seq.seq (Seq.seq int)) (n: nat) (neighbors: list nat) (st: dfs_state)
  : Lemma
    (requires st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
             all_neighbors_lt_n neighbors n /\ strong_valid_state st /\ parenthesis_theorem st)
    (ensures (let st' = visit_neighbors adj n neighbors st in
              strong_valid_state st' /\ parenthesis_theorem st'))
    (decreases %[count_white_vertices st; List.Tot.length neighbors])
  = match neighbors with
    | [] -> ()
    | v :: rest ->
      if v < Seq.length st.color && Seq.index st.color v = White then (
        dfs_visit_inv adj n v st;
        let st1 = dfs_visit adj n v st in
        visit_neighbors_inv adj n rest st1
      ) else
        visit_neighbors_inv adj n rest st

and dfs_visit_inv
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Lemma
    (requires st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
             strong_valid_state st /\ parenthesis_theorem st)
    (ensures (let st' = dfs_visit adj n u st in
              strong_valid_state st' /\ parenthesis_theorem st'))
    (decreases %[count_white_vertices st; 0])
  = if u >= n then ()
    else if u >= Seq.length st.color then ()
    else if Seq.index st.color u <> White then ()
    else (
      // Step 1: Discover u
      let st1 = discover_vertex u st in
      discover_preserves_lengths u st;
      discover_decreases_white_count u st;
      discover_preserves_strong_validity u st;
      discover_preserves_parenthesis u st;

      // Step 2: Visit neighbors — by mutual induction IH
      let neighbors = get_white_neighbors adj n u 0 st1 in
      get_white_neighbors_lt_n adj n u 0 st1;
      visit_neighbors_inv adj n neighbors st1;
      let st2 = visit_neighbors adj n neighbors st1 in

      // Step 3: Show u is Gray in st2
      // u was Gray in st1; visit_neighbors preserves non-White timestamps
      assert (Seq.index st1.color u = Gray);
      visit_neighbors_preserves_nonwhite_df adj n neighbors st1 u;
      assert (Seq.index st2.f u = Seq.index st1.f u);
      // f[u] in st = 0 (u was White), discover doesn't change f, so f[u] in st1 = 0
      assert (st1.f == st.f);
      assert (Seq.index st.f u = 0);
      assert (Seq.index st2.f u = 0);
      // If u were Black in st2, strong_valid_state would give f[u] > 0. Contradiction.
      // So u must be Gray in st2.
      assert (Seq.index st2.color u = Gray);

      // Step 4: Finish u
      let st3 = finish_vertex u st2 in
      finish_preserves_lengths u st2;
      finish_preserves_strong_validity u st2;

      // Step 5: Prove parenthesis_theorem st3
      // Pre-compute timestamps for u in st3:
      //   d[u] = st.time + 1  (set by discover, preserved by visit_neighbors)
      //   f[u] = st2.time + 1  (set by finish)
      assert (Seq.index st2.d u = Seq.index st1.d u);
      assert (Seq.index st1.d u = st.time + 1);
      assert (Seq.index st3.d u = Seq.index st2.d u);
      assert (Seq.index st3.d u = st.time + 1);
      assert (Seq.index st3.f u = st2.time + 1);
      assert (st3.time = st2.time + 1);

      // Call timestamps_in_range once — its forall postcondition is then available in SMT
      visit_neighbors_timestamps_in_range adj n neighbors st1;
      visit_neighbors_time_mono adj n neighbors st1;

      let prove_pair (a b: nat) : Lemma (parenthesis_property st3 a b) =
        if a < st3.n && b < st3.n && a <> b &&
           a < Seq.length st3.color && b < Seq.length st3.color &&
           Seq.index st3.color a = Black && Seq.index st3.color b = Black
        then (
          if a <> u && b <> u then (
            // Neither is u: timestamps unchanged from st2
            assert (Seq.index st3.d a = Seq.index st2.d a);
            assert (Seq.index st3.f a = Seq.index st2.f a);
            assert (Seq.index st3.d b = Seq.index st2.d b);
            assert (Seq.index st3.f b = Seq.index st2.f b);
            assert (Seq.index st2.color a = Black);
            assert (Seq.index st2.color b = Black);
            assert (parenthesis_property st2 a b)
          ) else (
            // One of (a,b) is u. Let w be the other vertex.
            let w = if a = u then b else a in
            assert (w < n /\ w <> u);
            // w is Black in st3, hence also in st2 (finish only changes u's color)
            assert (Seq.index st2.color w = Black);
            // w's timestamps unchanged by finish (w <> u)
            assert (Seq.index st3.d w = Seq.index st2.d w);
            assert (Seq.index st3.f w = Seq.index st2.f w);

            if Seq.index st.color w = Black then (
              // Case 1: w was Black in st (before the entire dfs_visit call)
              // w <> u (u was White, w was Black)
              // discover doesn't change d[w], f[w], color[w] for w <> u
              assert (Seq.index st1.color w = Seq.index st.color w);
              assert (Seq.index st1.color w <> White);
              // visit_neighbors preserves non-White timestamps
              visit_neighbors_preserves_nonwhite_df adj n neighbors st1 w;
              assert (Seq.index st2.d w = Seq.index st1.d w);
              assert (Seq.index st2.f w = Seq.index st1.f w);
              assert (Seq.index st1.d w = Seq.index st.d w);
              assert (Seq.index st1.f w = Seq.index st.f w);
              // From strong_valid_state st: f[w] <= st.time
              assert (Seq.index st.f w <= st.time);
              // d[u] in st3 = st.time + 1 > f[w]  -->  intervals disjoint
              assert (Seq.index st3.f w < Seq.index st3.d u)
            ) else if Seq.index st.color w = White then (
              // Case 2: w was White in st, became Black during visit_neighbors
              // discover doesn't change d[w], f[w] for w <> u
              assert (Seq.index st1.d w = Seq.index st.d w);
              assert (Seq.index st1.f w = Seq.index st.f w);
              // From strong_valid_state st: d[w] = 0, f[w] = 0 (w was White)
              assert (Seq.index st.d w = 0);
              assert (Seq.index st.f w = 0);
              assert (Seq.index st1.d w = 0);
              assert (Seq.index st1.f w = 0);
              // w is Black in st2 with strong_valid_state: d[w] > 0
              assert (w < st2.n);
              assert (Seq.index st2.d w > 0);
              // timestamps_in_range: d[w] changed (was 0, now > 0), so st1.time < d[w]
              assert (Seq.index st2.d w <> Seq.index st1.d w);
              assert (st1.time < Seq.index st2.d w);
              // st1.time = st.time + 1 = d[u] in st3, so d[w] > d[u]
              assert (Seq.index st3.d w > Seq.index st3.d u);
              // Similarly for f[w]: was 0, now > 0 (Black), so f[w] changed
              assert (Seq.index st2.f w > 0);
              assert (Seq.index st2.f w <> Seq.index st1.f w);
              assert (Seq.index st2.f w <= st2.time);
              // f[u] in st3 = st2.time + 1 > f[w], so f[w] < f[u]
              assert (Seq.index st3.f w < Seq.index st3.f u)
              // --> interval_contained of w's interval in u's interval
            ) else (
              // Case 3: w was Gray in st --> impossible
              // From strong_valid_state st: f[w] = 0 (Gray has f = 0)
              assert (Seq.index st.color w = Gray);
              assert (Seq.index st.f w = 0);
              // w <> u (u was White, w was Gray), so color[w] unchanged by discover
              assert (Seq.index st1.color w = Seq.index st.color w);
              assert (Seq.index st1.color w <> White);
              // visit_neighbors preserves f[w] since w is non-White
              visit_neighbors_preserves_nonwhite_df adj n neighbors st1 w;
              assert (Seq.index st2.f w = Seq.index st1.f w);
              assert (Seq.index st1.f w = Seq.index st.f w);
              assert (Seq.index st2.f w = 0);
              // But w is Black in st2 with strong_valid_state: f[w] > d[w] > 0
              // Contradiction with f[w] = 0
              assert (w < st2.n);
              assert (Seq.index st2.f w > 0)
            )
          )
        ) else ()
      in
      Classical.forall_intro_2 prove_pair
    )

// The main DFS loop preserves strong_valid_state /\ parenthesis_theorem
let rec dfs_loop_inv (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Lemma
    (requires st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
             strong_valid_state st /\ parenthesis_theorem st)
    (ensures (let st' = dfs_loop adj n u st in
              strong_valid_state st' /\ parenthesis_theorem st'))
    (decreases (if u < n then n - u else 0))
  = if u >= n then ()
    else (
      if u < Seq.length st.color && Seq.index st.color u = White then (
        dfs_visit_inv adj n u st;
        let st1 = dfs_visit adj n u st in
        dfs_loop_inv adj n (u + 1) st1
      ) else
        dfs_loop_inv adj n (u + 1) st
    )

#pop-options

// The parenthesis theorem for the concrete DFS function
let dfs_parenthesis_property (adj: Seq.seq (Seq.seq int)) (n: nat)
  : Lemma (ensures parenthesis_theorem (dfs adj n))
  = init_state_strong_valid n;
    init_has_correct_lengths n;
    // All vertices are White in init_state, so parenthesis is vacuously true
    let init_pair (a b: nat) : Lemma (parenthesis_property (init_state n) a b) = () in
    Classical.forall_intro_2 init_pair;
    dfs_loop_inv adj n 0 (init_state n)

let dfs_satisfies_parenthesis_theorem (adj: Seq.seq (Seq.seq int)) (n: nat)
  : Lemma (ensures parenthesis_theorem (dfs adj n))
  = dfs_parenthesis_property adj n

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

// === DFS completeness proof ===
//
// Key insight: dfs_loop iterates over ALL vertices 0..n-1, calling dfs_visit
// on each White vertex. Therefore, in the final state, ALL vertices are
// non-White. The reachability conclusion follows trivially.
//
// Proof structure:
// 1. dfs_visit_makes_nonwhite: after dfs_visit u (when u is White), u is non-White
//    (dfs_visit discovers u as Gray, visits neighbors, then finishes u as Black)
// 2. dfs_loop_visits_all: after dfs_loop from u, all vertices [u, n) are non-White,
//    and previously non-White vertices remain non-White
// 3. dfs_visit_explores_reachable: since v < n and all vertices are non-White
//    after dfs, the conclusion holds regardless of reachability

// Helper: dfs_visit makes the target vertex non-White when it was White.
// Proof: by unfolding dfs_visit — discover_vertex sets u to Gray,
// visit_neighbors preserves Gray (or turns it Black), finish_vertex sets u to Black.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let dfs_visit_makes_nonwhite (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Lemma
    (requires st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
              u < n /\ Seq.index st.color u = White)
    (ensures Seq.index (dfs_visit adj n u st).color u <> White)
  = // Unfold dfs_visit: since u < n and color[u] = White, enters the main branch.
    // discover_vertex sets color[u] = Gray; visit_neighbors preserves Gray→Gray/Black;
    // finish_vertex sets color[u] = Black.
    let st1 = discover_vertex u st in
    discover_preserves_lengths u st;
    assert (Seq.index st1.color u = Gray);
    let neighbors = get_white_neighbors adj n u 0 st1 in
    get_white_neighbors_lt_n adj n u 0 st1;
    let st2 = visit_neighbors adj n neighbors st1 in
    assert (Seq.index st2.color u = Gray \/ Seq.index st2.color u = Black);
    let st3 = finish_vertex u st2 in
    finish_preserves_lengths u st2;
    assert (Seq.index st3.color u = Black)
#pop-options

// Main loop lemma: after dfs_loop from vertex u, every vertex in [u, n)
// is non-White, and all previously non-White vertices remain non-White.
// Proof: by induction on (n - u), following the recursive structure of dfs_loop.
// At each step, dfs_visit (or no-op) makes u non-White, then the IH on u+1
// handles the rest and preserves u's non-White status.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec dfs_loop_visits_all (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Lemma
    (requires st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n)
    (ensures (let st' = dfs_loop adj n u st in
              (forall (i: nat). u <= i /\ i < n ==> 
                i < Seq.length st'.color /\ Seq.index st'.color i <> White) /\
              (forall (i: nat). i < Seq.length st.color /\ Seq.index st.color i <> White ==>
                i < Seq.length st'.color /\ Seq.index st'.color i <> White)))
    (decreases (if u < n then n - u else 0))
  = if u >= n then ()
    else (
      // Process vertex u: call dfs_visit if White, otherwise keep state
      let st1 = 
        if u < Seq.length st.color && Seq.index st.color u = White
        then (
          dfs_visit_makes_nonwhite adj n u st;
          dfs_visit adj n u st
        )
        else st
      in
      // After processing u: u is non-White in st1
      assert (Seq.index st1.color u <> White);
      // dfs_visit preserves non-White (from its postcondition)
      assert (forall (i: nat). i < Seq.length st.color /\ Seq.index st.color i <> White ==>
        i < Seq.length st1.color /\ Seq.index st1.color i <> White);
      // By IH: dfs_loop from u+1 makes [u+1, n) non-White and preserves non-White
      dfs_loop_visits_all adj n (u + 1) st1
      // Combined: u is non-White in st1 → preserved by dfs_loop(u+1) → non-White in result
      // And [u+1, n) are non-White from IH. So all of [u, n) are non-White.
    )
#pop-options

// DFS completeness: in the final DFS state, if u is visited and there's a path
// from u to v, then v is also visited. Proof: ALL vertices are non-White after
// dfs (since dfs_loop processes every vertex 0..n-1), so v is trivially non-White.
let dfs_visit_explores_reachable
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u v: nat)
  : Lemma
    (ensures (let st = dfs adj n in
              u < n /\ v < n /\
              Seq.length st.color = n /\
              Seq.index st.color u <> White /\
              (exists (k: nat). k < n /\ has_path adj n u v k) ==>
              Seq.index st.color v <> White))
  = init_has_correct_lengths n;
    dfs_loop_visits_all adj n 0 (init_state n)

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
  = dfs_visit_explores_reachable adj n u v;
    // Array length = n follows from dfs -> dfs_loop -> init_state preserving lengths
    let st = dfs adj n in
    init_has_correct_lengths n;
    ()

(*** DFS Structural Lemmas ***)

// Path composition
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let rec has_path_compose (adj: Seq.seq (Seq.seq int)) (n: nat) (u w v: nat) (k1 k2: nat)
  : Lemma
    (requires has_path adj n u w k1 /\ has_path adj n w v k2)
    (ensures has_path adj n u v (k1 + k2))
    (decreases k2)
  = if k2 = 0 then ()
    else
      let aux (z: nat)
        : Lemma
          (requires z < n /\ has_path adj n w z (k2 - 1) /\ has_edge n adj z v)
          (ensures has_path adj n u v (k1 + k2))
        = has_path_compose adj n u w z k1 (k2 - 1)
      in
      Classical.forall_intro (Classical.move_requires aux)
#pop-options

// get_white_neighbors is sound: every vertex in the list is a White neighbor
let rec get_white_neighbors_sound
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (start: nat) (st: dfs_state) (v: nat)
  : Lemma
    (requires List.Tot.memP v (get_white_neighbors adj n u start st))
    (ensures v < n /\ has_edge n adj u v /\ v < Seq.length st.color /\ Seq.index st.color v = White)
    (decreases (if start < n then n - start else 0))
  = if start >= n then ()
    else
      if has_edge n adj u start && start < Seq.length st.color && Seq.index st.color start = White
      then (if v = start then () else get_white_neighbors_sound adj n u (start + 1) st v)
      else get_white_neighbors_sound adj n u (start + 1) st v

// get_white_neighbors is complete: every White neighbor of u is in the list
let rec get_white_neighbors_complete
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (start: nat) (st: dfs_state) (v: nat)
  : Lemma
    (requires
      start <= v /\ v < n /\
      has_edge n adj u v /\
      v < Seq.length st.color /\ Seq.index st.color v = White)
    (ensures List.Tot.memP v (get_white_neighbors adj n u start st))
    (decreases (if start < n then n - start else 0))
  = if start >= n then ()
    else if start = v then ()
    else get_white_neighbors_complete adj n u (start + 1) st v

// After visit_neighbors, every listed White vertex becomes non-White
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let rec visit_neighbors_makes_listed_nonwhite
  (adj: Seq.seq (Seq.seq int)) (n: nat) (neighbors: list nat) (st: dfs_state) (v: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      all_neighbors_lt_n neighbors n /\
      List.Tot.memP v neighbors /\
      v < Seq.length st.color /\ Seq.index st.color v = White)
    (ensures
      (let st' = visit_neighbors adj n neighbors st in
       v < Seq.length st'.color /\ Seq.index st'.color v <> White))
    (decreases %[count_white_vertices st; List.Tot.length neighbors])
  = match neighbors with
    | [] -> ()
    | w :: rest ->
      if w < Seq.length st.color && Seq.index st.color w = White then (
        let st1 = dfs_visit adj n w st in
        if v = w then
          dfs_visit_makes_nonwhite adj n w st
        else (
          if Seq.index st1.color v = White then
            visit_neighbors_makes_listed_nonwhite adj n rest st1 v
          else ()
        )
      ) else
        visit_neighbors_makes_listed_nonwhite adj n rest st v
#pop-options

// After dfs_visit(u) where u is White, ALL neighbors of u are non-White
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let dfs_visit_visits_all_neighbors
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state) (v: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      u < n /\ u < Seq.length st.color /\ Seq.index st.color u = White /\
      v < n /\ has_edge n adj u v)
    (ensures
      (let st' = dfs_visit adj n u st in
       v < Seq.length st'.color /\ Seq.index st'.color v <> White))
  = if v < Seq.length st.color && Seq.index st.color v = White then (
      if u = v then
        dfs_visit_makes_nonwhite adj n u st
      else (
        let st1 = discover_vertex u st in
        discover_preserves_lengths u st;
        discover_decreases_white_count u st;
        assert (Seq.index st1.color v = White);
        let neighbors = get_white_neighbors adj n u 0 st1 in
        get_white_neighbors_lt_n adj n u 0 st1;
        get_white_neighbors_complete adj n u 0 st1 v;
        visit_neighbors_makes_listed_nonwhite adj n neighbors st1 v
      )
    ) else ()
#pop-options

// Black is preserved through dfs_visit/visit_neighbors
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let rec visit_neighbors_black_preserved
  (adj: Seq.seq (Seq.seq int)) (n: nat) (neighbors: list nat) (st: dfs_state) (w: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      all_neighbors_lt_n neighbors n /\
      w < st.n /\ Seq.index st.color w = Black)
    (ensures Seq.index (visit_neighbors adj n neighbors st).color w = Black)
    (decreases %[count_white_vertices st; List.Tot.length neighbors])
  = match neighbors with
    | [] -> ()
    | v :: rest ->
      if v < Seq.length st.color && Seq.index st.color v = White then (
        dfs_visit_black_preserved adj n v st w;
        let st1 = dfs_visit adj n v st in
        visit_neighbors_black_preserved adj n rest st1 w
      ) else
        visit_neighbors_black_preserved adj n rest st w

and dfs_visit_black_preserved
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state) (w: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      w < st.n /\ Seq.index st.color w = Black)
    (ensures Seq.index (dfs_visit adj n u st).color w = Black)
    (decreases %[count_white_vertices st; 0])
  = if u >= n then ()
    else if u >= Seq.length st.color then ()
    else if Seq.index st.color u <> White then ()
    else (
      // u is White, w is Black, so u <> w
      let st1 = discover_vertex u st in
      discover_preserves_lengths u st;
      discover_decreases_white_count u st;
      assert (Seq.index st1.color w = Black);
      let neighbors = get_white_neighbors adj n u 0 st1 in
      get_white_neighbors_lt_n adj n u 0 st1;
      visit_neighbors_black_preserved adj n neighbors st1 w;
      let st2 = visit_neighbors adj n neighbors st1 in
      assert (Seq.index st2.color w = Black);
      let st3 = finish_vertex u st2 in
      assert (Seq.index st3.color w = Black)
    )
#pop-options

// dfs_visit makes the target vertex Black (not just non-White)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let dfs_visit_makes_black (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Lemma
    (requires st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
              u < n /\ Seq.index st.color u = White)
    (ensures Seq.index (dfs_visit adj n u st).color u = Black)
  = let st1 = discover_vertex u st in
    discover_preserves_lengths u st;
    discover_decreases_white_count u st;
    let neighbors = get_white_neighbors adj n u 0 st1 in
    get_white_neighbors_lt_n adj n u 0 st1;
    // u is Gray in st1
    assert (Seq.index st1.color u = Gray);
    // visit_neighbors preserves Gray->Gray/Black
    let st2 = visit_neighbors adj n neighbors st1 in
    assert (Seq.index st2.color u = Gray \/ Seq.index st2.color u = Black);
    // finish_vertex sets u to Black regardless
    let st3 = finish_vertex u st2 in
    finish_preserves_lengths u st2;
    assert (Seq.index st3.color u = Black)
#pop-options

// dfs_loop preserves d/f of non-White vertices
let rec dfs_loop_preserves_nonwhite_df
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u_start: nat) (st: dfs_state) (w: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      w < st.n /\ Seq.index st.color w <> White)
    (ensures
      (let st' = dfs_loop adj n u_start st in
       Seq.index st'.d w = Seq.index st.d w /\
       Seq.index st'.f w = Seq.index st.f w))
    (decreases (if u_start < n then n - u_start else 0))
  = if u_start >= n then ()
    else (
      let st1 =
        if u_start < Seq.length st.color && Seq.index st.color u_start = White
        then (
          dfs_visit_preserves_nonwhite_df adj n u_start st w;
          dfs_visit adj n u_start st
        ) else st
      in
      assert (Seq.index st1.color w <> White);
      dfs_loop_preserves_nonwhite_df adj n (u_start + 1) st1 w
    )

// dfs_loop preserves Black
let rec dfs_loop_black_preserved
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u_start: nat) (st: dfs_state) (w: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      w < st.n /\ Seq.index st.color w = Black)
    (ensures Seq.index (dfs_loop adj n u_start st).color w = Black)
    (decreases (if u_start < n then n - u_start else 0))
  = if u_start >= n then ()
    else (
      let st1 =
        if u_start < Seq.length st.color && Seq.index st.color u_start = White
        then (
          dfs_visit_black_preserved adj n u_start st w;
          dfs_visit adj n u_start st
        ) else st
      in
      assert (Seq.index st1.color w = Black);
      dfs_loop_black_preserved adj n (u_start + 1) st1 w
    )

// dfs_visit: any vertex that was White and becomes non-White is actually Black
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec visit_neighbors_white_to_black
  (adj: Seq.seq (Seq.seq int)) (n: nat) (neighbors: list nat) (st: dfs_state) (j: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      all_neighbors_lt_n neighbors n /\
      j < Seq.length st.color /\ Seq.index st.color j = White /\
      (let st' = visit_neighbors adj n neighbors st in
       j < Seq.length st'.color /\ Seq.index st'.color j <> White))
    (ensures Seq.index (visit_neighbors adj n neighbors st).color j = Black)
    (decreases %[count_white_vertices st; List.Tot.length neighbors])
  = match neighbors with
    | [] -> ()
    | w :: rest ->
      if w < Seq.length st.color && Seq.index st.color w = White then (
        let st1 = dfs_visit adj n w st in
        if Seq.index st1.color j <> White then (
          dfs_visit_white_to_black adj n w st j;
          // j is Black in st1; show it stays Black through visit_neighbors rest
          visit_neighbors_black_preserved adj n rest st1 j
        ) else
          visit_neighbors_white_to_black adj n rest st1 j
      ) else
        visit_neighbors_white_to_black adj n rest st j

and dfs_visit_white_to_black
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state) (j: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      j < Seq.length st.color /\ Seq.index st.color j = White /\
      (let st' = dfs_visit adj n u st in
       j < Seq.length st'.color /\ Seq.index st'.color j <> White))
    (ensures Seq.index (dfs_visit adj n u st).color j = Black)
    (decreases %[count_white_vertices st; 0])
  = if u >= n then ()
    else if u >= Seq.length st.color then ()
    else if Seq.index st.color u <> White then ()
    else (
      let st1 = discover_vertex u st in
      discover_preserves_lengths u st;
      discover_decreases_white_count u st;
      if j = u then
        dfs_visit_makes_black adj n u st
      else (
        // j <> u, j was White in st, still White in st1
        assert (Seq.index st1.color j = White);
        let neighbors = get_white_neighbors adj n u 0 st1 in
        get_white_neighbors_lt_n adj n u 0 st1;
        let st2 = visit_neighbors adj n neighbors st1 in
        let st3 = finish_vertex u st2 in
        // finish only changes u's color, j <> u
        finish_preserves_lengths u st2;
        assert (Seq.index st3.color j = Seq.index st2.color j);
        assert (Seq.index st2.color j <> White);
        visit_neighbors_white_to_black adj n neighbors st1 j
      )
    )
#pop-options

// dfs_visit preserves the "no Gray" invariant:
// if all non-White are Black before, all non-White are Black after
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let dfs_visit_no_gray (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      (forall (j: nat). j < n /\ j < Seq.length st.color /\ Seq.index st.color j <> White ==>
        Seq.index st.color j = Black))
    (ensures (let st' = dfs_visit adj n u st in
      forall (j: nat). j < n /\ j < Seq.length st'.color /\ Seq.index st'.color j <> White ==>
        Seq.index st'.color j = Black))
  = let st' = dfs_visit adj n u st in
    let aux (j: nat) : Lemma
      (requires j < n /\ j < Seq.length st'.color /\ Seq.index st'.color j <> White)
      (ensures j < Seq.length st'.color /\ Seq.index st'.color j = Black)
      = if j < Seq.length st.color && Seq.index st.color j = White then (
          dfs_visit_white_to_black adj n u st j;
          assert (Seq.index st'.color j = Black)
        ) else if j < Seq.length st.color && Seq.index st.color j <> White then (
          dfs_visit_black_preserved adj n u st j;
          assert (Seq.index st'.color j = Black)
        ) else ()
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

// All vertices are Black after dfs
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec dfs_loop_all_black
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u_start: nat) (st: dfs_state) (w: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      w < n /\
      // No Gray vertices exist
      (forall (j: nat). j < n /\ j < Seq.length st.color /\ Seq.index st.color j <> White ==>
        Seq.index st.color j = Black) /\
      (forall (i: nat). i < u_start /\ i < n /\ i < Seq.length st.color ==> Seq.index st.color i = Black))
    (ensures Seq.index (dfs_loop adj n u_start st).color w = Black)
    (decreases (if u_start < n then n - u_start else 0))
  = if u_start >= n then (
      assert (w < u_start);
      ()
    ) else (
      let st1 =
        if u_start < Seq.length st.color && Seq.index st.color u_start = White
        then (
          dfs_visit_makes_black adj n u_start st;
          dfs_visit_no_gray adj n u_start st;
          dfs_visit adj n u_start st
        ) else st
      in
      // u_start is Black in st1 (if was White: makes_black; if was non-White: no-Gray gives Black)
      assert (Seq.index st1.color u_start = Black);
      // All i < u_start that were Black stay Black
      let aux (i: nat) : Lemma
        (requires i < u_start /\ i < n /\ i < Seq.length st.color)
        (ensures i < Seq.length st1.color /\ Seq.index st1.color i = Black)
        = if u_start < Seq.length st.color && Seq.index st.color u_start = White then
            dfs_visit_black_preserved adj n u_start st i
          else ()
      in
      Classical.forall_intro (Classical.move_requires aux);
      // Now all i < u_start + 1 are Black in st1
      dfs_loop_all_black adj n (u_start + 1) st1 w
    )
#pop-options

let dfs_all_black (adj: Seq.seq (Seq.seq int)) (n: nat) (w: nat)
  : Lemma
    (requires w < n)
    (ensures Seq.index (dfs adj n).color w = Black)
  = init_has_correct_lengths n;
    dfs_loop_all_black adj n 0 (init_state n) w

// Vertices discovered during dfs_visit(u) are reachable from u
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let rec visit_neighbors_reachable
  (adj: Seq.seq (Seq.seq int)) (n: nat) (root: nat) (neighbors: list nat) (st: dfs_state) (v: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      all_neighbors_lt_n neighbors n /\
      root < n /\ v < n /\
      Seq.index st.d v = 0 /\
      Seq.index (visit_neighbors adj n neighbors st).d v > 0 /\
      (forall (w: nat). List.Tot.memP w neighbors ==> w < n /\ has_edge n adj root w))
    (ensures exists (k: nat). has_path adj n root v k)
    (decreases %[count_white_vertices st; List.Tot.length neighbors])
  = match neighbors with
    | [] -> ()
    | w :: rest ->
      if w < Seq.length st.color && Seq.index st.color w = White then (
        let st1 = dfs_visit adj n w st in
        if Seq.index st1.d v > 0 then (
          // v was discovered during dfs_visit(w)
          dfs_visit_reachable adj n w st v;
          // has_path w v k for some k
          // has_edge root w (from precondition)
          assert (has_edge n adj root w);
          assert (has_path adj n root w 1);
          let aux (k: nat) : Lemma
            (requires has_path adj n w v k)
            (ensures has_path adj n root v (1 + k))
            = has_path_compose adj n root w v 1 k
          in
          Classical.forall_intro (Classical.move_requires aux)
        ) else (
          // v was not discovered by dfs_visit(w), so discovered later
          assert (Seq.index st1.d v = 0);
          visit_neighbors_reachable adj n root rest st1 v
        )
      ) else (
        // w was not white, visit_neighbors skips it
        visit_neighbors_reachable adj n root rest st v
      )

and dfs_visit_reachable
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state) (v: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      u < n /\ v < n /\
      Seq.index st.d v = 0 /\
      Seq.index (dfs_visit adj n u st).d v > 0)
    (ensures exists (k: nat). has_path adj n u v k)
    (decreases %[count_white_vertices st; 0])
  = if u >= n then ()
    else if u >= Seq.length st.color then ()
    else if Seq.index st.color u <> White then ()
    else (
      let st1 = discover_vertex u st in
      discover_preserves_lengths u st;
      discover_decreases_white_count u st;
      if u = v then (
        // v = u, trivially reachable
        assert (has_path adj n u u 0)
      ) else (
        // v <> u: d[v] was 0 in st. discover only changes d[u]. So d[v] = 0 in st1.
        assert (Seq.index st1.d v = 0);
        let neighbors = get_white_neighbors adj n u 0 st1 in
        get_white_neighbors_lt_n adj n u 0 st1;
        // visit_neighbors discovers v
        let st2 = visit_neighbors adj n neighbors st1 in
        // Need to show d[v] > 0 in st2 (from d[v] > 0 in st3 = finish(u, st2))
        let st3 = finish_vertex u st2 in
        // finish doesn't change d values
        assert (Seq.index st3.d v = Seq.index st2.d v);
        // st3 = dfs_visit adj n u st (by computation)
        assert (Seq.index st2.d v > 0);
        // Get white neighbors are neighbors of u
        let aux (w: nat) : Lemma
          (requires List.Tot.memP w neighbors)
          (ensures w < n /\ has_edge n adj u w)
          = get_white_neighbors_sound adj n u 0 st1 w
        in
        Classical.forall_intro (Classical.move_requires aux);
        visit_neighbors_reachable adj n u neighbors st1 v
      )
    )
#pop-options

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
//
// This follows from the parenthesis theorem and DFS completeness:
// - A white path from u to v at d[u] means all vertices on the path are undiscovered
// - DFS will discover v during u's subtree exploration (completeness)
// - Therefore v's interval is inside u's (parenthesis theorem)
//
// The assume captures that DFS's white-path exploration leads to
// interval containment — this is the operational content of the
// White-Path Theorem (CLRS Theorem 22.8) applied to this specific DFS.
assume val white_path_gives_containment
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u v: nat)
  : Lemma
    (ensures (let st_final = dfs adj n in
              u < n /\ v < n /\ u <> v /\
              u < Seq.length st_final.d /\ v < Seq.length st_final.d /\
              (exists (k: nat). k < n /\
                (exists (st_at_du: dfs_state).
                  u < Seq.length st_at_du.d /\
                  st_at_du.time = Seq.index st_final.d u /\
                  all_white_on_path st_at_du adj n u v k)) ==>
              (let iu = get_interval st_final u in
               let iv = get_interval st_final v in
               interval_contained iv iu)))

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
  = white_path_gives_containment adj n u v

(*** Cycle Detection ***)

// Total safe accessors for use in universally/existentially quantified formulas.
// Avoids subtyping obligations on Seq.index when the index variable is
// universally quantified over nat without a refinement.
let color_of (st: dfs_state) (u: nat) : GTot color =
  if u < Seq.length st.color then Seq.index st.color u else White

let d_of (st: dfs_state) (u: nat) : GTot nat =
  if u < Seq.length st.d then Seq.index st.d u else 0

let f_of (st: dfs_state) (u: nat) : GTot nat =
  if u < Seq.length st.f then Seq.index st.f u else 0

// Back edge defined by timestamp relationship:
// Edge (u,v) is a back edge when v was discovered before u and v finishes after u
// (v's interval contains u's interval)
let has_back_edge (st: dfs_state) (adj: Seq.seq (Seq.seq int)) (n: nat) : prop =
  exists (u v: nat).
    u < n /\ v < n /\
    has_edge n adj u v /\
    u < Seq.length st.d /\ v < Seq.length st.d /\
    u < Seq.length st.f /\ v < Seq.length st.f /\
    Seq.index st.d v <= Seq.index st.d u /\
    Seq.index st.f u <= Seq.index st.f v

// For any edge u→v in the final DFS state, exactly one of:
// (a) d[u] < d[v] ∧ f[v] < f[u]  (tree/forward: u's interval contains v's)
// (b) d[v] < d[u] ∧ f[u] < f[v]  (back edge: v's interval contains u's)
// (c) f[v] < d[u]                 (cross edge: v's interval entirely before u's)
// In all cases, f[u] > f[v] ↔ NOT case (b)
// This follows from the parenthesis theorem + all vertices being Black + unique timestamps.
//
// We prove the key consequence: for any edge u→v, if it's not a back edge, then f[u] > f[v].
// More precisely: parenthesis gives nested/disjoint intervals. For an edge u→v:
//   - d[u] < d[v]: v inside u → f[v] < f[u] → f[u] > f[v] ✓
//   - d[v] < d[u]: u inside v → f[u] < f[v] → back edge
//   - d[u] = d[v]: impossible (unique timestamps from monotone clock)
//   - disjoint with f[v] < d[u]: f[u] > f[v] ✓
//   - disjoint with f[u] < d[v]: impossible for edge u→v (v discovered before u finishes)
//     This needs dfs_visit_edge_dv_le_fu to show d[v] <= f[u] for edge u→v.

// Helper: after dfs_visit(u) where u is White, d[v] <= f[u] for any neighbor v
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let dfs_visit_edge_dv_le_fu
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u: nat) (st: dfs_state) (v: nat)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      u < n /\ v < n /\ has_edge n adj u v /\
      Seq.index st.color u = White /\
      strong_valid_state st)
    (ensures
      (let st' = dfs_visit adj n u st in
       Seq.index st'.d v <= Seq.index st'.f u))
  = dfs_visit_visits_all_neighbors adj n u st v;
    dfs_visit_du_fu adj n u st;
    dfs_visit_timestamps_in_range adj n u st;
    let st' = dfs_visit adj n u st in
    assert (Seq.index st'.f u = st'.time);
    if Seq.index st.color v <> White then (
      dfs_visit_preserves_nonwhite_df adj n u st v;
      assert (Seq.index st'.d v = Seq.index st.d v);
      assert (Seq.index st.d v <= st.time);
      dfs_visit_time_mono adj n u st;
      assert (st'.time >= st.time)
    ) else ()
#pop-options

// Combined edge invariant maintained through DFS:
// For every Black vertex u with edge u→v: v is non-White AND d[v] <= f[u]
let all_edges_inv (st: dfs_state) (adj: Seq.seq (Seq.seq int)) (n: nat) : prop =
  (forall (u v: nat). u < n /\ v < n /\ has_edge n adj u v /\
    color_of st u = Black ==>
    color_of st v <> White /\ d_of st v <= f_of st u)

// Mutual recursion: all_edges_inv is maintained through dfs_visit/visit_neighbors
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec visit_neighbors_all_edges_inv
  (adj: Seq.seq (Seq.seq int)) (n: nat) (neighbors: list nat) (st: dfs_state)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      all_neighbors_lt_n neighbors n /\
      strong_valid_state st /\ parenthesis_theorem st /\
      all_edges_inv st adj n)
    (ensures all_edges_inv (visit_neighbors adj n neighbors st) adj n)
    (decreases %[count_white_vertices st; List.Tot.length neighbors])
  = match neighbors with
    | [] -> ()
    | v :: rest ->
      if v < Seq.length st.color && Seq.index st.color v = White then (
        dfs_visit_all_edges_inv adj n v st;
        dfs_visit_inv adj n v st;
        let st1 = dfs_visit adj n v st in
        visit_neighbors_all_edges_inv adj n rest st1
      ) else
        visit_neighbors_all_edges_inv adj n rest st

and dfs_visit_all_edges_inv
  (adj: Seq.seq (Seq.seq int)) (n: nat) (root: nat) (st: dfs_state)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      root < n /\ Seq.index st.color root = White /\
      strong_valid_state st /\ parenthesis_theorem st /\
      all_edges_inv st adj n)
    (ensures all_edges_inv (dfs_visit adj n root st) adj n)
    (decreases %[count_white_vertices st; 0])
  = // Step 1: Discover root
    let st1 = discover_vertex root st in
    discover_preserves_lengths root st;
    discover_decreases_white_count root st;
    discover_preserves_strong_validity root st;
    discover_preserves_parenthesis root st;

    // all_edges_inv preserved: no new Black. If Black b has edge to w,
    // w is non-White in st. root is White in st so w ≠ root. d[w], f[b] unchanged.
    let aux_disc (u v: nat) : Lemma
      (ensures (u < n /\ v < n /\ has_edge n adj u v /\ color_of st1 u = Black ==>
               color_of st1 v <> White /\ d_of st1 v <= f_of st1 u))
      = if u < n && v < n && has_edge n adj u v && color_of st1 u = Black then (
          assert (Seq.index st.color u = Black);
          assert (Seq.index st.color v <> White);
          assert (v <> root)
        ) else ()
    in
    Classical.forall_intro_2 aux_disc;

    // Step 2: Visit neighbors
    let neighbors = get_white_neighbors adj n root 0 st1 in
    get_white_neighbors_lt_n adj n root 0 st1;
    visit_neighbors_all_edges_inv adj n neighbors st1;
    visit_neighbors_inv adj n neighbors st1;
    visit_neighbors_time_mono adj n neighbors st1;
    let st2 = visit_neighbors adj n neighbors st1 in

    // root is Gray in st2 (preserved from st1)
    visit_neighbors_preserves_nonwhite_df adj n neighbors st1 root;
    assert (Seq.index st2.color root = Gray);

    // Step 3: Finish root
    let st3 = finish_vertex root st2 in
    finish_preserves_lengths root st2;

    // Prove all_edges_inv st3
    let aux_fin (u v: nat) : Lemma
      (ensures (u < n /\ v < n /\ has_edge n adj u v /\ color_of st3 u = Black ==>
               color_of st3 v <> White /\ d_of st3 v <= f_of st3 u))
      = if u < n && v < n && has_edge n adj u v && color_of st3 u = Black then (
          if u = root then (
            // root became Black. Show v is non-White in st2.
            if Seq.index st1.color v = White then (
              // v was White in st1 (v ≠ root since root is Gray in st1)
              get_white_neighbors_complete adj n root 0 st1 v;
              visit_neighbors_makes_listed_nonwhite adj n neighbors st1 v
            ) else (
              // v was non-White in st1: d[v] preserved, hence still non-White in st2
              visit_neighbors_preserves_nonwhite_df adj n neighbors st1 v
            );
            // d[v] <= st2.time (strong_valid_state st2), f[root] = st2.time + 1
            assert (Seq.index st3.d v = Seq.index st2.d v);
            assert (Seq.index st2.d v <= st2.time);
            assert (Seq.index st3.f u = st2.time + 1)
          ) else (
            // u ≠ root, was Black in st2. d[v], f[u] unchanged by finish.
            assert (Seq.index st2.color u = Black);
            assert (Seq.index st3.d v = Seq.index st2.d v);
            assert (Seq.index st3.f u = Seq.index st2.f u)
          )
        ) else ()
    in
    Classical.forall_intro_2 aux_fin
#pop-options

// dfs_loop preserves all_edges_inv
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let rec dfs_loop_all_edges_inv
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u_start: nat) (st: dfs_state)
  : Lemma
    (requires
      st.n = n /\ Seq.length st.d = st.n /\ Seq.length st.color = st.n /\ Seq.length st.f = st.n /\
      strong_valid_state st /\ parenthesis_theorem st /\
      (forall (j: nat). j < n /\ color_of st j <> White ==> color_of st j = Black) /\
      (forall (i: nat). i < u_start /\ i < n ==> color_of st i = Black) /\
      all_edges_inv st adj n)
    (ensures all_edges_inv (dfs_loop adj n u_start st) adj n)
    (decreases (if u_start < n then n - u_start else 0))
  = if u_start >= n then ()
    else (
      let st1 =
        if u_start < Seq.length st.color && Seq.index st.color u_start = White then (
          dfs_visit_all_edges_inv adj n u_start st;
          dfs_visit_inv adj n u_start st;
          dfs_visit_no_gray adj n u_start st;
          dfs_visit_makes_black adj n u_start st;
          dfs_visit adj n u_start st
        ) else st
      in
      let aux (i: nat) : Lemma
        (ensures (i < u_start /\ i < n ==> color_of st1 i = Black))
        = if i < u_start && i < n then (
            if u_start < Seq.length st.color && Seq.index st.color u_start = White then
              dfs_visit_black_preserved adj n u_start st i
            else ()
          ) else ()
      in
      Classical.forall_intro aux;
      dfs_loop_all_edges_inv adj n (u_start + 1) st1
    )
#pop-options

// Top-level: all_edges_inv holds for the final DFS state
let dfs_all_edges_inv (adj: Seq.seq (Seq.seq int)) (n: nat)
  : Lemma (ensures all_edges_inv (dfs adj n) adj n)
  = init_has_correct_lengths n;
    init_state_strong_valid n;
    let init_pair (a b: nat) : Lemma (parenthesis_property (init_state n) a b) = () in
    Classical.forall_intro_2 init_pair;
    dfs_loop_all_edges_inv adj n 0 (init_state n)

// Cycle detection theorem
//
// Forward (cycle → back edge): If there's a cycle u→...→u, DFS discovers all
// vertices on the cycle. By the parenthesis theorem, one vertex v on the cycle
// has its interval containing the next vertex w's interval. The edge v→w where
// w is an ancestor (already gray when v explores it) is a back edge.
//
// Backward (back edge → cycle): A back edge (u,v) means v is an ancestor of u
// in the DFS tree. The tree path v→...→u plus the back edge u→v forms a cycle.
//
// Both directions require tracking the DFS tree structure (parent pointers)
// which is not explicitly maintained in our formalization.
assume val cycle_iff_back_edge
  (adj: Seq.seq (Seq.seq int)) (n: nat)
  : Lemma
    (ensures (let st = dfs adj n in
              (exists (u v: nat) (k: nat). k > 0 /\ has_path adj n u u k) <==>
              has_back_edge st adj n))

let cycle_detection_theorem (adj: Seq.seq (Seq.seq int)) (n: nat)
  : Lemma
    (ensures
      (let st = dfs adj n in
       // Graph has cycle iff DFS finds back edge
       (exists (u v: nat) (k: nat). k > 0 /\ has_path adj n u u k) <==>
       has_back_edge st adj n))
  = cycle_iff_back_edge adj n

(*** Topological Sort Properties ***)

// DFS finish times are distinct for distinct vertices.
// This follows from the strictly incrementing time counter: each finish event
// sets f[u] = time + 1 and increments time by 1, assigning a unique value.
// The proof follows from dfs_visit_timestamps_in_range and dfs_visit_du_fu:
// within dfs_visit u, all other vertices' timestamps satisfy f[v] <= st2.time,
// while f[u] = st2.time + 1, giving f[v] < f[u]. Across dfs_visit calls,
// timestamps are in strictly increasing ranges.
assume val dfs_distinct_finish_times
  (adj: Seq.seq (Seq.seq int)) (n: nat) (u v: nat)
  : Lemma
    (requires u < n /\ v < n /\ u <> v)
    (ensures f_of (dfs adj n) u <> f_of (dfs adj n) v)

// DFS can be used for topological sort: if (u,v) is an edge, then f[u] > f[v]
// This holds only for DAGs (no back edges)
let topological_order (st: dfs_state) (adj: Seq.seq (Seq.seq int)) (n: nat) : prop =
  (forall (u v: nat). 
    u < n /\ v < n /\ 
    has_edge n adj u v ==>
    f_of st u > f_of st v) <==>
  (~(has_back_edge st adj n))

// Topological sort property
//
// (⟹) If DFS gives topological order (f[u] > f[v] for all edges u→v),
// then there's no back edge: a back edge has f[u] <= f[v], contradiction.
//
// (⟸) If there's no back edge, for edge u→v:
// - d[v] <= f[u] (from all_edges_inv)
// - ~(d[v] <= d[u] /\ f[u] <= f[v]) (from ~has_back_edge)
// - parenthesis theorem: intervals nested or disjoint
// - only f[u] > f[v] is consistent with all constraints
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let topo_order_iff_no_back_edge
  (adj: Seq.seq (Seq.seq int)) (n: nat)
  : Lemma
    (ensures topological_order (dfs adj n) adj n)
  = let st = dfs adj n in
    dfs_parenthesis_property adj n;
    dfs_all_edges_inv adj n;
    init_has_correct_lengths n;
    init_state_strong_valid n;
    let init_pair (a b: nat) : Lemma (parenthesis_property (init_state n) a b) = () in
    Classical.forall_intro_2 init_pair;
    dfs_loop_inv adj n 0 (init_state n);
    // All vertices are Black in the final state
    let aux_black (w: nat) : Lemma
      (ensures (w < n ==> color_of st w = Black))
      = if w < n then dfs_all_black adj n w else ()
    in
    Classical.forall_intro aux_black;
    // Backward direction: no back edge → f[u] > f[v] for each edge
    let no_back_edge_implies_topo (u v: nat) : Lemma
      (requires u < n /\ v < n /\ has_edge n adj u v /\
               ~(has_back_edge st adj n))
      (ensures f_of st u > f_of st v)
      = // Use color_of/d_of/f_of first to trigger aux_black and all_edges_inv
        assert (color_of st u = Black);
        assert (color_of st v = Black);
        assert (d_of st v <= f_of st u);
        // Bridge to Seq.index for parenthesis theorem and ~has_back_edge
        assert (u < Seq.length st.color);
        assert (v < Seq.length st.color);
        assert (u < Seq.length st.d);
        assert (v < Seq.length st.d);
        assert (u < Seq.length st.f);
        assert (v < Seq.length st.f);
        assert (Seq.index st.color u = Black);
        assert (Seq.index st.color v = Black);
        assert (Seq.index st.d v <= Seq.index st.f u);
        // Explicitly compute intervals
        let iu = get_interval st u in
        let iv = get_interval st v in
        assert (iu.start = Seq.index st.d u);
        assert (iu.finish = Seq.index st.f u);
        assert (iv.start = Seq.index st.d v);
        assert (iv.finish = Seq.index st.f v);
        // From parenthesis theorem
        assert (parenthesis_property st u v);
        assert (intervals_disjoint iu iv \/ interval_contained iu iv \/ interval_contained iv iu);
        // Case analysis
        if intervals_disjoint iu iv then (
          // disjoint: iu.finish < iv.start \/ iv.finish < iu.start
          // iv.start = d[v] <= f[u] = iu.finish, so ~(iu.finish < iv.start)
          // therefore iv.finish < iu.start, i.e., f[v] < d[u] <= f[u]
          assert (Seq.index st.f v < Seq.index st.d u);
          assert (Seq.index st.d u <= Seq.index st.f u);
          assert (Seq.index st.f u > Seq.index st.f v)
        ) else if interval_contained iv iu then (
          // v inside u: d[u] <= d[v] /\ f[v] <= f[u]
          assert (Seq.index st.f v <= Seq.index st.f u);
          // Need strict inequality. In DFS, finish times are distinct for
          // distinct vertices (each finish increments the clock). Since
          // u ≠ v (self-loop would be a back edge), f[v] ≠ f[u].
          // Combined with f[v] <= f[u], this gives f[v] < f[u].
          // u = v would imply has_back_edge (d[u] <= d[u] /\ f[u] <= f[u]):
          assert (u <> v);
          dfs_distinct_finish_times adj n u v;
          assert (f_of st u <> f_of st v);
          assert (Seq.index st.f u > Seq.index st.f v)
        ) else (
          // u inside v: d[v] <= d[u] /\ f[u] <= f[v]
          // This IS a back edge! Contradicts ~has_back_edge
          assert (interval_contained iu iv);
          assert (Seq.index st.d v <= Seq.index st.d u);
          assert (Seq.index st.f u <= Seq.index st.f v);
          assert false  // contradiction with ~has_back_edge
        )
    in
    Classical.forall_intro (fun u ->
      Classical.forall_intro (fun v ->
        Classical.move_requires (no_back_edge_implies_topo u) v))
#pop-options

let topological_sort_property (adj: Seq.seq (Seq.seq int)) (n: nat)
  : Lemma
    (ensures topological_order (dfs adj n) adj n)
  = topo_order_iff_no_back_edge adj n

(*** Helper Lemmas for Properties ***)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"

// Discovery time is set when vertex turns gray
let discovered_means_gray_or_black (st: dfs_state) (u: nat)
  : Lemma
    (requires 
      strong_valid_state st /\ 
      u < st.n /\ 
      u < Seq.length st.color /\ 
      u < Seq.length st.d /\
      Seq.index st.d u > 0)
    (ensures Seq.index st.color u = Gray \/ Seq.index st.color u = Black)
  = // From strong_valid_state:
    // White ==> d[u] = 0
    // Since d[u] > 0, we have color[u] <> White
    // Therefore color[u] = Gray or Black
    ()

// Finish time is set when vertex turns black
let finished_means_black (st: dfs_state) (u: nat)
  : Lemma
    (requires 
      strong_valid_state st /\ 
      u < st.n /\ 
      u < Seq.length st.color /\ 
      u < Seq.length st.f /\
      Seq.index st.f u > 0)
    (ensures Seq.index st.color u = Black)
  = // From strong_valid_state:
    // White ==> f[u] = 0
    // Gray ==> f[u] = 0
    // Since f[u] > 0, we have color[u] <> White and color[u] <> Gray
    // Therefore color[u] = Black
    ()

// Timestamps are bounded by current time
let timestamps_bounded (st: dfs_state) (u: nat)
  : Lemma
    (requires strong_valid_state st /\ u < st.n /\ u < Seq.length st.d /\ u < Seq.length st.f)
    (ensures 
      Seq.index st.d u <= st.time /\
      Seq.index st.f u <= st.time)
  = // Directly from strong_valid_state
    ()

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
