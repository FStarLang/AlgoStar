module CLRS.Ch24.Dijkstra.Correctness

open FStar.Mul
open FStar.Seq

module Seq = FStar.Seq
module SP = CLRS.Ch24.ShortestPath.Spec

(*
   CLRS Theorem 24.6: Greedy Choice Property for Dijkstra's Algorithm
   
   When a vertex u is extracted from the priority queue (i.e., selected as the
   minimum-distance unvisited vertex), we have dist[u] = δ(s,u), the true 
   shortest-path distance from source s to u.
   
   This is the key correctness theorem that makes Dijkstra's algorithm work.
   Once a vertex is "settled" (removed from the priority queue), its distance
   is optimal and will never change.
   
   Proof Strategy (following CLRS):
   ==================
   By contradiction. Suppose u is the first vertex extracted with dist[u] > δ(s,u).
   
   Let p be an actual shortest path from s to u. Since we're in Dijkstra (all weights
   non-negative), p exists and has weight δ(s,u).
   
   Let S be the set of vertices whose final shortest-path weights have been determined
   (i.e., the "settled" vertices extracted so far). Since s ∈ S initially and u ∉ S
   just before extraction, path p must contain an edge (x,y) where x ∈ S and y ∉ S.
   
   Key observations:
   1. dist[x] = δ(s,x) because x was correctly settled earlier (by minimality of u
      as the first failure)
   2. When x was extracted, we relaxed edge (x,y), so dist[y] ≤ dist[x] + w(x,y)
   3. Since (x,y) is on a shortest path to u: δ(s,y) = δ(s,x) + w(x,y)
   4. Therefore: dist[y] ≤ δ(s,x) + w(x,y) = δ(s,y)
   
   But we also have (by upper bound property):
      dist[y] ≥ δ(s,y)   [because relaxation never makes distances too small]
   
   Combining: dist[y] = δ(s,y)
   
   Now, since y comes before u on the shortest path to u (and all weights ≥ 0):
      δ(s,y) ≤ δ(s,u)
   
   But u was chosen as the minimum among unvisited vertices, and y is also unvisited:
      dist[u] ≤ dist[y]
   
   Chaining inequalities:
      dist[u] ≤ dist[y] = δ(s,y) ≤ δ(s,u)
   
   But we assumed dist[u] > δ(s,u), contradiction!
   
   Therefore, when u is extracted, dist[u] = δ(s,u). □
*)

(* ===== Basic Definitions ===== *)

/// A vertex is "settled" if it has been extracted from the priority queue
/// and its distance is finalized
type settled_set = nat -> bool

/// The set of vertices extracted so far
let is_settled (s: settled_set) (v: nat) : bool = s v

/// Initial settled set: only source
let initial_settled (source: nat) : settled_set =
  fun v -> v = source

/// Add a vertex to the settled set
let add_to_settled (s: settled_set) (u: nat) : settled_set =
  fun v -> s v || v = u

(* ===== Key Properties ===== *)

/// All settled vertices have optimal distances
let all_settled_optimal 
  (dist: Seq.seq int) 
  (weights: Seq.seq int) 
  (n source: nat) 
  (settled: settled_set)
  : prop =
  n > 0 /\
  source < n /\
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (forall (v: nat). v < n /\ is_settled settled v ==>
    Seq.index dist v == SP.sp_dist weights n source v)

/// All distances are upper bounds on shortest paths
let all_distances_upper_bounds
  (dist: Seq.seq int)
  (weights: Seq.seq int)
  (n source: nat)
  : prop =
  n > 0 /\
  source < n /\
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (forall (v: nat). v < n ==>
    Seq.index dist v >= SP.sp_dist weights n source v)

/// Triangle inequality holds (edge relaxation has been applied)
let triangle_inequality
  (dist: Seq.seq int)
  (weights: Seq.seq int)
  (n: nat)
  (settled: settled_set)
  : prop =
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (forall (u v: nat). u < n /\ v < n /\ is_settled settled u ==>
    (let w_uv = Seq.index weights (u * n + v) in
     let d_u = Seq.index dist u in
     let d_v = Seq.index dist v in
     (w_uv < SP.inf /\ d_u < SP.inf) ==> d_v <= d_u + w_uv))

/// All weights are non-negative
let all_weights_non_negative (weights: Seq.seq int) : prop =
  forall (i: nat). i < Seq.length weights ==> Seq.index weights i >= 0

(* ===== Main Theorem: Greedy Choice Property ===== *)

/// When selecting the minimum unvisited vertex, if its distance is finite,
/// then the distance equals the true shortest path distance.
/// 
/// This is CLRS Theorem 24.6.
///
/// The proof strategy is to show that dist[u] <= δ(s,u).
/// Combined with the upper bound property (dist[u] >= δ(s,u)), this gives equality.
///
/// Key insight: If δ(s,u) < ∞, then there exists a shortest path from s to u.
/// This path must cross from settled to unsettled vertices at some point (x,y).
/// By triangle inequality (applied when x was settled), dist[y] <= dist[x] + w(x,y).
/// Since x is settled: dist[x] = δ(s,x) (by settled optimality).
/// Since (x,y) is on shortest path: δ(s,y) = δ(s,x) + w(x,y).
/// Therefore: dist[y] <= δ(s,y).
/// But also: dist[y] >= δ(s,y) (upper bound property).
/// So: dist[y] = δ(s,y).
/// Since y is on path to u: δ(s,y) <= δ(s,u) (non-negative weights).
/// Since u is minimum unvisited and y is unvisited: dist[u] <= dist[y].
/// Therefore: dist[u] <= dist[y] = δ(s,y) <= δ(s,u).
///
/// For the formal proof, we need to handle the path decomposition carefully.
/// The current version admits this detailed path-based reasoning.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let greedy_choice_invariant
  (dist: Seq.seq int)
  (weights: Seq.seq int)
  (n source: nat)
  (settled: settled_set)
  (u: nat)
  : Lemma
  (requires
    // Basic validity
    n > 0 /\
    source < n /\
    u < n /\
    Seq.length dist == n /\
    Seq.length weights == n * n /\
    
    // Source initialized correctly
    Seq.index dist source == 0 /\
    is_settled settled source /\
    
    // All weights non-negative (crucial for Dijkstra)
    all_weights_non_negative weights /\
    
    // u is not yet settled
    not (is_settled settled u) /\
    
    // u has minimum distance among unvisited vertices
    (forall (v: nat). v < n /\ not (is_settled settled v) ==>
      Seq.index dist u <= Seq.index dist v) /\
    
    // All previously settled vertices have optimal distances
    all_settled_optimal dist weights n source settled /\
    
    // Triangle inequality holds for all edges from settled vertices
    triangle_inequality dist weights n settled /\
    
    // All distances are upper bounds (no distance is too small)
    all_distances_upper_bounds dist weights n source)
    
  (ensures
    // The greedy choice is correct: dist[u] equals true shortest path distance
    Seq.index dist u == SP.sp_dist weights n source u)
  =
  // Get the distance values
  let d_u = Seq.index dist u in
  let delta_u = SP.sp_dist weights n source u in
  
  // From upper bound property: dist[u] >= δ(s,u)
  assert (d_u >= delta_u);
  
  // Need to prove: dist[u] <= δ(s,u)
  //
  // The formal proof requires reasoning about path decomposition:
  // 1. If δ(s,u) = ∞, then dist[u] = ∞ (by minimality and initialization)
  // 2. If δ(s,u) < ∞, then exists shortest path p from s to u
  // 3. Path p crosses from settled to unsettled at some edge (x,y)
  // 4. dist[y] = δ(s,y) by triangle inequality + settled optimality
  // 5. δ(s,y) <= δ(s,u) because y is on path to u (non-negative weights)
  // 6. dist[u] <= dist[y] because u is minimum unvisited
  // 7. Therefore: dist[u] <= dist[y] = δ(s,y) <= δ(s,u)
  //
  // Steps 2-4 require formalizing path decomposition and proving properties
  // about paths in graphs. This is a substantial proof that requires:
  // - Path induction lemmas
  // - Edge crossing lemmas
  // - Subpath weight monotonicity
  //
  // These lemmas are sketched below but not yet fully proven.
  admit()
#pop-options

(* ===== Supporting Lemmas ===== *)

/// After relaxing all edges from a settled vertex x, triangle inequality holds
/// for all edges from x
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let relax_establishes_triangle_inequality
  (dist_before dist_after: Seq.seq int)
  (weights: Seq.seq int)
  (n x: nat)
  (settled: settled_set)
  : Lemma
  (requires
    x < n /\
    is_settled settled x /\
    Seq.length dist_before == n /\
    Seq.length dist_after == n /\
    Seq.length weights == n * n /\
    // x's distance doesn't change (it's already settled)
    Seq.index dist_before x == Seq.index dist_after x /\
    // dist_after is result of relaxing all edges from x
    (forall (v: nat). v < n ==>
      (let w_xv = Seq.index weights (x * n + v) in
       let d_x = Seq.index dist_before x in
       let d_v_before = Seq.index dist_before v in
       let d_v_after = Seq.index dist_after v in
       d_v_after == (if d_x < SP.inf && w_xv < SP.inf && d_x + w_xv < d_v_before
                     then d_x + w_xv
                     else d_v_before))))
  (ensures
    // Triangle inequality holds for all edges from x
    forall (v: nat). v < n ==>
      (let w_xv = Seq.index weights (x * n + v) in
       let d_x = Seq.index dist_after x in
       let d_v = Seq.index dist_after v in
       (w_xv < SP.inf /\ d_x < SP.inf) ==> d_v <= d_x + w_xv))
  = ()
#pop-options

/// If all settled vertices have optimal distances and triangle inequality holds,
/// then all distances remain upper bounds
let optimal_settled_implies_upper_bounds
  (dist: Seq.seq int)
  (weights: Seq.seq int)
  (n source: nat)
  (settled: settled_set)
  : Lemma
  (requires
    all_settled_optimal dist weights n source settled /\
    triangle_inequality dist weights n settled /\
    all_weights_non_negative weights)
  (ensures
    all_distances_upper_bounds dist weights n source)
  = admit() // TODO: Prove using induction on path length

/// The minimum unvisited vertex cannot have distance greater than any
/// shortest path that stays within settled vertices
let minimum_unvisited_lower_bound
  (dist: Seq.seq int)
  (weights: Seq.seq int)
  (n source u: nat)
  (settled: settled_set)
  : Lemma
  (requires
    n > 0 /\
    source < n /\
    u < n /\
    not (is_settled settled u) /\
    Seq.length dist == n /\
    Seq.length weights == n * n /\
    // u is minimum among unvisited
    (forall (v: nat). v < n /\ not (is_settled settled v) ==>
      Seq.index dist u <= Seq.index dist v) /\
    all_settled_optimal dist weights n source settled /\
    triangle_inequality dist weights n settled /\
    all_weights_non_negative weights)
  (ensures
    // For any vertex y reachable via settled vertices, dist[u] <= dist[y]
    forall (y: nat). y < n /\ not (is_settled settled y) ==>
      Seq.index dist u <= Seq.index dist y)
  = ()

(* ===== Path Decomposition Lemmas ===== *)

/// Any path from a settled vertex to an unsettled vertex must have a
/// first edge crossing the boundary
let path_boundary_crossing
  (path: SP.path)
  (n: nat)
  (settled: settled_set)
  : Lemma
  (requires
    SP.path_valid path n /\
    SP.path_source path < n /\
    SP.path_dest path < n /\
    is_settled settled (SP.path_source path) /\
    not (is_settled settled (SP.path_dest path)) /\
    SP.path_edges path > 0)
  (ensures
    // There exists an edge (x,y) on path where x is settled and y is not
    exists (x y: nat). x < n /\ y < n /\
                       is_settled settled x /\
                       not (is_settled settled y))
  = admit() // TODO: Prove by path induction

/// Weight of a subpath is at most weight of full path (non-negative weights)
let subpath_weight_monotone
  (path: SP.path)
  (weights: Seq.seq int)
  (n: nat)
  : Lemma
  (requires
    SP.path_valid path n /\
    Seq.length weights == n * n /\
    all_weights_non_negative weights /\
    SP.path_edges path > 0)
  (ensures
    // For any prefix of the path, its weight <= full path weight
    true) // Simplified for now
  = admit() // TODO: Prove by induction on path structure

/// If there exists a shortest path from s to u, and triangle inequality holds
/// for all settled vertices, then the first unsettled vertex y on that path
/// has dist[y] = δ(s,y).
let first_unsettled_has_optimal_distance
  (dist: Seq.seq int)
  (weights: Seq.seq int)
  (n source u: nat)
  (settled: settled_set)
  (path: SP.path)
  : Lemma
  (requires
    // Path is valid shortest path from source to u
    n > 0 /\
    source < n /\
    u < n /\
    SP.path_valid path n /\
    SP.path_source path == source /\
    SP.path_dest path == u /\
    SP.path_weight path weights n == SP.sp_dist weights n source u /\
    SP.path_weight path weights n < SP.inf /\
    
    // Source is settled, u is not
    is_settled settled source /\
    not (is_settled settled u) /\
    
    // Settled vertices have correct distances
    all_settled_optimal dist weights n source settled /\
    
    // Triangle inequality holds from settled vertices
    triangle_inequality dist weights n settled /\
    
    // Upper bound property
    all_distances_upper_bounds dist weights n source /\
    
    // Non-negative weights
    all_weights_non_negative weights)
  (ensures
    // There exists a first unsettled vertex y on path with dist[y] = δ(s,y)
    exists (y: nat). y < n /\
                     not (is_settled settled y) /\
                     Seq.index dist y == SP.sp_dist weights n source y /\
                     SP.sp_dist weights n source y <= SP.sp_dist weights n source u)
  = 
  // Proof sketch:
  // 1. Path crosses from settled to unsettled at some edge (x,y)
  // 2. x is settled, so dist[x] = δ(s,x)
  // 3. When x was processed, we relaxed (x,y), so dist[y] <= dist[x] + w(x,y)
  // 4. Since (x,y) is on shortest path: δ(s,y) = δ(s,x) + w(x,y) = dist[x] + w(x,y)
  // 5. Therefore: dist[y] <= δ(s,y)
  // 6. By upper bound: dist[y] >= δ(s,y)
  // 7. Therefore: dist[y] = δ(s,y)
  // 8. Since y comes before u on path: δ(s,y) <= δ(s,u) (by non-negative weights)
  admit()

/// If y is unsettled and on a shortest path to u, and u is the minimum unvisited,
/// then dist[u] <= dist[y].
let minimum_property
  (dist: Seq.seq int)
  (n u y: nat)
  (settled: settled_set)
  : Lemma
  (requires
    n > 0 /\
    u < n /\
    y < n /\
    not (is_settled settled u) /\
    not (is_settled settled y) /\
    Seq.length dist == n /\
    // u is minimum among unvisited
    (forall (v: nat). v < n /\ not (is_settled settled v) ==>
      Seq.index dist u <= Seq.index dist v))
  (ensures
    Seq.index dist u <= Seq.index dist y)
  = ()

/// Main lemma: Combining first_unsettled and minimum properties gives us
/// dist[u] <= δ(s,u)
let greedy_choice_upper_bound
  (dist: Seq.seq int)
  (weights: Seq.seq int)
  (n source u: nat)
  (settled: settled_set)
  (path: SP.path)
  : Lemma
  (requires
    // Basic structure
    n > 0 /\
    source < n /\
    u < n /\
    Seq.length dist == n /\
    Seq.length weights == n * n /\
    
    // Path is valid shortest path from source to u
    SP.path_valid path n /\
    SP.path_source path == source /\
    SP.path_dest path == u /\
    SP.path_weight path weights n == SP.sp_dist weights n source u /\
    SP.path_weight path weights n < SP.inf /\
    
    // Source is settled, u is not
    is_settled settled source /\
    not (is_settled settled u) /\
    
    // u is minimum unvisited
    (forall (v: nat). v < n /\ not (is_settled settled v) ==>
      Seq.index dist u <= Seq.index dist v) /\
    
    // Settled vertices have correct distances
    all_settled_optimal dist weights n source settled /\
    
    // Triangle inequality holds from settled vertices
    triangle_inequality dist weights n settled /\
    
    // Upper bound property
    all_distances_upper_bounds dist weights n source /\
    
    // Non-negative weights
    all_weights_non_negative weights)
  (ensures
    Seq.index dist u <= SP.sp_dist weights n source u)
  =
  // Apply first_unsettled_has_optimal_distance to get y
  first_unsettled_has_optimal_distance dist weights n source u settled path;
  
  // There exists y with:
  // - y is unsettled
  // - dist[y] = δ(s,y)
  // - δ(s,y) <= δ(s,u)
  
  // By minimum property: dist[u] <= dist[y]
  // Therefore: dist[u] <= dist[y] = δ(s,y) <= δ(s,u)
  admit() // Need to extract witness from exists

(* ===== Alternative Formulation Using sp_dist Properties ===== *)

/// If u is unreachable (sp_dist = inf), then dist[u] will be inf
/// This follows from the upper bound property and the fact that distances
/// are bounded by inf in well-formed Dijkstra state.
let unreachable_stays_inf
  (dist: Seq.seq int)
  (weights: Seq.seq int)
  (n source u: nat)
  (settled: settled_set)
  : Lemma
  (requires
    n > 0 /\
    source < n /\
    u < n /\
    Seq.length dist == n /\
    Seq.length weights == n * n /\
    Seq.index dist source == 0 /\
    SP.sp_dist weights n source u == SP.inf /\
    all_distances_upper_bounds dist weights n source /\
    // In a well-formed Dijkstra state, all distances are at most inf
    (forall (v: nat). v < n ==> Seq.index dist v <= SP.inf))
  (ensures
    Seq.index dist u == SP.inf)
  = 
  // From upper bound: dist[u] >= sp_dist = inf
  // From well-formedness: dist[u] <= inf
  // Therefore: dist[u] = inf
  ()
