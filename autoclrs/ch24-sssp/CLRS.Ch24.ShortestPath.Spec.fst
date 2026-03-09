module CLRS.Ch24.ShortestPath.Spec

(*
   Pure Specification of Shortest-Path Distances — CLRS Chapter 24

   Defines the mathematical oracle for shortest-path distances using
   Bellman-Ford-style dynamic programming over path length:

     sp_dist_k weights n s v k  — min-weight path from s to v using ≤ k edges
     sp_dist weights n s v      — sp_dist_k with k = n−1

   Key properties proven:
   - sp_dist_k_monotone: more edges allowed ⟹ distance cannot increase
   - sp_dist_k_bounded: sp_dist_k ≤ inf
   - sp_dist_source_nonpositive: sp_dist(s, s) ≤ 0
   - sp_dist_k_triangle: sp_dist_k(v, k) ≤ sp_dist_k(u, k−1) + w(u, v)
   - has_triangle_inequality: predicate on concrete distance arrays
   - triangle_ineq_implies_upper_bound (CLRS Cor 24.3):
       if dist satisfies triangle inequality and dist[s]=0,
       then dist[v] ≤ sp_dist(s, v) for all v — proven by induction on k

   Soundness of the finite sentinel (inf):
   - weights_in_range: each finite edge weight w satisfies |w|*(n-1) < inf,
     ensuring any simple path (≤ n-1 edges) has representable weight.
   - path_weight_bounded: under weights_in_range, path_weight < inf.
   - sp_dist_faithful: under weights_in_range, reachable vertices have sp_dist < inf.

   This module provides the shared mathematical foundation used by both
   BellmanFord and Dijkstra correctness proofs.
*)

open FStar.Mul
open FStar.List.Tot

let inf : int = CLRS.Ch24.ShortestPath.Inf.inf

(* A path is a non-empty list of vertices *)
type path = l:list nat{Cons? l}

(* Source of a path *)
let path_source (p: path) : nat = hd p

(* Destination of a path *)  
let rec path_dest (p: path) : nat =
  match p with
  | [v] -> v
  | _ :: tl -> path_dest tl

(* Number of edges in a path *)
let path_edges (p: path) : nat = length p - 1

(* All vertices in path are < n *)
let rec path_valid (p: path) (n: nat) : bool =
  match p with
  | [v] -> v < n
  | v :: tl -> v < n && path_valid tl n

(* Weight of a path: sum of edge weights *)
let rec path_weight (p: path) (weights: Seq.seq int) (n: nat) : Tot int (decreases (length p)) =
  match p with
  | [_] -> 0
  | u :: tl -> 
    match tl with
    | v :: _ ->
      let w = if u < n && v < n && u * n + v < Seq.length weights 
              then Seq.index weights (u * n + v) else inf in
      w + path_weight tl weights n

(* All edges in path have finite weight *)
let rec path_all_edges_exist (p: path) (weights: Seq.seq int) (n: nat) : bool =
  match p with
  | [_] -> true
  | u :: tl -> 
    match tl with
    | v :: _ ->
      u < n && v < n && u * n + v < Seq.length weights &&
      Seq.index weights (u * n + v) < inf &&
      path_all_edges_exist tl weights n

//SNIPPET_START: weights_in_range
(* Weights-in-range: every finite edge weight w satisfies |w| * (n-1) < inf.
   This guarantees that any simple path (≤ n-1 edges) has total weight in (-inf, inf),
   so sp_dist faithfully represents shortest-path distances for all reachable vertices.
   Without this, paths whose true weight ≥ inf are silently treated as unreachable. *)
let weights_in_range (weights: Seq.seq int) (n: nat) : prop =
  Seq.length weights == n * n /\ n > 0 /\
  (forall (i: nat). i < Seq.length weights ==>
    (let w = Seq.index weights i in
     w == inf \/
     (n == 1 /\ -inf < w /\ w < inf) \/
     (n > 1 /\ w * (n - 1) < inf /\ w * (n - 1) > -inf)))
//SNIPPET_END: weights_in_range

//SNIPPET_START: all_weights_non_negative
(* All weights are non-negative: every entry is either inf (no edge) or ≥ 0. *)
let all_weights_non_negative (weights: Seq.seq int) : prop =
  forall (i: nat). i < Seq.length weights ==>
    Seq.index weights i >= 0
//SNIPPET_END: all_weights_non_negative

//SNIPPET_START: reachable
(* A vertex v is reachable from s in a graph with n vertices and given weights
   if there exists a valid simple path from s to v using only existing edges. *)
let reachable (weights: Seq.seq int) (n: nat) (s v: nat) : prop =
  n > 0 /\ s < n /\ v < n /\ Seq.length weights == n * n /\
  (exists (p: path).
    path_source p == s /\ path_dest p == v /\
    path_edges p <= n - 1 /\
    path_valid p n /\ path_all_edges_exist p weights n)
//SNIPPET_END: reachable

(* Shortest path distance: minimum weight among all paths from s to v with at most k edges.
   Returns inf if no such path exists. *)
let rec sp_dist_k (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat) 
  : Tot int (decreases %[k; 1])
  =
  if k = 0 then (if s = v then 0 else inf)
  else 
    (* Try all predecessors u: sp_dist_k(s, u, k-1) + w(u, v) *)
    let without = sp_dist_k weights n s v (k - 1) in
    min_over_predecessors weights n s v k without 0

and min_over_predecessors (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat{k > 0}) (best: int) (u: nat) 
  : Tot int (decreases %[k; 0; n - u])
  =
  if u >= n then best
  else
    let w = if u * n + v < Seq.length weights then Seq.index weights (u * n + v) else inf in
    let via_u = sp_dist_k weights n s u (k - 1) in
    let candidate = if via_u < inf && w < inf then via_u + w else inf in
    let new_best = if candidate < best then candidate else best in
    min_over_predecessors weights n s v k new_best (u + 1)

//SNIPPET_START: sp_dist
(* Shortest path distance (unbounded number of edges) *)
let sp_dist (weights: Seq.seq int) (n: nat) (s v: nat) : int =
  if n > 0 then sp_dist_k weights n s v (n - 1) else inf
//SNIPPET_END: sp_dist

(* Distance from a vertex to itself with 0 edges is 0 *)
let sp_dist_k_zero (weights: Seq.seq int) (n: nat) (s: nat) 
  : Lemma (sp_dist_k weights n s s 0 == 0)
  = ()

(* Upper bound: sp_dist_k is at most inf *)
let rec sp_dist_k_bounded (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat)
  : Lemma (ensures sp_dist_k weights n s v k <= inf)
          (decreases %[k; 1])
  =
  if k = 0 then ()
  else begin
    sp_dist_k_bounded weights n s v (k - 1);
    min_over_predecessors_bounded weights n s v k (sp_dist_k weights n s v (k - 1)) 0
  end

(* Helper: min_over_predecessors produces at most inf *)
and min_over_predecessors_bounded 
  (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat{k > 0}) (best: int) (u: nat)
  : Lemma 
    (requires best <= inf)
    (ensures min_over_predecessors weights n s v k best u <= inf)
    (decreases %[k; 0; n - u])
  =
  if u >= n then ()
  else begin
    sp_dist_k_bounded weights n s u (k - 1);
    // We know: sp_dist_k weights n s u (k - 1) <= inf
    let w = if u * n + v < Seq.length weights then Seq.index weights (u * n + v) else inf in
    let via_u = sp_dist_k weights n s u (k - 1) in
    let candidate = if via_u < inf && w < inf then via_u + w else inf in
    let new_best = if candidate < best then candidate else best in
    // candidate is inf if either via_u or w is inf, otherwise it's via_u + w
    // new_best is either candidate or best, both <= inf
    // Therefore new_best <= inf
    assert (new_best <= inf);
    min_over_predecessors_bounded weights n s v k new_best (u + 1)
  end

(* Helper: min_over_predecessors is monotone in best *)
let rec min_over_predecessors_monotone_best
  (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat{k > 0}) (best1 best2: int) (u: nat)
  : Lemma
    (requires best1 <= best2)
    (ensures min_over_predecessors weights n s v k best1 u <= min_over_predecessors weights n s v k best2 u)
    (decreases %[k; 0; n - u])
  =
  if u >= n then ()
  else begin
    let w = if u * n + v < Seq.length weights then Seq.index weights (u * n + v) else inf in
    let via_u = sp_dist_k weights n s u (k - 1) in
    let candidate = if via_u < inf && w < inf then via_u + w else inf in
    let new_best1 = if candidate < best1 then candidate else best1 in
    let new_best2 = if candidate < best2 then candidate else best2 in
    // If candidate < best1, then new_best1 = candidate
    // If candidate < best2, then new_best2 = candidate or best2
    // Otherwise new_best1 = best1 <= best2
    // In all cases: new_best1 <= new_best2
    assert (new_best1 <= new_best2);
    min_over_predecessors_monotone_best weights n s v k new_best1 new_best2 (u + 1)
  end

(* Helper: min_over_predecessors improves or stays same compared to best *)
let rec min_over_predecessors_improves
  (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat{k > 0}) (best: int) (u: nat)
  : Lemma
    (ensures min_over_predecessors weights n s v k best u <= best)
    (decreases %[k; 0; n - u])
  =
  if u >= n then ()
  else begin
    let w = if u * n + v < Seq.length weights then Seq.index weights (u * n + v) else inf in
    let via_u = sp_dist_k weights n s u (k - 1) in
    let candidate = if via_u < inf && w < inf then via_u + w else inf in
    let new_best = if candidate < best then candidate else best in
    min_over_predecessors_improves weights n s v k new_best (u + 1);
    min_over_predecessors_monotone_best weights n s v k new_best best (u + 1)
  end

(* Monotonicity: More edges can only help (or stay the same) *)
let rec sp_dist_k_monotone (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat)
  : Lemma (ensures sp_dist_k weights n s v (k + 1) <= sp_dist_k weights n s v k)
          (decreases %[k; 1])
  =
  if k = 0 then begin
    (* k = 0: sp_dist_k(k+1) = min(sp_dist_k(0), min_over_preds(...))
       We need to show this is <= sp_dist_k(0) *)
    let without = sp_dist_k weights n s v 0 in
    min_over_predecessors_improves weights n s v 1 without 0
  end else begin
    (* k > 0: Use inductive hypothesis *)
    sp_dist_k_monotone weights n s v (k - 1);
    (* sp_dist_k(s,v,k) <= sp_dist_k(s,v,k-1) by IH *)
    let without_k = sp_dist_k weights n s v (k - 1) in
    let without_k1 = sp_dist_k weights n s v k in
    (* Need: sp_dist_k(s,v,k+1) <= sp_dist_k(s,v,k) *)
    (* sp_dist_k(k+1) = min(sp_dist_k(k), min_over_preds(...,k+1)) *)
    min_over_predecessors_improves weights n s v (k + 1) without_k1 0
  end

(* ===== Edge Relaxation Specifications ===== *)

(* Relax a single edge: dist[v] = min(dist[v], dist[u] + w(u,v)) *)
let relax_edge (dist: Seq.seq int) (weights: Seq.seq int) (n u v: nat) : Seq.seq int =
  if u >= n || v >= n || Seq.length dist <> n || u * n + v >= Seq.length weights 
  then dist
  else
    let d_u = Seq.index dist u in
    let w = Seq.index weights (u * n + v) in
    let d_v = Seq.index dist v in
    if d_u < inf && w < inf && d_u + w < d_v
    then Seq.upd dist v (d_u + w)
    else dist

(* Relax all edges from vertex u to all vertices v *)
let rec relax_all_inner (dist: Seq.seq int) (weights: Seq.seq int) (n u v: nat)
  : Tot (Seq.seq int) (decreases (n - v)) =
  if v >= n then dist
  else relax_all_inner (relax_edge dist weights n u v) weights n u (v + 1)

(* Relax all edges from all vertices u *)
let rec relax_all_outer (dist: Seq.seq int) (weights: Seq.seq int) (n u: nat) 
  : Tot (Seq.seq int) (decreases (n - u)) =
  if u >= n then dist
  else relax_all_outer (relax_all_inner dist weights n u 0) weights n (u + 1)

(* One full round of edge relaxation *)
let relax_round (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : Seq.seq int =
  relax_all_outer dist weights n 0

(* ===== Properties of Edge Relaxation ===== *)

(* relax_edge preserves length *)
let relax_edge_length (dist weights: Seq.seq int) (n u v: nat)
  : Lemma (ensures Seq.length (relax_edge dist weights n u v) == Seq.length dist)
  = ()

(* relax_edge only decreases distances *)
let relax_edge_decreases (dist weights: Seq.seq int) (n u v: nat) (w: nat)
  : Lemma (requires w < Seq.length dist)
          (ensures Seq.index (relax_edge dist weights n u v) w <= Seq.index dist w)
  =
  if u >= n || v >= n || Seq.length dist <> n || u * n + v >= Seq.length weights 
  then ()
  else
    let d_u = Seq.index dist u in
    let wt = Seq.index weights (u * n + v) in
    let d_v = Seq.index dist v in
    if d_u < inf && wt < inf && d_u + wt < d_v
    then begin
      let dist' = Seq.upd dist v (d_u + wt) in
      if w = v then begin
        assert (Seq.index dist' v == d_u + wt);
        assert (d_u + wt < d_v)
      end else ()
    end else ()

(* relax_edge doesn't change dist[w] for w != v *)
let relax_edge_unchanged (dist weights: Seq.seq int) (n u v: nat) (w: nat)
  : Lemma (requires w < Seq.length dist /\ w <> v)
          (ensures Seq.index (relax_edge dist weights n u v) w == Seq.index dist w)
  =
  if u >= n || v >= n || Seq.length dist <> n || u * n + v >= Seq.length weights 
  then ()
  else
    let d_u = Seq.index dist u in
    let wt = Seq.index weights (u * n + v) in
    let d_v = Seq.index dist v in
    if d_u < inf && wt < inf && d_u + wt < d_v
    then ()
    else ()

(* ===== Triangle Inequality and Upper Bound Theorem (CLRS Corollary 24.3) ===== *)

//SNIPPET_START: has_triangle_inequality
(* Triangle inequality property: dist[v] <= dist[u] + w(u,v) for all edges *)
let has_triangle_inequality (dist weights: Seq.seq int) (n: nat) : prop =
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (forall (v: nat). v < n ==> Seq.index dist v <= inf) /\  // All distances bounded by inf
  (forall (u v: nat). u < n /\ v < n ==>
    (let d_u = Seq.index dist u in
     let d_v = Seq.index dist v in
     let w = Seq.index weights (u * n + v) in
     (d_u < inf /\ w < inf) ==> d_v <= d_u + w))
//SNIPPET_END: has_triangle_inequality

(* Main theorem: If triangle inequality holds and dist[source] = 0, 
   then dist[v] <= sp_dist_k for all v, k.
   
   This is the converse direction of the usual correctness proof:
   instead of showing that shortest paths satisfy triangle inequality,
   we show that triangle inequality implies distances are upper bounds
   on shortest path distances.
   
   Proof by induction on k:
   - Base case k=0: If v = source, sp_dist_k = 0 = dist[source].
                    If v != source, sp_dist_k = inf >= dist[v].
   - Inductive case: sp_dist_k(k+1) considers paths with at most k+1 edges.
     It takes the minimum of:
     (1) sp_dist_k(s,v,k) - by IH, dist[v] <= this
     (2) For each u: sp_dist_k(s,u,k) + w(u,v)
         By IH: dist[u] <= sp_dist_k(s,u,k)
         By triangle ineq: dist[v] <= dist[u] + w(u,v)
         So: dist[v] <= sp_dist_k(s,u,k) + w(u,v)
     Therefore dist[v] <= min of all these = sp_dist_k(s,v,k+1) *)

let rec triangle_ineq_sp_bound_helper
  (dist weights: Seq.seq int) (n source v: nat) (k: nat{k > 0}) (best: int) (u: nat)
  : Lemma
    (requires
      has_triangle_inequality dist weights n /\
      source < n /\ v < n /\
      Seq.index dist source == 0 /\
      Seq.index dist v <= best)
    (ensures Seq.index dist v <= min_over_predecessors weights n source v k best u)
    (decreases %[k; 0; n - u])
  =
  if u >= n then ()
  else begin
    let d_v = Seq.index dist v in
    let d_u = Seq.index dist u in
    let w = if u * n + v < Seq.length weights then Seq.index weights (u * n + v) else inf in
    let via_u = sp_dist_k weights n source u (k - 1) in
    
    // By induction on k-1, we have: d_u <= via_u
    triangle_ineq_sp_bound dist weights n source u (k - 1);
    assert (d_u <= via_u);
    
    let candidate = if via_u < inf && w < inf then via_u + w else inf in
    let new_best = if candidate < best then candidate else best in
    
    // Prove d_v <= new_best
    // We know: d_v <= best (from precondition) and d_v <= inf (from has_triangle_inequality)
    assert (d_v <= best);
    assert (d_v <= inf);  // from has_triangle_inequality
    
    if candidate < best then begin
      // new_best = candidate
      assert (new_best == candidate);
      // Need to show: d_v <= candidate
      if via_u < inf && w < inf then begin
        // candidate = via_u + w
        assert (candidate == via_u + w);
        // We have: d_u <= via_u and via_u < inf
        // Therefore: d_u < inf (by transitivity)
        if d_u >= inf then begin
          assert (d_u <= via_u);
          assert (via_u < inf);
          // d_u >= inf and via_u < inf implies d_u > via_u, contradiction
          assert (false)
        end;
        assert (d_u < inf);
        // Now by triangle inequality: d_v <= d_u + w (since d_u < inf and w < inf)
        assert (d_v <= d_u + w);
        // And since d_u <= via_u: d_u + w <= via_u + w
        assert (d_v <= via_u + w);
        assert (d_v <= candidate);
        assert (d_v <= new_best)
      end else begin
        // Either via_u >= inf or w >= inf, so candidate = inf
        assert (candidate == inf);
        // candidate < best means inf < best, which is possible with unbounded int
        // We need d_v <= candidate = inf, which we have from has_triangle_inequality
        assert (d_v <= inf);
        assert (d_v <= candidate);
        assert (d_v <= new_best)
      end
    end else begin
      // candidate >= best, so new_best = best
      assert (new_best == best);
      assert (d_v <= best);
      assert (d_v <= new_best)
    end;
    
    // Now we have d_v <= new_best
    assert (d_v <= new_best);
    
    // Recurse
    triangle_ineq_sp_bound_helper dist weights n source v k new_best (u + 1)
  end

and triangle_ineq_sp_bound
  (dist weights: Seq.seq int) (n source v: nat) (k: nat)
  : Lemma
    (requires
      has_triangle_inequality dist weights n /\
      source < n /\ v < n /\
      Seq.index dist source == 0)
    (ensures Seq.index dist v <= sp_dist_k weights n source v k)
    (decreases %[k; 1])
  =
  if k = 0 then begin
    // Base case: sp_dist_k(..., 0) = 0 if v = source, else inf
    if v = source then begin
      // dist[source] = 0 = sp_dist_k(..., 0)
      ()
    end else begin
      // sp_dist_k(..., 0) = inf, and all distances <= inf
      sp_dist_k_bounded weights n source v 0;
      // Any finite value <= inf, we need to show dist[v] <= inf
      // From has_triangle_inequality, dist is a proper sequence
      // We need a bound that dist values are at most inf
      // Actually, we don't have that constraint. Let's add it.
      // For now, assume distances are reasonable (< inf for reachable vertices)
      // Actually the theorem doesn't require dist[v] < inf
      // sp_dist_k returns inf for unreachable, so dist[v] <= inf is trivial if we can show it
      // But without a bound on dist[v], we can't prove this
      // Let me add a precondition that dist[v] < inf or accept that this is only interesting when dist[v] < inf
      ()
    end
  end else begin
    // Inductive case: k > 0
    let without = sp_dist_k weights n source v (k - 1) in
    
    // By IH: dist[v] <= sp_dist_k(..., k-1)
    triangle_ineq_sp_bound dist weights n source v (k - 1);
    assert (Seq.index dist v <= without);
    
    // Now apply helper to show dist[v] <= min_over_predecessors
    triangle_ineq_sp_bound_helper dist weights n source v k without 0
  end

//SNIPPET_START: triangle_ineq_upper_bound
(* Corollary: dist[v] <= sp_dist for all v *)
let triangle_ineq_implies_upper_bound
  (dist weights: Seq.seq int) (n source v: nat)
  : Lemma
    (requires
      has_triangle_inequality dist weights n /\
      n > 0 /\
      source < n /\ v < n /\
      Seq.index dist source == 0)
    (ensures Seq.index dist v <= sp_dist weights n source v)
  =
  triangle_ineq_sp_bound dist weights n source v (n - 1)
//SNIPPET_END: triangle_ineq_upper_bound

(* ===== No Negative Cycles (flat representation) ===== *)

//SNIPPET_START: no_neg_cycles_flat
(* No negative cycles reachable from source: adding an n-th edge doesn't improve sp_dist *)
let no_neg_cycles_flat (weights: Seq.seq int) (n: nat) (source: nat) : prop =
  n > 0 /\ source < n /\
  Seq.length weights == n * n /\
  (forall (v: nat). v < n ==> sp_dist_k weights n source v n == sp_dist_k weights n source v (n - 1))
//SNIPPET_END: no_neg_cycles_flat

(* Helper: min_over_predecessors achieves bound through a specific predecessor *)
let rec min_over_predecessors_achieves
  (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat{k > 0}) (best: int)
  (u_start u_target: nat)
  : Lemma
    (requires u_start <= u_target /\ u_target < n /\
              sp_dist_k weights n s u_target (k - 1) < inf /\
              u_target * n + v < Seq.length weights /\
              Seq.index weights (u_target * n + v) < inf)
    (ensures min_over_predecessors weights n s v k best u_start <=
             sp_dist_k weights n s u_target (k - 1) + Seq.index weights (u_target * n + v))
    (decreases (n - u_start))
  =
  if u_start >= n then ()
  else if u_start = u_target then begin
    let w = if u_target * n + v < Seq.length weights
            then Seq.index weights (u_target * n + v) else inf in
    let via_u = sp_dist_k weights n s u_target (k - 1) in
    let candidate = if via_u < inf && w < inf then via_u + w else inf in
    let new_best = if candidate < best then candidate else best in
    // candidate = via_u + w (since both < inf)
    // new_best <= candidate = via_u + w
    min_over_predecessors_improves weights n s v k new_best (u_start + 1)
  end else begin
    let w = if u_start * n + v < Seq.length weights
            then Seq.index weights (u_start * n + v) else inf in
    let via_u = sp_dist_k weights n s u_start (k - 1) in
    let candidate = if via_u < inf && w < inf then via_u + w else inf in
    let new_best = if candidate < best then candidate else best in
    min_over_predecessors_achieves weights n s v k new_best (u_start + 1) u_target
  end

(* sp_dist_k triangle inequality: sp_dist_k(v, k) <= sp_dist_k(u, k-1) + w(u,v) *)
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let sp_dist_k_triangle (weights: Seq.seq int) (n: nat) (s u v: nat) (k: nat)
  : Lemma
    (requires k > 0 /\ u < n /\ v < n /\ s < n /\
              Seq.length weights == n * n /\
              sp_dist_k weights n s u (k - 1) < inf /\
              Seq.index weights (u * n + v) < inf)
    (ensures sp_dist_k weights n s v k <=
             sp_dist_k weights n s u (k - 1) + Seq.index weights (u * n + v))
  =
  let without = sp_dist_k weights n s v (k - 1) in
  min_over_predecessors_achieves weights n s v k without 0 u;
  min_over_predecessors_improves weights n s v k without 0
#pop-options

//SNIPPET_START: sp_dist_triangle_flat
(* Under no negative cycles, sp_dist satisfies triangle inequality *)
let sp_dist_triangle_flat (weights: Seq.seq int) (n: nat) (source u v: nat)
  : Lemma
    (requires no_neg_cycles_flat weights n source /\
              u < n /\ v < n /\
              sp_dist weights n source u < inf /\
              Seq.index weights (u * n + v) < inf)
    (ensures sp_dist weights n source v <=
             sp_dist weights n source u + Seq.index weights (u * n + v))
  =
  // sp_dist_k(v, n) <= sp_dist_k(u, n-1) + w(u,v)  [by sp_dist_k_triangle with k=n]
  sp_dist_k_triangle weights n source u v n;
  // no_neg_cycles_flat: sp_dist_k(v, n) == sp_dist_k(v, n-1) == sp_dist(v)
  // and sp_dist_k(u, n-1) == sp_dist(u)
  ()
//SNIPPET_END: sp_dist_triangle_flat

(* sp_dist for source is non-positive (0 with 0 edges, monotone decreasing) *)
let rec sp_dist_source_nonpositive (weights: Seq.seq int) (n: nat) (s: nat) (k: nat)
  : Lemma
    (ensures sp_dist_k weights n s s k <= 0)
    (decreases k)
  =
  if k = 0 then ()
  else begin
    sp_dist_source_nonpositive weights n s (k - 1);
    sp_dist_k_monotone weights n s s (k - 1);
    min_over_predecessors_improves weights n s s k (sp_dist_k weights n s s (k - 1)) 0
  end

// ========== Declarative Characterisation of sp_dist ==========
//
// sp_dist is defined algorithmically via Bellman-Ford-style DP.
// Below we show it IS the shortest-path distance in the declarative
// sense: it equals the minimum weight of all valid paths from s to v.
//
//   Optimality:    path_weight p >= sp_dist_k(s, v, path_edges p)
//   Achievability: sp_dist_k(s, v, k) < inf ==> exists witnessing path

(* Remove the last vertex from a path with at least 2 vertices *)
let rec path_prefix (p: path)
  : Pure path
    (requires length p >= 2)
    (ensures fun r -> length r == length p - 1 /\
                      hd r == hd p)
    (decreases length p)
  = match p with
    | [a; _] -> [a]
    | a :: tl -> a :: path_prefix tl

(* Second-to-last vertex in a path with at least one edge *)
let rec path_penult (p: path)
  : Pure nat
    (requires length p >= 2)
    (ensures fun _ -> True)
    (decreases length p)
  = match p with
    | [u; _] -> u
    | _ :: tl -> path_penult tl

(* path_source of prefix is same as path_source of original *)
let path_prefix_source (p: path)
  : Lemma (requires length p >= 2)
          (ensures path_source (path_prefix p) == path_source p)
  = ()

(* path_dest of prefix is the penultimate vertex *)
let rec path_prefix_dest (p: path)
  : Lemma (requires length p >= 2)
          (ensures path_dest (path_prefix p) == path_penult p)
          (decreases length p)
  = match p with
    | [_; _] -> ()
    | _ :: tl -> path_prefix_dest tl

(* path_edges of prefix *)
let path_prefix_edges (p: path)
  : Lemma (requires length p >= 2)
          (ensures path_edges (path_prefix p) == path_edges p - 1)
  = ()

(* path_valid is preserved by prefix *)
let rec path_prefix_valid (p: path) (n: nat)
  : Lemma (requires length p >= 2 /\ path_valid p n)
          (ensures path_valid (path_prefix p) n)
          (decreases length p)
  = match p with
    | [_; _] -> ()
    | _ :: tl -> path_prefix_valid tl n

(* path_all_edges_exist is preserved by prefix *)
let rec path_prefix_edges_exist (p: path) (weights: Seq.seq int) (n: nat)
  : Lemma (requires length p >= 2 /\ path_all_edges_exist p weights n)
          (ensures path_all_edges_exist (path_prefix p) weights n)
          (decreases length p)
  = match p with
    | [_; _] -> ()
    | _ :: tl -> path_prefix_edges_exist tl weights n

(* Weight decomposition: weight(p) = weight(prefix) + w(penult, dest) *)
let rec path_weight_snoc (p: path) (weights: Seq.seq int) (n: nat)
  : Lemma
    (requires length p >= 2)
    (ensures (let u = path_penult p in
              let v = path_dest p in
              let w = if u < n && v < n && u * n + v < Seq.length weights
                      then Seq.index weights (u * n + v) else inf in
              path_weight p weights n == path_weight (path_prefix p) weights n + w))
    (decreases length p)
  = match p with
    | [_; _] -> ()
    | _ :: tl -> path_weight_snoc tl weights n

(* Penult is a valid vertex when path is valid *)
let rec path_penult_valid (p: path) (n: nat)
  : Lemma (requires length p >= 2 /\ path_valid p n)
          (ensures path_penult p < n)
          (decreases length p)
  = match p with
    | [_; _] -> ()
    | _ :: tl -> path_penult_valid tl n

(* Last edge exists when all edges exist *)
let rec path_last_edge_exists (p: path) (weights: Seq.seq int) (n: nat)
  : Lemma (requires length p >= 2 /\ path_all_edges_exist p weights n)
          (ensures (let u = path_penult p in
                    let v = path_dest p in
                    u < n /\ v < n /\ u * n + v < Seq.length weights /\
                    Seq.index weights (u * n + v) < inf))
          (decreases length p)
  = match p with
    | [_; _] -> ()
    | _ :: tl -> path_last_edge_exists tl weights n

(* Extend a path by appending a vertex *)
let path_snoc (p: path) (v: nat) : path = FStar.List.Tot.append p [v]

let rec path_snoc_dest (p: path) (v: nat)
  : Lemma (ensures path_dest (path_snoc p v) == v)
          (decreases length p)
  = match p with
    | [_] -> ()
    | _ :: tl -> path_snoc_dest tl v

let path_snoc_source (p: path) (v: nat)
  : Lemma (ensures path_source (path_snoc p v) == path_source p)
  = ()

let path_snoc_edges (p: path) (v: nat)
  : Lemma (ensures path_edges (path_snoc p v) == path_edges p + 1)
  = FStar.List.Tot.Properties.append_length p [v]

let rec path_snoc_valid (p: path) (v: nat) (n: nat)
  : Lemma (requires path_valid p n /\ v < n)
          (ensures path_valid (path_snoc p v) n)
          (decreases length p)
  = match p with
    | [_] -> ()
    | _ :: tl -> path_snoc_valid tl v n

let rec path_snoc_weight (p: path) (v: nat) (weights: Seq.seq int) (n: nat)
  : Lemma (ensures (let u = path_dest p in
                    let w = if u < n && v < n && u * n + v < Seq.length weights
                            then Seq.index weights (u * n + v) else inf in
                    path_weight (path_snoc p v) weights n ==
                    path_weight p weights n + w))
          (decreases length p)
  = match p with
    | [_] -> ()
    | _ :: tl -> path_snoc_weight tl v weights n

let rec path_snoc_edges_exist (p: path) (v: nat) (weights: Seq.seq int) (n: nat)
  : Lemma (requires path_all_edges_exist p weights n /\
                    (let u = path_dest p in
                     u < n /\ v < n /\ u * n + v < Seq.length weights /\
                     Seq.index weights (u * n + v) < inf))
          (ensures path_all_edges_exist (path_snoc p v) weights n)
          (decreases length p)
  = match p with
    | [_] -> ()
    | _ :: tl -> path_snoc_edges_exist tl v weights n

(* ---- Optimality ---- *)

(* Helper: non-negative weights make prefix weight ≤ path weight *)
let rec path_weight_nonneg (p: path) (weights: Seq.seq int) (n: nat)
  : Lemma
    (requires path_all_edges_exist p weights n /\
              all_weights_non_negative weights)
    (ensures path_weight p weights n >= 0)
    (decreases length p)
  = match p with
    | [_] -> ()
    | _ :: tl -> path_weight_nonneg tl weights n

(* Monotonicity generalized: sp_dist_k is non-increasing in k *)
let rec sp_dist_k_monotone_le (weights: Seq.seq int) (n: nat) (s v: nat) (j k: nat)
  : Lemma (requires j <= k)
          (ensures sp_dist_k weights n s v k <= sp_dist_k weights n s v j)
          (decreases k - j)
  = if j = k then ()
    else begin
      sp_dist_k_monotone weights n s v (k - 1);
      sp_dist_k_monotone_le weights n s v j (k - 1)
    end

(* Core optimality: for paths with exactly k edges *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec sp_dist_k_le_path_weight_exact
  (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat) (p: path)
  : Lemma
    (requires n > 0 /\ s < n /\ v < n /\ Seq.length weights == n * n /\
              path_source p == s /\ path_dest p == v /\
              path_edges p == k /\
              path_valid p n /\ path_all_edges_exist p weights n /\
              all_weights_non_negative weights)
    (ensures sp_dist_k weights n s v k <= path_weight p weights n)
    (decreases k)
  = if k = 0 then ()
    else begin
      let u = path_penult p in
      let p' = path_prefix p in
      path_weight_snoc p weights n;
      path_prefix_source p;
      path_prefix_valid p n;
      path_prefix_edges_exist p weights n;
      path_prefix_dest p;
      path_prefix_edges p;
      path_penult_valid p n;
      path_last_edge_exists p weights n;
      let w_uv = Seq.index weights (u * n + v) in
      sp_dist_k_le_path_weight_exact weights n s u (k - 1) p';
      let sp_u = sp_dist_k weights n s u (k - 1) in
      if sp_u < inf then
        sp_dist_k_triangle weights n s u v k
      else begin
        sp_dist_k_bounded weights n s u (k - 1);
        sp_dist_k_bounded weights n s v k
      end
    end
#pop-options

(* General optimality: for paths with at most k edges *)
let sp_dist_k_optimal
  (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat) (p: path)
  : Lemma
    (requires n > 0 /\ s < n /\ v < n /\ Seq.length weights == n * n /\
              path_source p == s /\ path_dest p == v /\
              path_edges p <= k /\
              path_valid p n /\ path_all_edges_exist p weights n /\
              all_weights_non_negative weights)
    (ensures sp_dist_k weights n s v k <= path_weight p weights n)
  = sp_dist_k_le_path_weight_exact weights n s v (path_edges p) p;
    sp_dist_k_monotone_le weights n s v (path_edges p) k

//SNIPPET_START: sp_dist_optimal
(* OPTIMALITY: sp_dist is at most the weight of any valid path (non-negative weights) *)
let sp_dist_optimal
  (weights: Seq.seq int) (n: nat) (s v: nat) (p: path)
  : Lemma
    (requires n > 0 /\ s < n /\ v < n /\ Seq.length weights == n * n /\
              path_source p == s /\ path_dest p == v /\
              path_edges p <= n - 1 /\
              path_valid p n /\ path_all_edges_exist p weights n /\
              all_weights_non_negative weights)
    (ensures sp_dist weights n s v <= path_weight p weights n)
  = sp_dist_k_optimal weights n s v (n - 1) p
//SNIPPET_END: sp_dist_optimal

(* ---- Achievability ---- *)

(* Helper: find the predecessor that achieves the min_over_predecessors result *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 0"
let rec find_achieving_predecessor
  (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat{k > 0}) (best: int) (u: nat)
  : Pure nat
    (requires s < n /\ v < n /\ Seq.length weights == n * n /\
              best <= inf /\
              min_over_predecessors weights n s v k best u < best)
    (ensures fun r -> u <= r /\ r < n /\
              sp_dist_k weights n s r (k - 1) < inf /\
              r * n + v < Seq.length weights /\
              Seq.index weights (r * n + v) < inf /\
              sp_dist_k weights n s r (k - 1) + Seq.index weights (r * n + v) ==
                min_over_predecessors weights n s v k best u)
    (decreases n - u)
  = let w = if u * n + v < Seq.length weights then Seq.index weights (u * n + v) else inf in
    let via_u = sp_dist_k weights n s u (k - 1) in
    let candidate = if via_u < inf && w < inf then via_u + w else inf in
    let new_best = if candidate < best then candidate else best in
    if u + 1 >= n then
      u
    else begin
      min_over_predecessors_improves weights n s v k new_best (u + 1);
      let inner = min_over_predecessors weights n s v k new_best (u + 1) in
      if inner < new_best then
        find_achieving_predecessor weights n s v k new_best (u + 1)
      else if candidate < best then
        u
      else begin
        (* new_best = best, inner >= new_best = best, but 
           min_over_predecessors(best, u) = inner <= new_best = best and < best: contradiction *)
        assert false;
        u
      end
    end
#pop-options

(* Achievability: construct a path witnessing sp_dist_k *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 0"
let rec sp_dist_k_achieving_path
  (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat)
  : Pure path
    (requires n > 0 /\ s < n /\ v < n /\ Seq.length weights == n * n /\
              sp_dist_k weights n s v k < inf)
    (ensures fun p ->
      path_source p == s /\ path_dest p == v /\
      path_edges p <= k /\
      path_valid p n /\ path_all_edges_exist p weights n /\
      path_weight p weights n == sp_dist_k weights n s v k)
    (decreases k)
  = if k = 0 then [s]
    else begin
      let without = sp_dist_k weights n s v (k - 1) in
      min_over_predecessors_improves weights n s v k without 0;
      if sp_dist_k weights n s v k = without then
        sp_dist_k_achieving_path weights n s v (k - 1)
      else begin
        sp_dist_k_bounded weights n s v (k - 1);
        let u = find_achieving_predecessor weights n s v k without 0 in
        let p' = sp_dist_k_achieving_path weights n s u (k - 1) in
        let result = path_snoc p' v in
        path_snoc_dest p' v;
        path_snoc_source p' v;
        path_snoc_edges p' v;
        path_snoc_valid p' v n;
        path_snoc_weight p' v weights n;
        path_snoc_edges_exist p' v weights n;
        result
      end
    end
#pop-options

//SNIPPET_START: sp_dist_achievable
(* ACHIEVABILITY: if sp_dist is finite, there exists a path achieving it *)
let sp_dist_achievable
  (weights: Seq.seq int) (n: nat) (s v: nat)
  : Pure path
    (requires n > 0 /\ s < n /\ v < n /\ Seq.length weights == n * n /\
              sp_dist weights n s v < inf)
    (ensures fun p ->
      path_source p == s /\ path_dest p == v /\
      path_edges p <= n - 1 /\
      path_valid p n /\ path_all_edges_exist p weights n /\
      path_weight p weights n == sp_dist weights n s v)
  = sp_dist_k_achieving_path weights n s v (n - 1)
//SNIPPET_END: sp_dist_achievable

(* ---- Weights-in-range soundness ---- *)

//SNIPPET_START: path_weight_bounded
(* Key soundness lemma: under weights_in_range with non-negative weights,
   any valid simple path has total weight in [0, inf). This ensures sp_dist
   faithfully represents true shortest-path distances for reachable vertices.
   Combined with sp_dist_optimal, guarantees sp_dist(s,v) < inf whenever
   v is reachable from s via existing edges. *)

(* Stronger inductive invariant: path_weight * (n-1) < path_edges * inf.
   Since path_edges ≤ n-1, this gives path_weight * (n-1) < (n-1) * inf,
   hence path_weight < inf. *)
#push-options "--fuel 2 --ifuel 0 --z3rlimit 30"
let rec path_weight_bounded_strong
  (p: path) (weights: Seq.seq int) (n: nat)
  : Lemma
    (requires
      weights_in_range weights n /\
      n > 1 /\
      path_valid p n /\
      path_all_edges_exist p weights n /\
      path_edges p <= n - 1 /\
      all_weights_non_negative weights)
    (ensures
      0 <= path_weight p weights n /\
      (path_edges p == 0 ==> path_weight p weights n == 0) /\
      (path_edges p > 0 ==> path_weight p weights n * (n - 1) < path_edges p * inf))
    (decreases (length p))
  = match p with
    | [_] -> ()
    | u :: tl ->
      match tl with
      | v :: _ ->
        path_weight_bounded_strong tl weights n;
        let w = Seq.index weights (u * n + v) in
        assert (w >= 0);
        assert (w * (n - 1) < inf);
        assert (path_weight tl weights n >= 0);
        if path_edges tl = 0
        then begin
          assert (path_weight tl weights n == 0);
          assert (path_weight p weights n == w);
          assert (path_edges p == 1);
          // w * (n-1) < inf = 1 * inf = path_edges p * inf
          ()
        end
        else begin
          assert (path_weight tl weights n * (n - 1) < path_edges tl * inf);
          // path_weight p = w + path_weight tl
          // (w + path_weight tl) * (n-1) = w*(n-1) + path_weight_tl*(n-1)
          //   < inf + path_edges_tl * inf = (1 + path_edges_tl) * inf = path_edges_p * inf
          assert (path_weight p weights n * (n - 1) ==
                  w * (n - 1) + path_weight tl weights n * (n - 1));
          assert (path_edges p == 1 + path_edges tl)
        end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let path_weight_bounded
  (p: path) (weights: Seq.seq int) (n: nat)
  : Lemma
    (requires
      weights_in_range weights n /\
      path_valid p n /\
      path_all_edges_exist p weights n /\
      path_edges p <= n - 1 /\
      all_weights_non_negative weights)
    (ensures 0 <= path_weight p weights n /\ path_weight p weights n < inf)
  = if n = 1
    then begin
      // n=1: path_edges p ≤ 0, so path_edges p = 0, path has 1 vertex, weight = 0
      // Use path_weight_nonneg to get >= 0, and sp_dist_k_bounded for < inf
      assert (path_edges p == 0);
      // With 0 edges, p must be [v] for some v, path_weight = 0
      assert (length p == 1);
      // path_weight on any list of length 1 is 0 (by definition)
      // SMT + fuel 2 handles this
      ()
    end
    else begin
      path_weight_bounded_strong p weights n;
      if path_edges p = 0
      then ()
      else begin
        // path_weight * (n-1) < path_edges * inf ≤ (n-1) * inf
        // So path_weight < inf
        assert (path_weight p weights n * (n - 1) < path_edges p * inf);
        assert (path_edges p <= n - 1)
      end
    end
#pop-options

//SNIPPET_START: sp_dist_faithful
(* Corollary: under weights_in_range and non-negative weights, if vertex v is
   reachable from s (there exists a valid simple path), then sp_dist(s,v) < inf.
   This shows sp_dist faithfully represents the shortest-path distance. *)
let sp_dist_faithful
  (weights: Seq.seq int) (n: nat) (s v: nat) (p: path)
  : Lemma
    (requires
      weights_in_range weights n /\
      s < n /\ v < n /\
      path_source p == s /\ path_dest p == v /\
      path_edges p <= n - 1 /\
      path_valid p n /\ path_all_edges_exist p weights n /\
      all_weights_non_negative weights)
    (ensures sp_dist weights n s v < inf)
  = path_weight_bounded p weights n;
    sp_dist_optimal weights n s v p
//SNIPPET_END: sp_dist_faithful

//SNIPPET_START: sp_dist_iff_reachable
(* Under weights_in_range and non-negative weights:
   sp_dist(s,v) < inf  ⟺  v is reachable from s.
   Forward: sp_dist_faithful (above).
   Backward: sp_dist_achievable gives a witnessing path. *)

(* Forward: reachable ⟹ sp_dist < inf *)
let reachable_implies_sp_dist_finite
  (weights: Seq.seq int) (n: nat) (s v: nat)
  : Lemma
    (requires
      reachable weights n s v /\
      weights_in_range weights n /\
      all_weights_non_negative weights)
    (ensures sp_dist weights n s v < inf)
  = eliminate exists (p: path).
      path_source p == s /\ path_dest p == v /\
      path_edges p <= n - 1 /\
      path_valid p n /\ path_all_edges_exist p weights n
    returns sp_dist weights n s v < inf
    with _. sp_dist_faithful weights n s v p

(* Backward: sp_dist < inf ⟹ reachable *)
let sp_dist_finite_implies_reachable
  (weights: Seq.seq int) (n: nat) (s v: nat)
  : Lemma
    (requires
      n > 0 /\ s < n /\ v < n /\ Seq.length weights == n * n /\
      sp_dist weights n s v < inf)
    (ensures reachable weights n s v)
  = let p = sp_dist_achievable weights n s v in
    assert (path_source p == s);
    assert (path_dest p == v);
    assert (path_edges p <= n - 1);
    assert (path_valid p n);
    assert (path_all_edges_exist p weights n)

(* Contrapositive: ¬reachable ⟹ sp_dist == inf *)
let not_reachable_implies_sp_dist_inf
  (weights: Seq.seq int) (n: nat) (s v: nat)
  : Lemma
    (requires
      n > 0 /\ s < n /\ v < n /\ Seq.length weights == n * n /\
      weights_in_range weights n /\
      all_weights_non_negative weights /\
      ~(reachable weights n s v))
    (ensures sp_dist weights n s v == inf)
  = if sp_dist weights n s v < inf
    then begin
      sp_dist_finite_implies_reachable weights n s v;
      assert (reachable weights n s v) // contradiction
    end
    else sp_dist_k_bounded weights n s v (n - 1)
//SNIPPET_END: sp_dist_iff_reachable
//SNIPPET_END: path_weight_bounded
