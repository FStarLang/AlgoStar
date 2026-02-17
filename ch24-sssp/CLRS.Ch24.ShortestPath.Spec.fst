module CLRS.Ch24.ShortestPath.Spec

open FStar.Mul
open FStar.List.Tot

let inf : int = 1000000

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
