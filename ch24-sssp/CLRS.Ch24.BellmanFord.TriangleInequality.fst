module CLRS.Ch24.BellmanFord.TriangleInequality

open FStar.Mul
module Seq = FStar.Seq

(*
 * Proof that triangle inequality is a CONSEQUENCE of the relaxation-based
 * negative cycle check in Bellman-Ford.
 * 
 * Key insight from CLRS Chapter 24:
 * After |V|-1 iterations of relaxing all edges, the algorithm performs a final
 * pass checking if any edge can still be relaxed. This check serves two purposes:
 *   1. Negative cycle detection: if any edge can be relaxed, a negative cycle exists
 *   2. Triangle inequality verification: if no edge can be relaxed, triangle inequality holds
 * 
 * This file proves that (2) follows from (1), making the triangle inequality a
 * consequence rather than requiring separate verification.
 * 
 * This allows removing the explicit "triangle inequality verification" from the
 * implementation - it's automatically implied by passing the negative cycle check!
 *)

let inf : int = 1000000

(* Distance vector: current distance estimates *)
type dist_vec (n: nat) = d:Seq.seq int{Seq.length d == n}

(* Weight matrix: n×n adjacency matrix (flattened) *)
type weight_matrix (n: nat) = w:Seq.seq int{Seq.length w == n * n}

(* Triangle inequality for a single edge (u,v) *)
let edge_satisfies_triangle (dist: dist_vec 'n) (weights: weight_matrix 'n) (u v: nat{u < 'n /\ v < 'n}) : prop =
  let d_u = Seq.index dist u in
  let d_v = Seq.index dist v in
  let w = Seq.index weights (u * 'n + v) in
  (w < inf /\ d_u < inf) ==> d_v <= d_u + w

(* Triangle inequality holds for all edges *)
let triangle_inequality (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) : prop =
  forall (u v: nat). u < n /\ v < n ==> edge_satisfies_triangle dist weights u v

(* ===== Connection to Negative Cycle Check ===== *)

(* The negative cycle check verifies that no edge violates the triangle inequality.
   Specifically, it checks that for all edges (u,v):
     NOT (w < inf /\ d_u < inf /\ d_v > d_u + w)
   which is equivalent to:
     (w < inf /\ d_u < inf) ==> d_v <= d_u + w
   which is exactly the triangle inequality! *)

(* Theorem: If the negative cycle check passes (no violations), then triangle inequality holds *)
let no_violations_implies_triangle (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
  : Lemma
    (requires (
      // No edge can be relaxed (negative cycle check passes)
      forall (u v: nat). u < n /\ v < n ==>
        (let d_u = Seq.index dist u in
         let d_v = Seq.index dist v in
         let w = Seq.index weights (u * n + v) in
         w >= inf \/ d_u >= inf \/ d_v <= d_u + w)
    ))
    (ensures triangle_inequality dist weights)
  =
  // The precondition is logically equivalent to the triangle inequality.
  // For each edge (u,v), the condition "w >= inf \/ d_u >= inf \/ d_v <= d_u + w"
  // is exactly "(w < inf /\ d_u < inf) ==> d_v <= d_u + w" (by propositional logic).
  ()

(* ===== Connection to Bellman-Ford Relaxation ===== *)

(* Relax a single edge: update dist[v] to min(dist[v], dist[u] + w) if beneficial *)
let relax_edge (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) (u v: nat{u < n /\ v < n}) 
  : dist_vec n =
  let d_u = Seq.index dist u in
  let d_v = Seq.index dist v in
  let w = Seq.index weights (u * n + v) in
  if w < inf && d_u < inf && d_u + w < d_v
  then Seq.upd dist v (d_u + w)
  else dist

(* Relax all edges from vertex u to all vertices v *)
let rec relax_from_u (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) (u: nat{u < n}) (v: nat)
  : Tot (dist_vec n) (decreases (n - v))
  =
  if v >= n then dist
  else relax_from_u (relax_edge dist weights u v) weights u (v + 1)

(* Relax all edges: iterate over all source vertices *)
let rec relax_all (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) (u: nat)
  : Tot (dist_vec n) (decreases (n - u))
  =
  if u >= n then dist
  else relax_all (relax_from_u dist weights u 0) weights (u + 1)

(* One round of Bellman-Ford: relax all edges once *)
let bf_round (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) : dist_vec n =
  relax_all dist weights 0

(* k rounds of Bellman-Ford *)
let rec bf_k_rounds (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) (k: nat)
  : Tot (dist_vec n) (decreases k)
  =
  if k = 0 then dist
  else bf_round (bf_k_rounds dist weights (k - 1)) weights

(* ===== Stability Implies Triangle Inequality ===== *)

(* ---- Monotonicity: relaxation only decreases distances ---- *)

let relax_edge_monotone (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                        (u v: nat{u < n /\ v < n}) (i: nat{i < n})
  : Lemma (ensures Seq.index (relax_edge dist weights u v) i <= Seq.index dist i)
  = ()

let rec relax_from_u_monotone (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                              (u: nat{u < n}) (v: nat) (i: nat{i < n})
  : Lemma (ensures Seq.index (relax_from_u dist weights u v) i <= Seq.index dist i)
          (decreases (n - v))
  = if v >= n then ()
    else (relax_edge_monotone dist weights u v i;
          relax_from_u_monotone (relax_edge dist weights u v) weights u (v + 1) i)

let rec relax_all_monotone (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                           (u: nat) (i: nat{i < n})
  : Lemma (ensures Seq.index (relax_all dist weights u) i <= Seq.index dist i)
          (decreases (n - u))
  = if u >= n then ()
    else (relax_from_u_monotone dist weights u 0 i;
          relax_all_monotone (relax_from_u dist weights u 0) weights (u + 1) i)

(* ---- Order preservation: pointwise-smaller input gives pointwise-smaller output ---- *)

let relax_edge_order (#n: nat) (d1 d2: dist_vec n) (weights: weight_matrix n)
                     (u v: nat{u < n /\ v < n}) (i: nat{i < n})
  : Lemma (requires forall (j: nat{j < n}). Seq.index d1 j <= Seq.index d2 j)
          (ensures Seq.index (relax_edge d1 weights u v) i <= Seq.index (relax_edge d2 weights u v) i)
  = ()

let rec relax_from_u_order (#n: nat) (d1 d2: dist_vec n) (weights: weight_matrix n)
                           (u: nat{u < n}) (v: nat) (i: nat{i < n})
  : Lemma (requires forall (j: nat{j < n}). Seq.index d1 j <= Seq.index d2 j)
          (ensures Seq.index (relax_from_u d1 weights u v) i <= Seq.index (relax_from_u d2 weights u v) i)
          (decreases (n - v))
  = if v >= n then ()
    else begin
      let d1' = relax_edge d1 weights u v in
      let d2' = relax_edge d2 weights u v in
      let aux (j: nat{j < n}) : Lemma (Seq.index d1' j <= Seq.index d2' j)
        = relax_edge_order d1 d2 weights u v j
      in
      FStar.Classical.forall_intro aux;
      relax_from_u_order d1' d2' weights u (v + 1) i
    end

let rec relax_all_order (#n: nat) (d1 d2: dist_vec n) (weights: weight_matrix n)
                        (u: nat) (i: nat{i < n})
  : Lemma (requires forall (j: nat{j < n}). Seq.index d1 j <= Seq.index d2 j)
          (ensures Seq.index (relax_all d1 weights u) i <= Seq.index (relax_all d2 weights u) i)
          (decreases (n - u))
  = if u >= n then ()
    else begin
      let d1' = relax_from_u d1 weights u 0 in
      let d2' = relax_from_u d2 weights u 0 in
      let aux (j: nat{j < n}) : Lemma (Seq.index d1' j <= Seq.index d2' j)
        = relax_from_u_order d1 d2 weights u 0 j
      in
      FStar.Classical.forall_intro aux;
      relax_all_order d1' d2' weights (u + 1) i
    end

(* ---- Stability decomposition: bf_round fixpoint => each relax_from_u is identity ---- *)

(* Key lemma: If bf_round(dist) = dist, then relax_all(dist, u) = dist for all u <= n.
   In particular, relax_from_u(dist, u, 0) = dist for each u.
   
   Proof by induction on u (ascending from 0).
   relax_all(dist, 0) = relax_all(relax_from_u(dist, 0, 0), 1)   [unfolding, since 0 < n]
   
   By monotonicity: relax_from_u(dist, 0, 0) <= dist (pointwise).
   By order-preservation: relax_all(relax_from_u(dist, 0, 0), 1) <= relax_all(dist, 1) (pointwise).
   Also: relax_all(dist, 1) <= dist by monotonicity.
   
   But relax_all(relax_from_u(dist, 0, 0), 1) = relax_all(dist, 0) = dist.
   So: dist = relax_all(relax_from_u(dist, 0, 0), 1) <= relax_from_u(dist, 0, 0) <= dist.
   Hence relax_from_u(dist, 0, 0) = dist (pointwise).
   
   Then relax_all(dist, 1) = relax_all(relax_from_u(dist, 0, 0), 1) = relax_all(dist, 1) = dist.
   Repeat for u = 1, 2, ...  *)

let relax_all_stable_step (#n: pos) (dist: dist_vec n) (weights: weight_matrix n) (u: nat{u < n})
  : Lemma
    (requires Seq.equal (relax_all dist weights u) dist)
    (ensures Seq.equal (relax_from_u dist weights u 0) dist /\
             Seq.equal (relax_all dist weights (u + 1)) dist)
  = let d' = relax_from_u dist weights u 0 in
    // relax_all dist u = relax_all d' (u+1)  [unfolding since u < n]
    assert (relax_all dist weights u == relax_all d' weights (u + 1));
    // So relax_all d' (u+1) = dist
    let squeeze (i: nat{i < n})
      : Lemma (Seq.index d' i == Seq.index dist i)
      = relax_from_u_monotone dist weights u 0 i;       // d'[i] <= dist[i]
        relax_all_monotone d' weights (u + 1) i;          // (relax_all d' (u+1))[i] <= d'[i]
        // dist[i] = (relax_all d' (u+1))[i] <= d'[i] <= dist[i]
        ()
    in
    FStar.Classical.forall_intro squeeze;
    Seq.lemma_eq_intro d' dist;
    // Now: relax_all dist (u+1) = relax_all d' (u+1) = dist
    ()

let rec relax_all_fixpoint_decompose (#n: pos) (dist: dist_vec n) (weights: weight_matrix n) (u: nat{u < n})
  : Lemma
    (requires Seq.equal (relax_all dist weights 0) dist)
    (ensures Seq.equal (relax_from_u dist weights u 0) dist /\
             Seq.equal (relax_all dist weights (u + 1)) dist)
    (decreases u)
  = if u = 0 then
      relax_all_stable_step dist weights 0
    else begin
      relax_all_fixpoint_decompose dist weights (u - 1);
      // IH gives: relax_from_u(dist, u-1, 0) = dist AND relax_all(dist, u) = dist
      relax_all_stable_step dist weights u
    end

(* ---- relax_from_u identity => each edge satisfies triangle inequality ---- *)

(* relax_edge only modifies position v *)
let relax_edge_other (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                     (u v: nat{u < n /\ v < n}) (i: nat{i < n /\ i <> v})
  : Lemma (ensures Seq.index (relax_edge dist weights u v) i == Seq.index dist i)
  = ()

(* During relax_from_u(dist, u, 0), edges 0, 1, ..., v-1 are processed before edge v.
   Since relax_edge(d, u, j) for j != v doesn't change position v,
   the state at position v just before processing edge v equals dist[v]. *)
let rec relax_from_u_preserves_before (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                      (u: nat{u < n}) (v_start: nat) (target: nat{target < n /\ target >= v_start})
  : Lemma (ensures Seq.index (relax_from_u dist weights u v_start) target <=
                   Seq.index (relax_edge dist weights u target) target)
          (decreases (n - v_start))
  = if v_start >= n then
      relax_edge_monotone dist weights u target target
    else if v_start = target then
      // About to process edge target: relax_from_u dist u target = relax_from_u (relax_edge dist u target) u (target+1)
      // Result at target <= (relax_edge dist u target) at target (by monotonicity of remaining steps)
      relax_from_u_monotone (relax_edge dist weights u target) weights u (target + 1) target
    else begin
      // v_start < target: process edge v_start first, which doesn't change position target
      let d' = relax_edge dist weights u v_start in
      relax_edge_other dist weights u v_start target;
      assert (Seq.index d' target == Seq.index dist target);
      // relax_from_u dist u v_start = relax_from_u d' u (v_start + 1)
      // By IH on d' from (v_start+1):
      relax_from_u_preserves_before d' weights u (v_start + 1) target;
      // relax_from_u d' u (v_start+1) at target <= relax_edge d' u target at target
      // Since d'[target] = dist[target] and d'[u] depends on whether u = v_start or not:
      // But relax_edge d' u target depends on d'[u] and d'[target].
      // d'[target] = dist[target]. 
      // d'[u]: if u != v_start, then d'[u] = dist[u], so relax_edge d' u target = relax_edge dist u target.
      // if u = v_start, then d'[u] <= dist[u], so d'[u] + w <= dist[u] + w.
      //   relax_edge d' u target: sets target to min(d'[target], d'[u]+w) = min(dist[target], d'[u]+w)
      //   relax_edge dist u target: sets target to min(dist[target], dist[u]+w)
      //   Since d'[u] <= dist[u]: d'[u]+w <= dist[u]+w
      //   So min(dist[target], d'[u]+w) <= min(dist[target], dist[u]+w)
      //   i.e., relax_edge d' u target at target <= relax_edge dist u target at target
      // In either case: result <= relax_edge dist u target at target.
      relax_edge_monotone dist weights u v_start u;
      // d'[u] <= dist[u]
      ()
    end

(* If relax_from_u(dist, u, 0) = dist at position v, then relax_edge(dist, u, v) = dist at position v *)
let from_u_stable_implies_edge_stable (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                      (u: nat{u < n}) (v: nat{v < n})
  : Lemma
    (requires Seq.index (relax_from_u dist weights u 0) v == Seq.index dist v)
    (ensures Seq.index (relax_edge dist weights u v) v == Seq.index dist v)
  = relax_from_u_preserves_before dist weights u 0 v;
    // (relax_from_u dist u 0)[v] <= (relax_edge dist u v)[v] 
    // dist[v] = (relax_from_u dist u 0)[v] <= (relax_edge dist u v)[v] <= dist[v]
    relax_edge_monotone dist weights u v v

(* If relax_edge(dist, u, v) = dist at position v, then triangle inequality holds for edge (u,v) *)
let stable_edge_satisfies_triangle (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                   (u v: nat{u < n /\ v < n})
  : Lemma
    (requires Seq.index (relax_edge dist weights u v) v == Seq.index dist v)
    (ensures edge_satisfies_triangle dist weights u v)
  = ()

(* ---- Main theorem ---- *)

let stable_distances_have_triangle (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
  : Lemma
    (requires Seq.equal (bf_round dist weights) dist)
    (ensures triangle_inequality dist weights)
  = if n = 0 then ()
    else
      let aux (u v: nat{u < n /\ v < n})
        : Lemma (ensures edge_satisfies_triangle dist weights u v)
        = relax_all_fixpoint_decompose dist weights u;
          from_u_stable_implies_edge_stable dist weights u v;
          stable_edge_satisfies_triangle dist weights u v
      in
      FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux)

(* Corollary: After k rounds, if one more round changes nothing, triangle inequality holds *)
let bf_k_rounds_stable_implies_triangle (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) (k: nat)
  : Lemma
    (requires Seq.equal (bf_k_rounds dist weights (k + 1)) (bf_k_rounds dist weights k))
    (ensures triangle_inequality (bf_k_rounds dist weights k) weights)
  =
  stable_distances_have_triangle (bf_k_rounds dist weights k) weights

(* Main theorem for n-1 rounds (standard Bellman-Ford) *)
let bellman_ford_stable_establishes_triangle (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
  : Lemma
    (requires 
      n >= 1 /\
      Seq.equal (bf_k_rounds dist weights n) (bf_k_rounds dist weights (n - 1))
    )
    (ensures triangle_inequality (bf_k_rounds dist weights (n - 1)) weights)
  =
  bf_k_rounds_stable_implies_triangle dist weights (n - 1)

(*
 * ===== Summary =====
 * 
 * 1. [no_violations_implies_triangle]
 *    "No edge can be relaxed" is logically equivalent to triangle inequality.
 * 
 * 2. [stable_distances_have_triangle]
 *    If bf_round is stable (fixpoint), triangle inequality holds.
 *    Proof: stability => each relax_from_u is identity => each relax_edge is identity
 *    => triangle inequality by contrapositive of relaxation condition.
 * 
 * 3. [bellman_ford_stable_establishes_triangle]
 *    After n-1 rounds with no negative cycle, triangle inequality holds.
 *)
