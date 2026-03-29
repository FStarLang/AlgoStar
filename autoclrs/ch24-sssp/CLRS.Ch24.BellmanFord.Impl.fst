(*
   Bellman-Ford Single-Source Shortest Paths — Verified in Pulse

   Graph: weighted adjacency matrix (n×n flat array, SP.inf = no edge/infinity)
   
   Sentinel constraint: The constant SP.inf encodes infinity. Edge weights and
   all valid shortest-path distances must be strictly less than SP.inf. If any
   true shortest-path distance reaches SP.inf, it becomes indistinguishable
   from "unreachable." F*'s int is mathematical (unbounded), so arithmetic
   overflow is not a concern—only the sentinel comparison matters.
   
   Postcondition:
   - dist[source] == 0
   - All distances valid (< SP.inf or == SP.inf)
   - If no negative cycle (result == true):
     * Triangle inequality: for all edges (u,v), dist[v] <= dist[u] + w(u,v)
     * Upper bound: dist[v] <= sp_dist(weights, n, source, v) for all v
       (from CLRS Corollary 24.3, proved in ShortestPath.Spec)
    - If negative cycle detected (result == false):
      * Exists a violating edge (u,v) with dist[v] > dist[u] + w(u,v)
        (CLRS Corollary 24.5)
    - If no negative-weight cycles (unconditional on result):
      * dist[v] == sp_dist(source, v) for all v (CLRS Theorem 24.4)
   
   Complexity (O(V³)):
   - Initialization: n ticks
   - Main relaxation: (n-1) rounds × n² edge checks = (n-1)n²
   - Negative cycle detection: n² edge checks
   - Total: n + n³ ticks ≤ 2n³ (proven in bellman_ford_cubic_bound)
   
   NO admits. NO assumes.
*)

module CLRS.Ch24.BellmanFord.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = CLRS.Ch24.ShortestPath.Spec

/// No edge violates triangle inequality (including edges to source)
let no_violations (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : prop =
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (forall (u v: nat). u < n /\ v < n ==>
    (let d_u = Seq.index dist u in
     let d_v = Seq.index dist v in
     let w = Seq.index weights (u * n + v) in
     (w < SP.inf /\ d_u < SP.inf) ==> d_v <= d_u + w))

/// no_violations implies triangle_inequality
let no_violations_implies_triangle (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : Lemma
  (requires no_violations dist weights n)
  (ensures triangle_inequality dist weights n)
  = ()

/// Partial no-violations: for edges (u,v) with u < u_bound, or u == u_bound and v < v_bound
let no_violations_partial (dist: Seq.seq int) (weights: Seq.seq int) (n u_bound v_bound: nat) : prop =
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (forall (u v: nat). u < n /\ v < n /\
    (u < u_bound \/ (u == u_bound /\ v < v_bound)) ==>
    (let d_u = Seq.index dist u in
     let d_v = Seq.index dist v in
     let w = Seq.index weights (u * n + v) in
     (w < SP.inf /\ d_u < SP.inf) ==> d_v <= d_u + w))

/// Partial at (n, 0) implies full no_violations
let partial_full (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : Lemma
  (requires no_violations_partial dist weights n n 0)
  (ensures no_violations dist weights n)
  = ()

/// Check if edge (u,v) violates triangle inequality; if so, exists_violation holds
let check_edge_violation (dist: Seq.seq int) (weights: Seq.seq int) (n u v: nat)
    (w du dv: int) (edge_ok: bool) : Lemma
  (requires Seq.length dist == n /\ Seq.length weights == n * n /\
            u < n /\ v < n /\
            w == Seq.index weights (u * n + v) /\
            du == Seq.index dist u /\
            dv == Seq.index dist v /\
            edge_ok == (w >= SP.inf || du >= SP.inf || dv <= du + w))
  (ensures (not edge_ok) ==> exists_violation dist weights n)
  = ()

/// Relaxation step preserves lower bound (conditional on no_neg_cycles_flat)
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let relax_step_lower_bound
  (weights: Seq.seq int) (n source u_idx v_idx: nat)
  (dist_u w_uv old_dist_v new_dist_v: int) (should_update: bool) : Lemma
  (requires
    n > 0 /\ source < n /\ u_idx < n /\ v_idx < n /\
    Seq.length weights == n * n /\
    w_uv == Seq.index weights (u_idx * n + v_idx) /\
    new_dist_v == (if should_update then dist_u + w_uv else old_dist_v) /\
    (should_update ==> (w_uv < SP.inf /\ dist_u < SP.inf /\ dist_u + w_uv < old_dist_v)) /\
    (SP.no_neg_cycles_flat weights n source ==>
      (dist_u >= SP.sp_dist weights n source u_idx /\
       old_dist_v >= SP.sp_dist weights n source v_idx)))
  (ensures
    SP.no_neg_cycles_flat weights n source ==>
      new_dist_v >= SP.sp_dist weights n source v_idx)
  =
  let helper (_:unit) : Lemma
    (requires SP.no_neg_cycles_flat weights n source /\
              dist_u >= SP.sp_dist weights n source u_idx /\
              old_dist_v >= SP.sp_dist weights n source v_idx)
    (ensures new_dist_v >= SP.sp_dist weights n source v_idx)
    =
    if should_update then
      SP.sp_dist_triangle_flat weights n source u_idx v_idx
    else ()
  in
  FStar.Classical.move_requires helper ()
#pop-options

/// Seq.upd preserves lower_bound_inv (conditional)
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let upd_preserves_lower_bound_cond
  (dist weights: Seq.seq int) (n source v_idx: nat) (new_val: int) : Lemma
  (requires Seq.length dist == n /\ v_idx < n /\
            (SP.no_neg_cycles_flat weights n source ==>
              lower_bound_inv dist weights n source /\
              new_val >= SP.sp_dist weights n source v_idx))
  (ensures SP.no_neg_cycles_flat weights n source ==>
    lower_bound_inv (Seq.upd dist v_idx new_val) weights n source)
  =
  let helper (_:unit) : Lemma
    (requires SP.no_neg_cycles_flat weights n source /\
              lower_bound_inv dist weights n source /\
              new_val >= SP.sp_dist weights n source v_idx)
    (ensures lower_bound_inv (Seq.upd dist v_idx new_val) weights n source)
    =
    let aux (w: nat{w < n}) : Lemma
      (Seq.index (Seq.upd dist v_idx new_val) w >= SP.sp_dist weights n source w) =
      if w = v_idx then () else ()
    in
    FStar.Classical.forall_intro aux
  in
  FStar.Classical.move_requires helper ()
#pop-options

/// Initialization satisfies lower bound
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let init_satisfies_lower_bound (dist weights: Seq.seq int) (n source: nat) : Lemma
  (requires Seq.length dist == n /\ n > 0 /\ source < n /\
            Seq.length weights == n * n /\
            (forall (j: nat). j < n ==>
              (if j = source then Seq.index dist j == 0
               else Seq.index dist j == SP.inf)))
  (ensures SP.no_neg_cycles_flat weights n source ==>
    lower_bound_inv dist weights n source)
  =
  let helper (_:unit) : Lemma
    (requires SP.no_neg_cycles_flat weights n source)
    (ensures lower_bound_inv dist weights n source)
    =
    let aux (v: nat{v < n}) : Lemma
      (Seq.index dist v >= SP.sp_dist weights n source v) =
      SP.sp_dist_k_bounded weights n source v (n - 1);
      if v = source then
        SP.sp_dist_source_nonpositive weights n source (n - 1)
      else ()
    in
    FStar.Classical.forall_intro aux
  in
  FStar.Classical.move_requires helper ()
#pop-options

/// Connect BF triangle_inequality + valid_distances to SP.has_triangle_inequality
let bf_to_sp_triangle (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : Lemma
  (requires triangle_inequality dist weights n /\
            valid_distances dist n /\
            Seq.length weights == n * n)
  (ensures SP.has_triangle_inequality dist weights n)
  = ()

/// Helper: establish sp_dist upper bound from triangle inequality + valid_distances
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let bf_sp_upper_bound_cond (dist weights: Seq.seq int) (n source: nat) (flag: bool) : Lemma
  (requires Seq.length dist == n /\
            Seq.length weights == n * n /\
            n > 0 /\ source < n /\
            Seq.index dist source == 0 /\
            valid_distances dist n /\
            (flag == true ==> triangle_inequality dist weights n))
  (ensures flag == true ==>
    (forall (v: nat). v < n ==>
      Seq.index dist v <= SP.sp_dist weights n source v))
  = if flag then begin
      bf_to_sp_triangle dist weights n;
      let aux (v: nat{v < n}) : Lemma 
        (ensures Seq.index dist v <= SP.sp_dist weights n source v) =
        SP.triangle_ineq_implies_upper_bound dist weights n source v
      in
      FStar.Classical.forall_intro aux
    end
#pop-options

/// Combine upper bound (from triangle inequality) and lower bound for equality
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let bf_sp_equality (dist weights: Seq.seq int) (n source: nat) : Lemma
  (requires Seq.length dist == n /\
            Seq.length weights == n * n /\
            n > 0 /\ source < n /\
            Seq.index dist source == 0 /\
            valid_distances dist n /\
            triangle_inequality dist weights n /\
            lower_bound_inv dist weights n source)
  (ensures forall (v: nat). v < n ==>
    Seq.index dist v == SP.sp_dist weights n source v)
  =
  bf_to_sp_triangle dist weights n;
  let aux (v: nat{v < n}) : Lemma
    (ensures Seq.index dist v == SP.sp_dist weights n source v) =
    SP.triangle_ineq_implies_upper_bound dist weights n source v
  in
  FStar.Classical.forall_intro aux
#pop-options

/// Conditional equality: when triangle_ineq AND no_neg_cycles_flat both hold
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let bf_sp_equality_cond (dist weights: Seq.seq int) (n source: nat) (flag: bool) : Lemma
  (requires Seq.length dist == n /\
            Seq.length weights == n * n /\
            n > 0 /\ source < n /\
            Seq.index dist source == 0 /\
            valid_distances dist n /\
            (flag == true ==> triangle_inequality dist weights n) /\
            (SP.no_neg_cycles_flat weights n source ==>
              lower_bound_inv dist weights n source))
  (ensures SP.no_neg_cycles_flat weights n source /\ flag == true ==>
    (forall (v: nat). v < n ==>
      Seq.index dist v == SP.sp_dist weights n source v))
  = if flag then
      Classical.move_requires (fun () -> bf_sp_equality dist weights n source) ()
#pop-options

// ========== Upper Bound Tracking (for nncf ==> no_neg_cycle proof) ==========

/// dist[v] <= sp_dist_k(v, k) for all v
let upper_bound_k (dist: Seq.seq int) (weights: Seq.seq int) (n source: nat) (k: nat) : prop =
  Seq.length dist == n /\
  (forall (v: nat). v < n ==> Seq.index dist v <= SP.sp_dist_k weights n source v k)

/// All edges from u < u_bound to any v have been relaxed (sp_dist version)
let edges_relaxed_sp (dist: Seq.seq int) (weights: Seq.seq int) (n source: nat) (k u_bound: nat) : prop =
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (forall (u v: nat). u < u_bound /\ u < n /\ v < n ==>
    (let w = Seq.index weights (u * n + v) in
     let sp_u = SP.sp_dist_k weights n source u k in
     (w < SP.inf /\ sp_u < SP.inf) ==> Seq.index dist v <= sp_u + w))

/// Edges from u to v < v_bound have been relaxed
let current_u_relaxed (dist: Seq.seq int) (weights: Seq.seq int) (n source: nat) (k u v_bound: nat) : prop =
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  u < n /\
  (forall (v: nat). v < v_bound /\ v < n ==>
    (let w = Seq.index weights (u * n + v) in
     let sp_u = SP.sp_dist_k weights n source u k in
     (w < SP.inf /\ sp_u < SP.inf) ==> Seq.index dist v <= sp_u + w))

// --- Path weight bounded under WIR (allowing negative weights) ---

#push-options "--fuel 2 --ifuel 0 --z3rlimit 30"
let rec path_weight_wir_bounded_strong (p: SP.path) (weights: Seq.seq int) (n: nat)
  : Lemma
    (requires SP.weights_in_range weights n /\ n > 1 /\
              SP.path_valid p n /\ SP.path_all_edges_exist p weights n /\
              SP.path_edges p <= n - 1)
    (ensures (SP.path_edges p == 0 ==> SP.path_weight p weights n == 0) /\
             (SP.path_edges p > 0 ==>
               SP.path_weight p weights n * (n - 1) < SP.path_edges p * SP.inf /\
               SP.path_weight p weights n * (n - 1) > -(SP.path_edges p * SP.inf)))
    (decreases FStar.List.Tot.length p)
  = match p with
    | [_] -> ()
    | u :: tl ->
      match tl with
      | v :: _ ->
        path_weight_wir_bounded_strong tl weights n;
        let w = Seq.index weights (u * n + v) in
        if SP.path_edges tl = 0
        then ()
        else begin
          assert (SP.path_weight p weights n * (n - 1) ==
                  w * (n - 1) + SP.path_weight tl weights n * (n - 1));
          assert (SP.path_edges p == 1 + SP.path_edges tl)
        end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let path_weight_wir_abs_bound (p: SP.path) (weights: Seq.seq int) (n: nat)
  : Lemma
    (requires SP.weights_in_range weights n /\
              SP.path_valid p n /\ SP.path_all_edges_exist p weights n /\
              SP.path_edges p <= n - 1)
    (ensures SP.path_weight p weights n < SP.inf /\
             SP.path_weight p weights n > -(SP.inf))
  = if n = 1 then ()
    else begin
      path_weight_wir_bounded_strong p weights n;
      if SP.path_edges p = 0 then ()
      else begin
        assert (SP.path_weight p weights n * (n - 1) < SP.path_edges p * SP.inf);
        assert (SP.path_edges p <= n - 1)
      end
    end
#pop-options

// --- Chain lemma: sp_dist_triangle_flat along a path from source ---

#push-options "--fuel 2 --ifuel 0 --z3rlimit 60"
let rec sp_dist_chain (weights: Seq.seq int) (n source: nat) (p: SP.path)
  : Lemma
    (requires SP.no_neg_cycles_flat weights n source /\
              SP.weights_in_range weights n /\
              SP.path_source p == source /\
              SP.path_valid p n /\
              SP.path_all_edges_exist p weights n /\
              SP.path_edges p <= n - 1 /\
              SP.sp_dist weights n source source < 0)
    (ensures SP.sp_dist weights n source (SP.path_dest p) <=
               SP.sp_dist weights n source source + SP.path_weight p weights n /\
             SP.sp_dist weights n source (SP.path_dest p) < SP.inf)
    (decreases FStar.List.Tot.length p)
  = match p with
    | [_] -> ()
    | _ :: tl ->
      match tl with
      | _ :: _ ->
        let prefix = SP.path_prefix p in
        SP.path_prefix_source p;
        SP.path_prefix_dest p;
        SP.path_prefix_valid p n;
        SP.path_prefix_edges_exist p weights n;
        SP.path_prefix_edges p;
        SP.path_weight_snoc p weights n;
        SP.path_penult_valid p n;
        SP.path_last_edge_exists p weights n;
        sp_dist_chain weights n source prefix;
        let u = SP.path_penult p in
        let v = SP.path_dest p in
        SP.sp_dist_triangle_flat weights n source u v;
        path_weight_wir_abs_bound p weights n
#pop-options

// --- sp_dist(source) == 0 under nncf + wir ---

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let sp_dist_source_zero_nncf (weights: Seq.seq int) (n source: nat) : Lemma
  (requires SP.no_neg_cycles_flat weights n source /\ SP.weights_in_range weights n)
  (ensures SP.sp_dist weights n source source == 0)
  =
  SP.sp_dist_source_nonpositive weights n source (n - 1);
  if SP.sp_dist weights n source source < 0 then begin
    let p = SP.sp_dist_achievable weights n source source in
    sp_dist_chain weights n source p
  end
#pop-options

// --- sp_dist_k(source, k) == 0 for k <= n-1 ---

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let sp_dist_k_source_zero_nncf (weights: Seq.seq int) (n source: nat) (k: nat) : Lemma
  (requires SP.no_neg_cycles_flat weights n source /\ SP.weights_in_range weights n /\ k <= n - 1)
  (ensures SP.sp_dist_k weights n source source k == 0)
  =
  sp_dist_source_zero_nncf weights n source;
  SP.sp_dist_source_nonpositive weights n source k;
  SP.sp_dist_k_monotone_le weights n source source k (n - 1)
#pop-options

// --- Source edge bound: 0 <= sp_dist_k(u, k) + w(u, source) ---

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let source_edge_bound (weights: Seq.seq int) (n source u_idx: nat) (k: nat) : Lemma
  (requires SP.no_neg_cycles_flat weights n source /\ SP.weights_in_range weights n /\
            u_idx < n /\ k <= n - 1 /\
            SP.sp_dist_k weights n source u_idx k < SP.inf /\
            Seq.index weights (u_idx * n + source) < SP.inf)
  (ensures SP.sp_dist_k weights n source u_idx k + Seq.index weights (u_idx * n + source) >= 0)
  =
  sp_dist_source_zero_nncf weights n source;
  SP.sp_dist_k_monotone_le weights n source u_idx k (n - 1);
  SP.sp_dist_triangle_flat weights n source u_idx source
#pop-options

// --- Init establishes upper_bound_k at 0 ---

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let init_upper_bound_k_0 (dist weights: Seq.seq int) (n source: nat) : Lemma
  (requires Seq.length dist == n /\ n > 0 /\ source < n /\
            (forall (j: nat). j < n ==>
              (if j = source then Seq.index dist j == 0
               else Seq.index dist j == SP.inf)))
  (ensures upper_bound_k dist weights n source 0)
  =
  let aux (v: nat{v < n}) : Lemma
    (Seq.index dist v <= SP.sp_dist_k weights n source v 0) =
    ()
  in
  FStar.Classical.forall_intro aux
#pop-options

// --- Seq.upd preserves upper_bound_k (conditional) ---

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let upd_preserves_upper_bound_k_cond
  (dist weights: Seq.seq int) (n source v_idx: nat) (new_val: int) (k: nat) : Lemma
  (requires Seq.length dist == n /\ v_idx < n /\
            new_val <= Seq.index dist v_idx /\
            (SP.no_neg_cycles_flat weights n source ==>
              upper_bound_k dist weights n source k))
  (ensures SP.no_neg_cycles_flat weights n source ==>
    upper_bound_k (Seq.upd dist v_idx new_val) weights n source k)
  =
  let helper (_:unit) : Lemma
    (requires SP.no_neg_cycles_flat weights n source /\
              upper_bound_k dist weights n source k)
    (ensures upper_bound_k (Seq.upd dist v_idx new_val) weights n source k)
    =
    let aux (w: nat{w < n}) : Lemma
      (Seq.index (Seq.upd dist v_idx new_val) w <= SP.sp_dist_k weights n source w k) =
      ()
    in
    FStar.Classical.forall_intro aux
  in
  FStar.Classical.move_requires helper ()
#pop-options

// --- Seq.upd preserves edges_relaxed_sp (conditional) ---

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let upd_preserves_edges_relaxed_cond
  (dist weights: Seq.seq int) (n source v_idx: nat) (new_val: int) (k u_bound: nat) : Lemma
  (requires Seq.length dist == n /\ Seq.length weights == n * n /\
            v_idx < n /\
            new_val <= Seq.index dist v_idx /\
            (SP.no_neg_cycles_flat weights n source ==>
              edges_relaxed_sp dist weights n source k u_bound))
  (ensures SP.no_neg_cycles_flat weights n source ==>
    edges_relaxed_sp (Seq.upd dist v_idx new_val) weights n source k u_bound)
  =
  let helper (_:unit) : Lemma
    (requires SP.no_neg_cycles_flat weights n source /\
              edges_relaxed_sp dist weights n source k u_bound)
    (ensures edges_relaxed_sp (Seq.upd dist v_idx new_val) weights n source k u_bound)
    = ()
  in
  FStar.Classical.move_requires helper ()
#pop-options

// --- Seq.upd preserves current_u_relaxed (conditional) ---

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let upd_preserves_current_u_cond
  (dist weights: Seq.seq int) (n source v_idx: nat) (new_val: int) (k u v_bound: nat) : Lemma
  (requires Seq.length dist == n /\ Seq.length weights == n * n /\
            v_idx < n /\ u < n /\
            new_val <= Seq.index dist v_idx /\
            (SP.no_neg_cycles_flat weights n source ==>
              current_u_relaxed dist weights n source k u v_bound))
  (ensures SP.no_neg_cycles_flat weights n source ==>
    current_u_relaxed (Seq.upd dist v_idx new_val) weights n source k u v_bound)
  =
  let helper (_:unit) : Lemma
    (requires SP.no_neg_cycles_flat weights n source /\
              current_u_relaxed dist weights n source k u v_bound)
    (ensures current_u_relaxed (Seq.upd dist v_idx new_val) weights n source k u v_bound)
    = ()
  in
  FStar.Classical.move_requires helper ()
#pop-options

// --- Relaxation step establishes current_u_relaxed for the current edge ---

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let relax_step_current_u_edge
  (sdist weights: Seq.seq int) (n source u_idx v_idx: nat)
  (dist_u w_uv old_dist_v new_dist_v: int) (should_update: bool) (k: nat) : Lemma
  (requires
    n > 0 /\ source < n /\ u_idx < n /\ v_idx < n /\ k <= n - 1 /\
    Seq.length weights == n * n /\ Seq.length sdist == n /\
    SP.weights_in_range weights n /\
    w_uv == Seq.index weights (u_idx * n + v_idx) /\
    old_dist_v == Seq.index sdist v_idx /\
    Seq.index sdist source == 0 /\
    new_dist_v == (if should_update then dist_u + w_uv else old_dist_v) /\
    (should_update ==> (w_uv < SP.inf /\ dist_u < SP.inf /\ dist_u + w_uv < old_dist_v /\ v_idx <> source)) /\
    (~should_update ==> (w_uv >= SP.inf \/ dist_u >= SP.inf \/ dist_u + w_uv >= old_dist_v \/ v_idx == source)) /\
    (SP.no_neg_cycles_flat weights n source ==>
      dist_u <= SP.sp_dist_k weights n source u_idx k))
  (ensures
    SP.no_neg_cycles_flat weights n source ==>
      (let w = Seq.index weights (u_idx * n + v_idx) in
       let sp_u = SP.sp_dist_k weights n source u_idx k in
       (w < SP.inf /\ sp_u < SP.inf) ==> new_dist_v <= sp_u + w))
  =
  let helper (_:unit) : Lemma
    (requires SP.no_neg_cycles_flat weights n source /\
              dist_u <= SP.sp_dist_k weights n source u_idx k)
    (ensures
      (let w = Seq.index weights (u_idx * n + v_idx) in
       let sp_u = SP.sp_dist_k weights n source u_idx k in
       (w < SP.inf /\ sp_u < SP.inf) ==> new_dist_v <= sp_u + w))
    =
    let w = Seq.index weights (u_idx * n + v_idx) in
    let sp_u = SP.sp_dist_k weights n source u_idx k in
    if w < SP.inf && sp_u < SP.inf then begin
      if should_update then ()
      else if v_idx = source then
        source_edge_bound weights n source u_idx k
      else ()
    end
  in
  FStar.Classical.move_requires helper ()
#pop-options

// --- Combine current_u_relaxed at n into edges_relaxed_sp ---

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let extend_edges_relaxed
  (dist weights: Seq.seq int) (n source: nat) (k u_done: nat) : Lemma
  (requires n > 0 /\ source < n /\ u_done < n /\
            Seq.length dist == n /\ Seq.length weights == n * n /\
            (SP.no_neg_cycles_flat weights n source ==>
              edges_relaxed_sp dist weights n source k u_done /\
              current_u_relaxed dist weights n source k u_done n))
  (ensures SP.no_neg_cycles_flat weights n source ==>
    edges_relaxed_sp dist weights n source k (u_done + 1))
  =
  let helper (_:unit) : Lemma
    (requires SP.no_neg_cycles_flat weights n source /\
              edges_relaxed_sp dist weights n source k u_done /\
              current_u_relaxed dist weights n source k u_done n)
    (ensures edges_relaxed_sp dist weights n source k (u_done + 1))
    = ()
  in
  FStar.Classical.move_requires helper ()
#pop-options

// --- Helper for advancement: d <= min_over_predecessors ---

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let rec dist_le_min_over_pred
  (weights: Seq.seq int) (n: nat) (s v: nat) (k: nat{k > 0})
  (d best: int) (u_start: nat) : Lemma
  (requires
    Seq.length weights == n * n /\ s < n /\ v < n /\
    d <= best /\ d <= SP.inf /\
    (forall (u: nat). u >= u_start /\ u < n ==>
      (let w = if u * n + v < Seq.length weights then Seq.index weights (u * n + v) else SP.inf in
       let via_u = SP.sp_dist_k weights n s u (k - 1) in
       (via_u < SP.inf /\ w < SP.inf) ==> d <= via_u + w)))
  (ensures d <= SP.min_over_predecessors weights n s v k best u_start)
  (decreases n - u_start)
= if u_start >= n then ()
  else begin
    let w = if u_start * n + v < Seq.length weights then Seq.index weights (u_start * n + v) else SP.inf in
    let via_u = SP.sp_dist_k weights n s u_start (k - 1) in
    let candidate = if via_u < SP.inf && w < SP.inf then via_u + w else SP.inf in
    let new_best = if candidate < best then candidate else best in
    assert (d <= new_best);
    dist_le_min_over_pred weights n s v k d new_best (u_start + 1)
  end
#pop-options

// --- Advancement: upper_bound_k at k + edges_relaxed at n ==> upper_bound_k at k+1 ---

#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
let advance_upper_bound_k (dist weights: Seq.seq int) (n source: nat) (k: nat) : Lemma
  (requires
    SP.no_neg_cycles_flat weights n source /\
    SP.weights_in_range weights n /\
    upper_bound_k dist weights n source k /\
    edges_relaxed_sp dist weights n source k n /\
    k < n - 1)
  (ensures upper_bound_k dist weights n source (k + 1))
  =
  let aux (v: nat{v < n}) : Lemma
    (Seq.index dist v <= SP.sp_dist_k weights n source v (k + 1)) =
    let d = Seq.index dist v in
    let without = SP.sp_dist_k weights n source v k in
    SP.sp_dist_k_bounded weights n source v k;
    dist_le_min_over_pred weights n source v (k + 1) d without 0
  in
  FStar.Classical.forall_intro aux
#pop-options

// --- Advancement conditional wrapper ---

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let advance_upper_bound_k_cond (dist weights: Seq.seq int) (n source: nat) (k: nat) : Lemma
  (requires
    SP.weights_in_range weights n /\ n > 0 /\ source < n /\
    Seq.length dist == n /\ Seq.length weights == n * n /\
    k < n - 1 /\
    (SP.no_neg_cycles_flat weights n source ==>
      upper_bound_k dist weights n source k /\
      edges_relaxed_sp dist weights n source k n))
  (ensures SP.no_neg_cycles_flat weights n source ==>
    upper_bound_k dist weights n source (k + 1))
  =
  Classical.move_requires (fun () -> advance_upper_bound_k dist weights n source k) ()
#pop-options

// --- Under nncf + equality, each edge check passes ---

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let nncf_edge_ok (dist weights: Seq.seq int) (n source u v: nat) : Lemma
  (requires
    SP.no_neg_cycles_flat weights n source /\
    SP.weights_in_range weights n /\
    Seq.length dist == n /\ Seq.length weights == n * n /\
    u < n /\ v < n /\
    (forall (w: nat). w < n ==> Seq.index dist w == SP.sp_dist weights n source w))
  (ensures
    (let d_u = Seq.index dist u in
     let d_v = Seq.index dist v in
     let w = Seq.index weights (u * n + v) in
     w >= SP.inf \/ d_u >= SP.inf \/ d_v <= d_u + w))
  =
  let d_u = Seq.index dist u in
  let d_v = Seq.index dist v in
  let w = Seq.index weights (u * n + v) in
  if w < SP.inf && d_u < SP.inf then
    SP.sp_dist_triangle_flat weights n source u v
#pop-options

// --- Under nncf + upper/lower bounds, no violations ---

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let nncf_implies_no_violations
  (dist weights: Seq.seq int) (n source: nat) : Lemma
  (requires
    SP.weights_in_range weights n /\ n > 0 /\ source < n /\
    Seq.length dist == n /\ Seq.length weights == n * n /\
    Seq.index dist source == 0 /\
    valid_distances dist n /\
    (SP.no_neg_cycles_flat weights n source ==>
      lower_bound_inv dist weights n source /\
      upper_bound_k dist weights n source (n - 1)))
  (ensures SP.no_neg_cycles_flat weights n source ==>
    no_violations dist weights n)
  =
  let helper (_:unit) : Lemma
    (requires SP.no_neg_cycles_flat weights n source /\
              lower_bound_inv dist weights n source /\
              upper_bound_k dist weights n source (n - 1))
    (ensures no_violations dist weights n)
    =
    let aux (u: nat{u < n}) : Lemma
      (forall (v: nat). v < n ==>
                (let d_u = Seq.index dist u in
                 let d_v = Seq.index dist v in
                 let w = Seq.index weights (u * n + v) in
                 (w < SP.inf /\ d_u < SP.inf) ==> d_v <= d_u + w))
      =
      let aux2 (v: nat{v < n}) : Lemma
        (let d_u = Seq.index dist u in
         let d_v = Seq.index dist v in
         let w = Seq.index weights (u * n + v) in
         (w < SP.inf /\ d_u < SP.inf) ==> d_v <= d_u + w) =
        let d_u = Seq.index dist u in
        let w = Seq.index weights (u * n + v) in
        if w < SP.inf && d_u < SP.inf then
          SP.sp_dist_triangle_flat weights n source u v
      in
      FStar.Classical.forall_intro aux2
    in
    FStar.Classical.forall_intro aux
  in
  Classical.move_requires helper ()
#pop-options

// ========== Main Algorithm ==========

// Ghost tick for complexity counting
let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

// Pure complexity bounds

(**
 * Simplify: n + (n-1)n² + n² = n + n³ - n² + n² = n + n³
 *)
let bellman_ford_simplified (n: nat) : Lemma
  (requires n >= 1)
  (ensures bellman_ford_iterations n == n + n * n * n)
  =
  assert ((n - 1) * n * n + n * n == n * n * n)

(**
 * Main complexity bound: prove the total is at most 2n³ for n ≥ 1
 * This establishes O(n³) asymptotic complexity.
 *)
let bellman_ford_cubic_bound (n: nat) : Lemma
  (requires n >= 1)
  (ensures bellman_ford_iterations n <= 2 * n * n * n)
  =
  bellman_ford_simplified n;
  assert (n >= 1);
  assert (n <= n * n);
  assert (n * n <= n * n * n);
  assert (n + n * n * n <= 2 * n * n * n)

(**
 * Lower bound: for n ≥ 2, we do at least n³ operations
 *)
let bellman_ford_lower_bound (n: nat) : Lemma
  (requires n >= 2)
  (ensures bellman_ford_iterations n >= n * n * n)
  =
  bellman_ford_simplified n;
  assert (n + n * n * n >= n * n * n)

/// Ghost counter proves O(n³): cf - c0 ≤ 2n³
let bellman_ford_complexity_is_cubic (cf c0 n: nat) : Lemma
  (requires bellman_ford_complexity_bounded cf c0 n /\ n >= 1)
  (ensures cf - c0 <= 2 * n * n * n)
  =
  bellman_ford_cubic_bound n

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0 --split_queries always"
//SNIPPET_START: bellman_ford_sig
fn bellman_ford
  (weights: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (dist: A.array int)
  (result: R.ref bool)
  (#sweights: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#sresult: erased bool)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist **
    R.pts_to result sresult **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      Seq.length sdist == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      SP.weights_in_range sweights (SZ.v n)
    )
  ensures exists* sdist' no_neg_cycle (cf: nat).
    A.pts_to weights sweights **
    A.pts_to dist sdist' **
    R.pts_to result no_neg_cycle **
    GR.pts_to ctr cf **
    pure (
      Seq.length sdist' == SZ.v n /\
      SZ.v source < Seq.length sdist' /\
      Seq.index sdist' (SZ.v source) == 0 /\
      valid_distances sdist' (SZ.v n) /\
      (no_neg_cycle == true ==> triangle_inequality sdist' sweights (SZ.v n)) /\
      // Shortest-path upper bound (CLRS Corollary 24.3):
      (no_neg_cycle == true ==>
        (forall (v: nat). v < SZ.v n ==>
          Seq.index sdist' v <= SP.sp_dist sweights (SZ.v n) (SZ.v source) v)) /\
      // Negative-cycle detection (CLRS Corollary 24.5):
      (no_neg_cycle == false ==> exists_violation sdist' sweights (SZ.v n)) /\
      // Lower bound: dist[v] >= sp_dist[v] (under no negative cycles)
      (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
        lower_bound_inv sdist' sweights (SZ.v n) (SZ.v source)) /\
      // Shortest-path equality (CLRS Theorem 24.4):
      (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) /\ no_neg_cycle == true ==>
        (forall (v: nat). v < SZ.v n ==>
          Seq.index sdist' v == SP.sp_dist sweights (SZ.v n) (SZ.v source) v)) /\
      // No negative cycles implies no_neg_cycle == true:
      (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==> no_neg_cycle == true) /\
      // O(V³) complexity bound
      bellman_ford_complexity_bounded cf (reveal c0) (SZ.v n)
    )
//SNIPPET_END: bellman_ford_sig
{
  // Initialization: dist[source] = 0, all others = inf
  let mut init_i: SZ.t = 0sz;
  
  while (
    let vi = !init_i;
    vi <^ n
  )
  invariant exists* vi sdist_current (vc: nat).
    R.pts_to init_i vi **
    A.pts_to dist sdist_current **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length sdist_current == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==>
        (if j = SZ.v source 
         then Seq.index sdist_current j == 0 
         else Seq.index sdist_current j == SP.inf)) /\
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v vi
    )
  decreases (SZ.v n - SZ.v !init_i)
  {
    let vi = !init_i;
    let new_val: int = (if vi = source then 0 else SP.inf);
    A.op_Array_Assignment dist vi new_val;
    tick ctr;
    init_i := vi +^ 1sz;
  };
  
  let _ = !init_i;
  
  // Establish lower bound after initialization
  with sdist_init. assert (A.pts_to dist sdist_init);
  init_satisfies_lower_bound sdist_init sweights (SZ.v n) (SZ.v source);
  // Establish upper bound at k=0 after initialization
  init_upper_bound_k_0 sdist_init sweights (SZ.v n) (SZ.v source);
  
  // Relaxation: n-1 rounds
  let mut round: SZ.t = 1sz;
  
  while (
    let vround = !round;
    vround <^ n
  )
  invariant exists* vround sdist_current (vc: nat).
    R.pts_to round vround **
    A.pts_to dist sdist_current **
    GR.pts_to ctr vc **
    pure (
      SZ.v vround >= 1 /\
      SZ.v vround <= SZ.v n /\
      Seq.length sdist_current == SZ.v n /\
      Seq.index sdist_current (SZ.v source) == 0 /\
      valid_distances sdist_current (SZ.v n) /\
      (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
        lower_bound_inv sdist_current sweights (SZ.v n) (SZ.v source)) /\
      (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
        upper_bound_k sdist_current sweights (SZ.v n) (SZ.v source) (SZ.v vround - 1)) /\
      vc >= reveal c0 /\
      vc - reveal c0 == SZ.v n + (SZ.v vround - 1) * SZ.v n * SZ.v n
    )
  decreases (SZ.v n - SZ.v !round)
  {
    let vround = !round;
    
    let mut u: SZ.t = 0sz;
    
    while (
      let vu = !u;
      vu <^ n
    )
    invariant exists* vu sdist_u (vc_u: nat).
      R.pts_to u vu **
      A.pts_to dist sdist_u **
      GR.pts_to ctr vc_u **
      pure (
        SZ.v vu <= SZ.v n /\
        Seq.length sdist_u == SZ.v n /\
        Seq.index sdist_u (SZ.v source) == 0 /\
        valid_distances sdist_u (SZ.v n) /\
        (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
          lower_bound_inv sdist_u sweights (SZ.v n) (SZ.v source)) /\
        (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
          upper_bound_k sdist_u sweights (SZ.v n) (SZ.v source) (SZ.v vround - 1)) /\
        (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
          edges_relaxed_sp sdist_u sweights (SZ.v n) (SZ.v source) (SZ.v vround - 1) (SZ.v vu)) /\
        vc_u >= reveal c0 /\
        vc_u - reveal c0 == SZ.v n + (SZ.v vround - 1) * SZ.v n * SZ.v n + SZ.v vu * SZ.v n
      )
    decreases (SZ.v n - SZ.v !u)
    {
      let vu = !u;
      let dist_u = A.op_Array_Access dist vu;
      
      assert pure (dist_u < SP.inf \/ dist_u == SP.inf);
      
      // Under nncf, dist_u <= sp_dist_k(vu, vround-1)
      with sdist_before_v. assert (A.pts_to dist sdist_before_v);
      assert pure (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
        dist_u <= SP.sp_dist_k sweights (SZ.v n) (SZ.v source) (SZ.v vu) (SZ.v vround - 1));
      
      let mut v: SZ.t = 0sz;
      
      while (
        let vv = !v;
        vv <^ n
      )
      invariant exists* vv sdist_v (vc_v: nat).
        R.pts_to v vv **
        A.pts_to dist sdist_v **
        GR.pts_to ctr vc_v **
        pure (
          SZ.v vv <= SZ.v n /\
          Seq.length sdist_v == SZ.v n /\
          Seq.index sdist_v (SZ.v source) == 0 /\
          valid_distances sdist_v (SZ.v n) /\
          (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
            lower_bound_inv sdist_v sweights (SZ.v n) (SZ.v source)) /\
          (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
            upper_bound_k sdist_v sweights (SZ.v n) (SZ.v source) (SZ.v vround - 1)) /\
          (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
            edges_relaxed_sp sdist_v sweights (SZ.v n) (SZ.v source) (SZ.v vround - 1) (SZ.v vu)) /\
          (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
            current_u_relaxed sdist_v sweights (SZ.v n) (SZ.v source) (SZ.v vround - 1) (SZ.v vu) (SZ.v vv)) /\
          vc_v >= reveal c0 /\
          vc_v - reveal c0 == SZ.v n + (SZ.v vround - 1) * SZ.v n * SZ.v n + SZ.v vu * SZ.v n + SZ.v vv
        )
      decreases (SZ.v n - SZ.v !v)
      {
        let vv = !v;
        with sdist_v. assert (A.pts_to dist sdist_v);
        
        let w_idx = vu *^ n +^ vv;
        let w_uv = A.op_Array_Access weights w_idx;
        
        let old_dist_v = A.op_Array_Access dist vv;
        
        let can_relax = (w_uv < SP.inf && dist_u < SP.inf);
        let sum = dist_u + w_uv;
        let should_update = (can_relax && sum < old_dist_v && vv <> source);
        
        let new_dist_v: int = (if should_update then sum else old_dist_v);
        
        assert pure (old_dist_v < SP.inf \/ old_dist_v == SP.inf);
        
        if should_update {
          assert pure (sum < SP.inf);
        };
        
        assert pure (new_dist_v < SP.inf \/ new_dist_v == SP.inf);
        
        if (vv = source) {
          assert pure (old_dist_v == 0);
          assert pure (new_dist_v == 0);
        };
        
        // Preserve lower bound through relaxation
        relax_step_lower_bound sweights (SZ.v n) (SZ.v source) (SZ.v vu) (SZ.v vv)
          dist_u w_uv old_dist_v new_dist_v should_update;
        upd_preserves_lower_bound_cond sdist_v sweights (SZ.v n) (SZ.v source) (SZ.v vv)
          new_dist_v;
        
        // Preserve upper bound through relaxation
        upd_preserves_upper_bound_k_cond sdist_v sweights (SZ.v n) (SZ.v source) (SZ.v vv)
          new_dist_v (SZ.v vround - 1);
        // Preserve edges_relaxed through relaxation
        upd_preserves_edges_relaxed_cond sdist_v sweights (SZ.v n) (SZ.v source) (SZ.v vv)
          new_dist_v (SZ.v vround - 1) (SZ.v vu);
        // Preserve current_u_relaxed through relaxation
        upd_preserves_current_u_cond sdist_v sweights (SZ.v n) (SZ.v source) (SZ.v vv)
          new_dist_v (SZ.v vround - 1) (SZ.v vu) (SZ.v vv);
        // Establish current_u_relaxed for current edge
        assert pure (~should_update ==> (w_uv >= SP.inf \/ dist_u >= SP.inf \/ dist_u + w_uv >= old_dist_v \/ (SZ.v vv) == (SZ.v source)));
        relax_step_current_u_edge sdist_v sweights (SZ.v n) (SZ.v source) (SZ.v vu) (SZ.v vv)
          dist_u w_uv old_dist_v new_dist_v should_update (SZ.v vround - 1);
        
        A.op_Array_Assignment dist vv new_dist_v;
        tick ctr;
        
        v := vv +^ 1sz;
      };
      
      // After v-loop: current_u_relaxed at n, combine into edges_relaxed
      let _ = !v;
      with sdist_after_v. assert (A.pts_to dist sdist_after_v);
      extend_edges_relaxed sdist_after_v sweights (SZ.v n) (SZ.v source) (SZ.v vround - 1) (SZ.v vu);
      u := vu +^ 1sz;
    };
    
    // After u-loop: advance upper_bound_k from vround-1 to vround
    let _ = !u;
    with sdist_after_round. assert (A.pts_to dist sdist_after_round);
    if (vround <^ (n -^ 1sz)) {
      advance_upper_bound_k_cond sdist_after_round sweights (SZ.v n) (SZ.v source) (SZ.v vround - 1);
    } else {
      // Last round: vround == n-1, upper_bound_k at n-2.
      // edges_relaxed at n: all edges processed.
      // We could advance to n-1 but advance requires k < n-1.
      // vround - 1 == n - 2, so k = n-2 < n-1 iff n > 2. For n == 2: k = 0 < 1 = n-1. ✓
      // For n == 1: no rounds (loop doesn't execute). This branch won't be reached for n==1.
      advance_upper_bound_k_cond sdist_after_round sweights (SZ.v n) (SZ.v source) (SZ.v vround - 1);
    };
    round := vround +^ 1sz;
  };
  
  let _ = !round;
  
  // === Establish nncf ==> no_violations before check phase ===
  with sdist_pre_check. assert (A.pts_to dist sdist_pre_check);
  nncf_implies_no_violations sdist_pre_check sweights (SZ.v n) (SZ.v source);
  
  // === Negative-cycle detection + triangle inequality verification ===
  // Read-only pass: check if any edge (u,v) violates dist[v] <= dist[u] + w.
  // If no violation, triangle inequality holds.
  let mut no_neg: bool = true;
  let mut cu: SZ.t = 0sz;
  
  while (
    let vcu = !cu;
    vcu <^ n
  )
  invariant exists* vcu sdist_check vno (vc_c: nat).
    R.pts_to cu vcu **
    R.pts_to no_neg vno **
    A.pts_to dist sdist_check **
    GR.pts_to ctr vc_c **
    pure (
      SZ.v vcu <= SZ.v n /\
      Seq.length sdist_check == SZ.v n /\
      Seq.index sdist_check (SZ.v source) == 0 /\
      valid_distances sdist_check (SZ.v n) /\
      (vno == true ==> no_violations_partial sdist_check sweights (SZ.v n) (SZ.v vcu) 0) /\
      (vno == false ==> exists_violation sdist_check sweights (SZ.v n)) /\
      (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
        lower_bound_inv sdist_check sweights (SZ.v n) (SZ.v source)) /\
      (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
        no_violations sdist_check sweights (SZ.v n)) /\
      (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==> vno == true) /\
      vc_c >= reveal c0 /\
      vc_c - reveal c0 == SZ.v n + (SZ.v n - 1) * SZ.v n * SZ.v n + SZ.v vcu * SZ.v n
    )
  decreases (SZ.v n - SZ.v !cu)
  {
    let vcu = !cu;
    with sdist_check. assert (A.pts_to dist sdist_check);
    let dist_cu = A.op_Array_Access dist vcu;
    
    let mut cv: SZ.t = 0sz;
    
    while (
      let vcv = !cv;
      vcv <^ n
    )
    invariant exists* vcv vno_inner (vc_cv: nat).
      R.pts_to cv vcv **
      R.pts_to no_neg vno_inner **
      A.pts_to dist sdist_check **
      GR.pts_to ctr vc_cv **
      pure (
        SZ.v vcv <= SZ.v n /\
        (vno_inner == true ==> no_violations_partial sdist_check sweights (SZ.v n) (SZ.v vcu) (SZ.v vcv)) /\
        (vno_inner == false ==> exists_violation sdist_check sweights (SZ.v n)) /\
        (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
          no_violations sdist_check sweights (SZ.v n)) /\
        (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==> vno_inner == true) /\
        vc_cv >= reveal c0 /\
        vc_cv - reveal c0 == SZ.v n + (SZ.v n - 1) * SZ.v n * SZ.v n + SZ.v vcu * SZ.v n + SZ.v vcv
      )
    decreases (SZ.v n - SZ.v !cv)
    {
      let vcv = !cv;
      
      let w_idx = vcu *^ n +^ vcv;
      let w = A.op_Array_Access weights w_idx;
      let d_u = dist_cu;
      let d_v = A.op_Array_Access dist vcv;
      
      // Check triangle inequality for this edge
      let edge_ok = (w >= SP.inf || d_u >= SP.inf || d_v <= d_u + w);
      
      let vno = !no_neg;
      // Must call before the if — Pulse can't call lemmas inside if blocks
      check_edge_violation sdist_check sweights (SZ.v n) (SZ.v vcu) (SZ.v vcv) w d_u d_v edge_ok;
      // Under nncf: no_violations holds, so edge_ok must be true
      assert pure (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==> edge_ok == true);
      if (not edge_ok) {
        no_neg := false;
      };
      
      tick ctr;
      
      cv := vcv +^ 1sz;
    };
    
    let _ = !cv;
    cu := vcu +^ 1sz;
  };
  
  let _ = !cu;
  
  let final_no_neg = !no_neg;
  with sdist_final. assert (A.pts_to dist sdist_final);
  // Connect triangle inequality to shortest-path upper bound
  bf_sp_upper_bound_cond sdist_final sweights (SZ.v n) (SZ.v source) final_no_neg;
  // Connect upper + lower bound to equality (under no_neg_cycles_flat)
  bf_sp_equality_cond sdist_final sweights (SZ.v n) (SZ.v source) final_no_neg;
  
  // At this point: cf - c0 == n + (n-1)n² + n² == n + n³
  assert pure (SZ.v n >= 1);
  bellman_ford_simplified (SZ.v n);
  
  result := final_no_neg;
}
#pop-options
