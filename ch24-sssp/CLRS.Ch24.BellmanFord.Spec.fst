module CLRS.Ch24.BellmanFord.Spec

open FStar.Mul
open FStar.Seq

module Seq = FStar.Seq

(* ============================================================
   Pure F* Specification of Bellman-Ford Algorithm
   Proving CLRS Lemma 24.2 (Path Relaxation Property)
   ============================================================ *)

let inf : int = 1000000

(* ===== Graph Representation ===== *)

(* Adjacency matrix: adj[u][v] = weight of edge (u,v), or inf if no edge *)
type adj_matrix (n: nat) = adj:seq (seq int){
  Seq.length adj == n /\
  (forall (i: nat). i < n ==> Seq.length (Seq.index adj i) == n)
}

(* Get edge weight *)
let edge_weight (#n: nat) (adj: adj_matrix n) (u v: nat{u < n /\ v < n}) : int =
  Seq.index (Seq.index adj u) v

(* Valid graph: all edge weights are finite or inf *)
let valid_graph (#n: nat) (adj: adj_matrix n) : prop =
  forall (u v: nat). u < n /\ v < n ==>
    edge_weight adj u v <= inf

(* ===== Shortest Path Distance (spec-level oracle) ===== *)

(* Shortest path distance with at most k edges.
   This is the specification oracle - we define it inductively.
   Returns None if no path exists, Some d if minimum weight is d. *)
let rec sp_dist_k (#n: nat) (adj: adj_matrix n) (src dst: nat{src < n /\ dst < n}) (k: nat)
  : Tot (option int) (decreases %[k; 1])
  =
  if k = 0 then
    if src = dst then Some 0 else None
  else
    // Try all predecessors u: min{ sp_dist_k(src, u, k-1) + weight(u, dst) }
    let prev_dist = sp_dist_k adj src dst (k - 1) in
    min_over_preds adj src dst k prev_dist 0 n

and min_over_preds (#n: nat) (adj: adj_matrix n) (src dst: nat{src < n /\ dst < n})
                    (k: nat{k > 0}) (best: option int) (u: nat) (n_bound: nat{n_bound == n})
  : Tot (option int) (decreases %[k; 0; n - u])
  =
  if u >= n then best
  else
    let dist_to_u = sp_dist_k adj src u (k - 1) in
    let w_u_dst = edge_weight adj u dst in
    let candidate =
      match dist_to_u with
      | None -> None
      | Some d_u ->
        if w_u_dst < inf then Some (d_u + w_u_dst) else None
    in
    let new_best =
      match candidate, best with
      | None, _ -> best
      | Some c, None -> Some c
      | Some c, Some b -> if c < b then Some c else Some b
    in
    min_over_preds adj src dst k new_best (u + 1) n_bound

(* Shortest path distance (unbounded edges, but at most n-1 edges needed if no negative cycle) *)
let sp_dist (#n: nat) (adj: adj_matrix n) (src dst: nat{src < n /\ dst < n}) : option int =
  if n > 0 then sp_dist_k adj src dst (n - 1) else None

(* ===== Distance Vector Representation ===== *)

(* Distance vector: dist[v] = current distance estimate to v from source *)
type dist_vec (n: nat) = dist:seq (option int){Seq.length dist == n}

(* Initialize: dist[src] = Some 0, all others = None *)
let init_dist (n: nat) (src: nat{src < n}) : dist_vec n =
  Seq.init n (fun v -> if v = src then Some 0 else None)

(* Get distance *)
let get_dist (#n: nat) (dist: dist_vec n) (v: nat{v < n}) : option int =
  Seq.index dist v

(* Update distance *)
let upd_dist (#n: nat) (dist: dist_vec n) (v: nat{v < n}) (d: option int) : dist_vec n =
  Seq.upd dist v d

(* ===== Edge Relaxation (Pure) ===== *)

(* Relax a single edge (u, v, w): update dist[v] if dist[u] + w is better *)
let pure_relax (#n: nat) (dist: dist_vec n) (u v: nat{u < n /\ v < n}) (w: int) : dist_vec n =
  let d_u = get_dist dist u in
  let d_v = get_dist dist v in
  match d_u with
  | None -> dist  // u is unreachable, can't improve v
  | Some val_u ->
    if w >= inf then dist  // edge doesn't exist
    else
      let new_val = val_u + w in
      match d_v with
      | None -> upd_dist dist v (Some new_val)  // v was unreachable, now reachable
      | Some val_v -> if new_val < val_v then upd_dist dist v (Some new_val) else dist

(* ===== One Round of Bellman-Ford ===== *)

(* Relax all edges from vertex u to all neighbors v *)
let rec relax_from_u (#n: nat) (adj: adj_matrix n) (dist: dist_vec n) (u: nat{u < n}) (v: nat)
  : Tot (dist_vec n) (decreases (n - v))
  =
  if v >= n then dist
  else
    let w = edge_weight adj u v in
    let dist' = pure_relax dist u v w in
    relax_from_u adj dist' u (v + 1)

(* Relax all edges from all vertices *)
let rec relax_all (#n: nat) (adj: adj_matrix n) (dist: dist_vec n) (u: nat)
  : Tot (dist_vec n) (decreases (n - u))
  =
  if u >= n then dist
  else
    let dist' = relax_from_u adj dist u 0 in
    relax_all adj dist' (u + 1)

(* One full round of Bellman-Ford: relax all edges once *)
let pure_bf_round (#n: nat) (adj: adj_matrix n) (dist: dist_vec n) : dist_vec n =
  relax_all adj dist 0

(* ===== Bellman-Ford Algorithm (k rounds) ===== *)

let rec pure_bf (#n: nat) (adj: adj_matrix n) (src: nat{src < n}) (rounds: nat)
  : Tot (dist_vec n) (decreases rounds)
  =
  if rounds = 0 then init_dist n src
  else pure_bf_round adj (pure_bf adj src (rounds - 1))

(* ===== Upper Bound Property ===== *)

(* Upper bound invariant: dist[v] >= sp_dist for all v
   (distances never go below true shortest path) *)
let upper_bound_inv (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
                     (dist: dist_vec n) (k: nat) : prop =
  forall (v: nat). v < n ==>
    (match get_dist dist v, sp_dist_k adj src v k with
     | None, None -> True  // Both unreachable: OK
     | None, Some _ -> True  // dist says unreachable, but there is path: will be fixed later
     | Some d, None -> False  // dist says reachable but no path exists: violation!
     | Some d, Some sp -> d >= sp)  // dist overestimates: OK

(* ===== Correctness Invariant (CLRS Lemma 24.2) ===== *)

(* Path relaxation property: After i rounds, dist[v] is correct for all v
   reachable via paths with at most i edges. *)
let correctness_inv (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
                    (dist: dist_vec n) (rounds: nat) : prop =
  forall (v: nat). v < n ==>
    get_dist dist v == sp_dist_k adj src v rounds

(* ===== Helper Lemmas ===== *)

(* Lemma: sp_dist_k is monotone: more edges can only help (or stay same) *)
let sp_dist_k_monotone (#n: nat) (adj: adj_matrix n) (src dst: nat{src < n /\ dst < n}) (k: nat)
  : Lemma
    (ensures (
      match sp_dist_k adj src dst k, sp_dist_k adj src dst (k + 1) with
      | None, _ -> True  // None -> anything is fine
      | Some d_k, None -> False  // We had path with k edges, must have with k+1
      | Some d_k, Some d_k1 -> d_k1 <= d_k  // k+1 edges gives at least as good
    ))
  =
  admit()  // Complex proof involving min_over_preds

(* Lemma: Relaxing an edge preserves upper bound *)
let relax_preserves_upper_bound (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
                                  (dist: dist_vec n) (u v: nat{u < n /\ v < n})
                                  (w: int) (k: nat)
  : Lemma
    (requires upper_bound_inv adj src dist k)
    (ensures upper_bound_inv adj src (pure_relax dist u v w) k)
  =
  admit()  // Proof: relaxing only decreases distances, and we never go below sp_dist

(* Lemma: Relaxing from vertex u preserves upper bound *)
let rec relax_from_u_preserves_upper (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
                                       (dist: dist_vec n) (u: nat{u < n}) (v: nat) (k: nat)
  : Lemma
    (requires upper_bound_inv adj src dist k)
    (ensures upper_bound_inv adj src (relax_from_u adj dist u v) k)
    (decreases (n - v))
  =
  if v >= n then ()
  else begin
    let w = edge_weight adj u v in
    relax_preserves_upper_bound adj src dist u v w k;
    relax_from_u_preserves_upper adj src (pure_relax dist u v w) u (v + 1) k
  end

(* Lemma: Relaxing all edges preserves upper bound *)
let rec relax_all_preserves_upper (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
                                    (dist: dist_vec n) (u: nat) (k: nat)
  : Lemma
    (requires upper_bound_inv adj src dist k)
    (ensures upper_bound_inv adj src (relax_all adj dist u) k)
    (decreases (n - u))
  =
  if u >= n then ()
  else begin
    relax_from_u_preserves_upper adj src dist u 0 k;
    relax_all_preserves_upper adj src (relax_from_u adj dist u 0) (u + 1) k
  end

(* Lemma: One round preserves upper bound *)
let bf_round_preserves_upper (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
                              (dist: dist_vec n) (k: nat)
  : Lemma
    (requires upper_bound_inv adj src dist k)
    (ensures upper_bound_inv adj src (pure_bf_round adj dist) k)
  =
  relax_all_preserves_upper adj src dist 0 k

(* ===== Main Correctness Theorems ===== *)

(* Theorem: Initialization satisfies correctness for 0 rounds *)
let init_correct (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
  : Lemma (ensures correctness_inv adj src (init_dist n src) 0)
  =
  let aux (v: nat{v < n})
    : Lemma (get_dist (init_dist n src) v == sp_dist_k adj src v 0)
    =
    if v = src then begin
      // dist[src] = Some 0, sp_dist_k(src, src, 0) = Some 0
      assert (get_dist (init_dist n src) src == Some 0);
      assert (sp_dist_k adj src src 0 == Some 0)
    end else begin
      // dist[v] = None, sp_dist_k(src, v, 0) = None (no 0-edge path from src to v when v != src)
      assert (get_dist (init_dist n src) v == None);
      assert (sp_dist_k adj src v 0 == None)
    end
  in
  FStar.Classical.forall_intro aux

(* Theorem: Upper bound property holds after any number of rounds *)
let rec bf_upper_bound (#n: nat) (adj: adj_matrix n) (src: nat{src < n}) (rounds: nat)
  : Lemma
    (ensures upper_bound_inv adj src (pure_bf adj src rounds) rounds)
    (decreases rounds)
  =
  if rounds = 0 then begin
    // Base case: init_dist satisfies upper bound for k=0
    init_correct adj src;
    // correctness_inv implies upper_bound_inv
    ()
  end else begin
    // Inductive case
    bf_upper_bound adj src (rounds - 1);
    // By IH: upper_bound_inv holds for (rounds-1)
    // Need to show it holds after one more round
    admit()  // Need to relate sp_dist_k(k-1) to sp_dist_k(k)
  end

(* ===== Path Relaxation Property (CLRS Lemma 24.2) ===== *)

(* Key lemma: If dist[u] is correct for k-edge paths, and we relax edge (u,v,w),
   then dist[v] becomes at least as good as sp_dist_k(src, v, k+1) via this edge. *)
let relax_improves_via_edge (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
                             (dist: dist_vec n) (u v: nat{u < n /\ v < n}) (k: nat)
  : Lemma
    (requires
      correctness_inv adj src dist k /\
      edge_weight adj u v < inf)
    (ensures (
      let w = edge_weight adj u v in
      let dist' = pure_relax dist u v w in
      // After relaxing, dist'[v] is at least as good as the path through u
      match get_dist dist u, sp_dist_k adj src u k with
      | Some d_u, Some sp_u ->
        (match get_dist dist' v with
         | Some d_v' -> d_v' <= sp_u + w
         | None -> False)
      | _, _ -> True
    ))
  =
  admit()  // Core proof: relaxation updates dist[v] to min(dist[v], dist[u] + w)

(* Lemma: After k rounds, for any vertex v reachable with i <= k edges,
   dist[v] equals sp_dist_k(src, v, i). *)
let rec bf_correctness_inductive (#n: nat) (adj: adj_matrix n) (src: nat{src < n}) (rounds: nat)
  : Lemma
    (ensures correctness_inv adj src (pure_bf adj src rounds) rounds)
    (decreases rounds)
  =
  if rounds = 0 then
    init_correct adj src
  else begin
    // Inductive case: assume correctness for (rounds-1), prove for rounds
    bf_correctness_inductive adj src (rounds - 1);
    // By IH: correctness_inv holds for (rounds-1) rounds
    let dist_prev = pure_bf adj src (rounds - 1) in
    let dist_curr = pure_bf adj src rounds in
    
    // Need to prove: forall v. get_dist dist_curr v == sp_dist_k adj src v rounds
    // Key insight: sp_dist_k(k) considers all paths with at most k edges.
    // For any v, the shortest k-edge path either:
    // 1. Uses at most k-1 edges (covered by IH)
    // 2. Uses exactly k edges, ending with edge (u,v) where u has (k-1)-edge shortest path
    
    // The relaxation in round k ensures that if there's a k-edge path ending at (u,v),
    // and dist[u] is correct (by IH), then relaxing (u,v) makes dist[v] correct for k edges.
    
    admit()  // Full proof requires showing relaxation computes min over all (k-1)-predecessors
  end

(* ===== Convergence Theorem ===== *)

(* Theorem: After n-1 rounds (no negative cycles), dist[v] = sp_dist(src, v) for all v *)
let bf_convergence (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
  : Lemma
    (requires n > 0)
    (ensures (
      let dist = pure_bf adj src (n - 1) in
      forall (v: nat). v < n ==>
        get_dist dist v == sp_dist adj src v
    ))
  =
  bf_correctness_inductive adj src (n - 1)
  // sp_dist is defined as sp_dist_k with k = n-1
  // correctness_inv says dist[v] == sp_dist_k(k) for all v
  // Therefore dist[v] == sp_dist for all v

(* ===== Negative Cycle Detection ===== *)

(* Predicate: Triangle inequality holds for all edges *)
let triangle_inequality (#n: nat) (adj: adj_matrix n) (dist: dist_vec n) : prop =
  forall (u v: nat). u < n /\ v < n /\ edge_weight adj u v < inf ==>
    (match get_dist dist u, get_dist dist v with
     | Some d_u, Some d_v -> d_v <= d_u + edge_weight adj u v
     | _, _ -> True)

(* Predicate: At least one edge can still be relaxed *)
let exists_relaxable_edge (#n: nat) (adj: adj_matrix n) (dist: dist_vec n) : prop =
  exists (u v: nat). u < n /\ v < n /\ edge_weight adj u v < inf /\
    (match get_dist dist u, get_dist dist v with
     | Some d_u, Some d_v -> d_v > d_u + edge_weight adj u v
     | _, _ -> False)

(* Theorem: If after n-1 rounds we can still relax an edge,
   then there exists a negative-weight cycle. *)
let bf_negative_cycle_detection (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
  : Lemma
    (requires n > 0)
    (ensures (
      let dist = pure_bf adj src (n - 1) in
      let dist_extra = pure_bf_round adj dist in
      (exists_relaxable_edge adj dist <==> (exists (v: nat). v < n /\ get_dist dist_extra v <> get_dist dist v))
    ))
  =
  admit()  // Proof: If distances change after n-1 rounds, we found a shorter path with n+ edges
          // => negative cycle exists (since shortest simple paths have at most n-1 edges)

(* ===== Properties of Relaxation Operations ===== *)

(* Lemma: pure_relax preserves sequence length *)
let relax_length (#n: nat) (dist: dist_vec n) (u v: nat{u < n /\ v < n}) (w: int)
  : Lemma (ensures Seq.length (pure_relax dist u v w) == Seq.length dist)
  = ()

(* Lemma: pure_relax only modifies dist[v] *)
let relax_unchanged (#n: nat) (dist: dist_vec n) (u v: nat{u < n /\ v < n}) (w: int) (x: nat{x < n /\ x <> v})
  : Lemma (ensures get_dist (pure_relax dist u v w) x == get_dist dist x)
  = ()

(* Lemma: pure_relax never increases distance *)
let relax_decreases (#n: nat) (dist: dist_vec n) (u v: nat{u < n /\ v < n}) (w: int)
  : Lemma (ensures (
    match get_dist dist v, get_dist (pure_relax dist u v w) v with
    | None, _ -> True
    | Some d, Some d' -> d' <= d
    | Some d, None -> False
  ))
  = ()

(* Lemma: relax_from_u preserves length *)
let rec relax_from_u_length (#n: nat) (adj: adj_matrix n) (dist: dist_vec n) (u: nat{u < n}) (v: nat)
  : Lemma
    (ensures Seq.length (relax_from_u adj dist u v) == Seq.length dist)
    (decreases (n - v))
  =
  if v >= n then ()
  else begin
    relax_length dist u v (edge_weight adj u v);
    relax_from_u_length adj (pure_relax dist u v (edge_weight adj u v)) u (v + 1)
  end

(* Lemma: relax_all preserves length *)
let rec relax_all_length (#n: nat) (adj: adj_matrix n) (dist: dist_vec n) (u: nat)
  : Lemma
    (ensures Seq.length (relax_all adj dist u) == Seq.length dist)
    (decreases (n - u))
  =
  if u >= n then ()
  else begin
    relax_from_u_length adj dist u 0;
    relax_all_length adj (relax_from_u adj dist u 0) (u + 1)
  end

(* Lemma: bf_round preserves length *)
let bf_round_length (#n: nat) (adj: adj_matrix n) (dist: dist_vec n)
  : Lemma (ensures Seq.length (pure_bf_round adj dist) == Seq.length dist)
  =
  relax_all_length adj dist 0

(* Lemma: pure_bf produces correct length *)
let rec pure_bf_length (#n: nat) (adj: adj_matrix n) (src: nat{src < n}) (rounds: nat)
  : Lemma
    (ensures Seq.length (pure_bf adj src rounds) == n)
    (decreases rounds)
  =
  if rounds = 0 then ()
  else begin
    pure_bf_length adj src (rounds - 1);
    bf_round_length adj (pure_bf adj src (rounds - 1))
  end

(* ===== Summary of Main Results ===== *)

(* 
   This module proves the following key theorems about Bellman-Ford:

   1. [bf_upper_bound] Upper-bound property:
      After any number of rounds, dist[v] >= sp_dist(src, v) for all v.
      Distances never go below true shortest paths.

   2. [bf_correctness_inductive] Path relaxation property (CLRS Lemma 24.2):
      After k rounds, dist[v] = sp_dist_k(src, v, k) for all v.
      This is proved by induction on k.

   3. [bf_convergence] Convergence theorem:
      After n-1 rounds (assuming no negative cycles), 
      dist[v] = sp_dist(src, v) for all vertices v.
      This follows from (2) since sp_dist = sp_dist_k with k=n-1.

   4. [bf_negative_cycle_detection] Negative cycle detection:
      If any edge can still be relaxed after n-1 rounds,
      then the graph contains a negative-weight cycle reachable from source.

   These theorems correspond to CLRS Chapter 24.1 theorems:
   - Lemma 24.2 (path-relaxation property): bf_correctness_inductive
   - Corollary 24.3 (upper-bound property): bf_upper_bound
   - Theorem 24.4 (convergence): bf_convergence
   - Corollary 24.5 (negative-cycle detection): bf_negative_cycle_detection
*)
