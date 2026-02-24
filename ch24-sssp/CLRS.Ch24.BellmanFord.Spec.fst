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

(* No negative cycles reachable from src:
   Adding one more edge (n-th) doesn't improve shortest paths. *)
let no_neg_cycles (#n: nat) (adj: adj_matrix n) (src: nat{src < n}) : prop =
  forall (v: nat). v < n ==> sp_dist_k adj src v n == sp_dist adj src v

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
                     (dist: dist_vec n) : prop =
  forall (v: nat). v < n ==>
    (match get_dist dist v, sp_dist adj src v with
     | None, _ -> True  // dist says unreachable: OK
     | Some d, None -> False  // dist says reachable but no path exists: violation!
     | Some d, Some sp -> d >= sp)  // dist overestimates: OK

(* ===== Correctness Invariant (CLRS Lemma 24.2) ===== *)

(* Path relaxation property: After i rounds, dist[v] is at least as good as
   sp_dist_k(src, v, i) — the shortest path using at most i edges. *)
let correctness_inv (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
                    (dist: dist_vec n) (rounds: nat) : prop =
  forall (v: nat). v < n ==>
    (match sp_dist_k adj src v rounds with
     | None -> True  // no path with <= rounds edges: no constraint
     | Some sp -> (match get_dist dist v with
                   | None -> False  // if k-edge path exists, dist must have found at least as good
                   | Some d -> d <= sp))

(* ===== Helper Lemmas ===== *)

(* Helper: min_over_preds with initial best returns result at least as good as best *)
let rec min_over_preds_improves_best (#n: nat) (adj: adj_matrix n) (src dst: nat{src < n /\ dst < n})
                                      (k: nat{k > 0}) (best: option int) (u: nat) (n_bound: nat{n_bound == n})
  : Lemma
    (ensures (
      let result = min_over_preds adj src dst k best u n_bound in
      match best, result with
      | None, _ -> True
      | Some b, None -> False
      | Some b, Some r -> r <= b
    ))
    (decreases (n - u))
  =
  if u >= n then ()
  else begin
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
    min_over_preds_improves_best adj src dst k new_best (u + 1) n_bound
  end

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
  let prev_dist = sp_dist_k adj src dst k in
  let result = sp_dist_k adj src dst (k + 1) in
  assert (result == min_over_preds adj src dst (k + 1) prev_dist 0 n);
  min_over_preds_improves_best adj src dst (k + 1) prev_dist 0 n

(* ===== Relaxation Monotonicity ===== *)

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

(* Lemma: pure_relax achieves bound when dist[u] is defined *)
let pure_relax_achieves (#n: nat) (dist: dist_vec n) (u v: nat{u < n /\ v < n}) (w: int)
  : Lemma
    (requires w < inf)
    (ensures (
      match get_dist dist u with
      | None -> True
      | Some d_u ->
        match get_dist (pure_relax dist u v w) v with
        | None -> False
        | Some d_v' -> d_v' <= d_u + w))
  = ()

(* Lemma: relax_from_u never increases any distance *)
let rec relax_from_u_monotone (#n: nat) (adj: adj_matrix n) (dist: dist_vec n)
    (u: nat{u < n}) (v_start: nat) (x: nat{x < n})
  : Lemma
    (ensures (
      match get_dist dist x, get_dist (relax_from_u adj dist u v_start) x with
      | None, _ -> True
      | Some d, Some d' -> d' <= d
      | Some _, None -> False))
    (decreases (n - v_start))
  = if v_start >= n then ()
    else begin
      let w = edge_weight adj u v_start in
      let dist' = pure_relax dist u v_start w in
      (if x = v_start then relax_decreases dist u v_start w
       else relax_unchanged dist u v_start w x);
      relax_from_u_monotone adj dist' u (v_start + 1) x
    end

(* Lemma: relax_all never increases any distance *)
let rec relax_all_monotone (#n: nat) (adj: adj_matrix n) (dist: dist_vec n)
    (u_start: nat) (x: nat{x < n})
  : Lemma
    (ensures (
      match get_dist dist x, get_dist (relax_all adj dist u_start) x with
      | None, _ -> True
      | Some d, Some d' -> d' <= d
      | Some _, None -> False))
    (decreases (n - u_start))
  = if u_start >= n then ()
    else begin
      relax_from_u_monotone adj dist u_start 0 x;
      relax_all_monotone adj (relax_from_u adj dist u_start 0) (u_start + 1) x
    end

(* Lemma: relax_from_u doesn't change positions before v_start *)
let rec relax_from_u_unchanged_before (#n: nat) (adj: adj_matrix n) (dist: dist_vec n)
    (u: nat{u < n}) (v_start: nat) (x: nat{x < n /\ x < v_start})
  : Lemma
    (ensures get_dist (relax_from_u adj dist u v_start) x == get_dist dist x)
    (decreases (n - v_start))
  = if v_start >= n then ()
    else begin
      relax_unchanged dist u v_start (edge_weight adj u v_start) x;
      relax_from_u_unchanged_before adj (pure_relax dist u v_start (edge_weight adj u v_start))
        u (v_start + 1) x
    end

(* ===== Edge Achievement: relax_from_u achieves dist[v] <= dist[u] + w ===== *)

(* Helper: relax_from_u starting from v_start achieves the bound for target v *)
let rec relax_from_u_achieves_aux (#n: nat) (adj: adj_matrix n) (dist: dist_vec n)
    (u: nat{u < n}) (v_start: nat) (v: nat{v < n /\ v >= v_start})
  : Lemma
    (ensures (
      let w = edge_weight adj u v in
      match get_dist dist u with
      | None -> True
      | Some d_u ->
        if w >= inf then True
        else
          match get_dist (relax_from_u adj dist u v_start) v with
          | None -> False
          | Some d_v' -> d_v' <= d_u + w))
    (decreases (n - v_start))
  = let w = edge_weight adj u v in
    match get_dist dist u with
    | None -> ()
    | Some d_u ->
      if w >= inf then ()
      else if v_start >= n then () // impossible: v >= v_start >= n but v < n
      else if v_start = v then begin
        // At step v: relax (u, v, w)
        let dist' = pure_relax dist u v w in
        pure_relax_achieves dist u v w;
        // dist'[v] <= d_u + w
        // Remaining steps don't change v (v < v+1)
        if v + 1 <= n then
          relax_from_u_unchanged_before adj dist' u (v + 1) v
        else ()
      end else begin
        // v_start < v: process v_start, then recurse
        let w_vs = edge_weight adj u v_start in
        let dist' = pure_relax dist u v_start w_vs in
        // dist'[u] <= dist[u] = Some d_u
        (if u = v_start then relax_decreases dist u v_start w_vs
         else relax_unchanged dist u v_start w_vs u);
        // Apply IH: relax_from_u on dist' from v_start+1 achieves bound with dist'[u]
        relax_from_u_achieves_aux adj dist' u (v_start + 1) v
        // IH gives result[v] <= dist'[u] + w, and dist'[u] <= d_u
        // So result[v] <= d_u + w
      end

(* Main edge achievement lemma for relax_from_u *)
let relax_from_u_achieves (#n: nat) (adj: adj_matrix n) (dist: dist_vec n)
    (u: nat{u < n}) (v: nat{v < n})
  : Lemma
    (ensures (
      let w = edge_weight adj u v in
      match get_dist dist u with
      | None -> True
      | Some d_u ->
        if w >= inf then True
        else
          match get_dist (relax_from_u adj dist u 0) v with
          | None -> False
          | Some d_v' -> d_v' <= d_u + w))
  = relax_from_u_achieves_aux adj dist u 0 v

(* Edge achievement for relax_all: after one full round, dist[v] <= dist[u] + w for all edges *)
let rec relax_all_achieves_edge (#n: nat) (adj: adj_matrix n) (dist: dist_vec n)
    (u_start: nat) (u_src: nat{u_src < n}) (v: nat{v < n})
  : Lemma
    (requires u_src >= u_start)
    (ensures (
      let w = edge_weight adj u_src v in
      match get_dist dist u_src with
      | None -> True
      | Some d_u ->
        if w >= inf then True
        else
          match get_dist (relax_all adj dist u_start) v with
          | None -> False
          | Some d_v' -> d_v' <= d_u + w))
    (decreases (n - u_start))
  = let w = edge_weight adj u_src v in
    match get_dist dist u_src with
    | None -> ()
    | Some d_u ->
      if w >= inf then ()
      else if u_start >= n then () // impossible: u_src >= u_start >= n but u_src < n
      else if u_start = u_src then begin
        // At u_src: relax_from_u achieves the bound
        let dist' = relax_from_u adj dist u_src 0 in
        relax_from_u_achieves adj dist u_src v;
        // dist'[v] <= d_u + w
        // Remaining relax_all only decreases distances
        relax_all_monotone adj dist' (u_src + 1) v
      end else begin
        // u_start < u_src: process u_start, then recurse
        let dist' = relax_from_u adj dist u_start 0 in
        // dist'[u_src] <= dist[u_src] = Some d_u
        relax_from_u_monotone adj dist u_start 0 u_src;
        // By IH on dist' from u_start+1
        relax_all_achieves_edge adj dist' (u_start + 1) u_src v
      end

(* ===== Correctness Invariant: bounded_by_min_over_preds ===== *)

(* If d_val <= best and d_val <= each candidate, then d_val <= min_over_preds result *)
let rec bounded_by_min_over_preds (#n: nat) (adj: adj_matrix n) (src dst: nat{src < n /\ dst < n})
    (k: nat{k > 0}) (best: option int) (start: nat) (n_bound: nat{n_bound == n})
    (d_val: int)
  : Lemma
    (requires
      (match best with | None -> True | Some b -> d_val <= b) /\
      (forall (u: nat). u < n /\ u >= start ==>
        (match sp_dist_k adj src u (k-1) with
         | None -> True
         | Some d_u ->
           let w = edge_weight adj u dst in
           w >= inf \/ d_val <= d_u + w)))
    (ensures (
      match min_over_preds adj src dst k best start n_bound with
      | None -> True
      | Some r -> d_val <= r))
    (decreases (n - start))
  = if start >= n then ()
    else begin
      let dist_to_u = sp_dist_k adj src start (k - 1) in
      let w_u_dst = edge_weight adj start dst in
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
      // d_val <= new_best follows from d_val <= best and d_val <= candidate
      bounded_by_min_over_preds adj src dst k new_best (start + 1) n_bound d_val
    end

(* ===== Upper Bound: Triangle inequality for sp_dist ===== *)

(* Helper: min_over_preds considers a specific predecessor *)
let rec min_over_preds_considers_u (#n: nat) (adj: adj_matrix n) (src dst: nat{src < n /\ dst < n})
    (k: nat{k > 0}) (best: option int) (start: nat) (n_bound: nat{n_bound == n})
    (u_target: nat{u_target < n})
  : Lemma
    (requires start <= u_target /\
              (match sp_dist_k adj src u_target (k-1) with | None -> False | Some _ -> True) /\
              edge_weight adj u_target dst < inf)
    (ensures (
      match sp_dist_k adj src u_target (k-1) with
      | Some d_u ->
        let w = edge_weight adj u_target dst in
        (match min_over_preds adj src dst k best start n_bound with
         | None -> False
         | Some r -> r <= d_u + w)
      | None -> True))
    (decreases (n - start))
  = if start >= n then () // impossible: u_target < n and start <= u_target
    else if start = u_target then begin
      // At u_target: candidate = Some(d_u + w)
      let dist_to_u = sp_dist_k adj src u_target (k - 1) in
      let w = edge_weight adj u_target dst in
      let candidate = match dist_to_u with
        | Some d_u -> Some (d_u + w)
        | None -> None in
      let new_best = match candidate, best with
        | None, _ -> best
        | Some c, None -> Some c
        | Some c, Some b -> if c < b then Some c else Some b in
      // new_best <= candidate = Some(d_u + w)
      // result = min_over_preds(new_best, start+1) <= new_best <= d_u + w
      min_over_preds_improves_best adj src dst k new_best (start + 1) n_bound
    end else begin
      // start < u_target: recurse
      let dist_to_u = sp_dist_k adj src start (k - 1) in
      let w_u_dst = edge_weight adj start dst in
      let candidate = match dist_to_u with
        | None -> None
        | Some d_u -> if w_u_dst < inf then Some (d_u + w_u_dst) else None in
      let new_best = match candidate, best with
        | None, _ -> best
        | Some c, None -> Some c
        | Some c, Some b -> if c < b then Some c else Some b in
      min_over_preds_considers_u adj src dst k new_best (start + 1) n_bound u_target
    end

(* Triangle inequality for sp_dist under no_neg_cycles *)
let sp_dist_triangle (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
    (u v: nat{u < n /\ v < n})
  : Lemma
    (requires no_neg_cycles adj src /\ edge_weight adj u v < inf)
    (ensures (
      match sp_dist adj src u with
      | None -> True
      | Some sp_u ->
        match sp_dist adj src v with
        | None -> False
        | Some sp_v -> sp_v <= sp_u + edge_weight adj u v))
  = match sp_dist adj src u with
    | None -> ()
    | Some sp_u ->
      // sp_dist(src,u) = sp_dist_k(src,u,n-1) = Some sp_u
      // sp_dist_k(src,v,n) considers predecessor u:
      //   candidate = sp_dist_k(src,u,n-1) + w(u,v) = sp_u + w
      // So sp_dist_k(src,v,n) <= sp_u + w
      let w = edge_weight adj u v in
      // sp_dist_k(src,v,n) = min_over_preds(adj, src, v, n, sp_dist_k(src,v,n-1), 0, n)
      min_over_preds_considers_u adj src v n (sp_dist_k adj src v (n-1)) 0 n u;
      // Now sp_dist_k(src,v,n) = Some r with r <= sp_u + w
      // By no_neg_cycles: sp_dist_k(src,v,n) = sp_dist(src,v)
      ()

(* Lemma: Relaxing an edge preserves upper bound (under no_neg_cycles) *)
let relax_preserves_upper_bound (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
                                  (dist: dist_vec n) (u v: nat{u < n /\ v < n})
                                  (w: int)
  : Lemma
    (requires upper_bound_inv adj src dist /\ no_neg_cycles adj src /\ w == edge_weight adj u v)
    (ensures upper_bound_inv adj src (pure_relax dist u v w))
  =
  let dist' = pure_relax dist u v w in
  let aux (x: nat{x < n})
    : Lemma (match get_dist dist' x, sp_dist adj src x with
             | None, _ -> True
             | Some d, None -> False
             | Some d, Some sp -> d >= sp)
    =
    if x <> v then
      relax_unchanged dist u v w x
    else begin
      // x = v: need to show dist'[v] >= sp_dist(src, v)
      relax_decreases dist u v w;
      match get_dist dist u with
      | None -> () // dist' = dist
      | Some val_u ->
        if w >= inf then () // dist' = dist
        else begin
          let new_val = val_u + w in
          match get_dist dist v with
          | Some val_v ->
            if new_val < val_v then begin
              // dist'[v] = Some new_val
              // By upper_bound_inv on u: sp_dist(src,u) = Some sp_u and val_u >= sp_u
              // By triangle: sp_dist(src,v) <= sp_u + w <= val_u + w = new_val
              sp_dist_triangle adj src u v
            end else () // dist' = dist
          | None ->
            // dist'[v] = Some new_val, was None before
            // By upper_bound_inv on u: sp_dist(src,u) = Some sp_u with val_u >= sp_u
            // By triangle: sp_dist(src,v) = Some sp_v with sp_v <= sp_u + w <= new_val
            sp_dist_triangle adj src u v
        end
    end
  in
  FStar.Classical.forall_intro aux

(* Lemma: Relaxing from vertex u preserves upper bound *)
let rec relax_from_u_preserves_upper (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
                                       (dist: dist_vec n) (u: nat{u < n}) (v: nat)
  : Lemma
    (requires upper_bound_inv adj src dist /\ no_neg_cycles adj src)
    (ensures upper_bound_inv adj src (relax_from_u adj dist u v))
    (decreases (n - v))
  =
  if v >= n then ()
  else begin
    let w = edge_weight adj u v in
    relax_preserves_upper_bound adj src dist u v w;
    relax_from_u_preserves_upper adj src (pure_relax dist u v w) u (v + 1)
  end

(* Lemma: Relaxing all edges preserves upper bound *)
let rec relax_all_preserves_upper (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
                                    (dist: dist_vec n) (u: nat)
  : Lemma
    (requires upper_bound_inv adj src dist /\ no_neg_cycles adj src)
    (ensures upper_bound_inv adj src (relax_all adj dist u))
    (decreases (n - u))
  =
  if u >= n then ()
  else begin
    relax_from_u_preserves_upper adj src dist u 0;
    relax_all_preserves_upper adj src (relax_from_u adj dist u 0) (u + 1)
  end

(* Lemma: One round preserves upper bound *)
let bf_round_preserves_upper (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
                              (dist: dist_vec n)
  : Lemma
    (requires upper_bound_inv adj src dist /\ no_neg_cycles adj src)
    (ensures upper_bound_inv adj src (pure_bf_round adj dist))
  =
  relax_all_preserves_upper adj src dist 0

(* ===== Main Correctness Theorems ===== *)

(* Theorem: Initialization satisfies correctness for 0 rounds *)
let init_correct (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
  : Lemma (ensures correctness_inv adj src (init_dist n src) 0)
  =
  let aux (v: nat{v < n})
    : Lemma (match sp_dist_k adj src v 0 with
             | None -> True
             | Some sp -> (match get_dist (init_dist n src) v with
                           | None -> False
                           | Some d -> d <= sp))
    =
    // sp_dist_k(src, v, 0) = if src = v then Some 0 else None
    // init_dist: dist[src] = Some 0, dist[v] = None for v <> src
    ()
  in
  FStar.Classical.forall_intro aux

(* Theorem: Initialization satisfies upper bound (under no_neg_cycles) *)
let init_upper_bound (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
  : Lemma
    (requires no_neg_cycles adj src)
    (ensures upper_bound_inv adj src (init_dist n src))
  =
  let aux (v: nat{v < n})
    : Lemma (match get_dist (init_dist n src) v, sp_dist adj src v with
             | None, _ -> True
             | Some d, None -> False
             | Some d, Some sp -> d >= sp)
    =
    // Only init_dist[src] = Some 0, rest are None
    if v = src then begin
      // sp_dist(src, src) = sp_dist_k(src, src, n-1)
      // sp_dist_k(src, src, 0) = Some 0
      // By monotonicity: sp_dist_k(src, src, n-1) <= 0
      let rec aux_mono (k: nat)
        : Lemma
          (ensures (match sp_dist_k adj src src k with
                    | None -> False
                    | Some d -> d <= 0))
          (decreases k)
        = if k = 0 then ()
          else begin
            aux_mono (k - 1);
            sp_dist_k_monotone adj src src (k - 1)
          end
      in
      if n > 0 then aux_mono (n - 1)
      else ()
    end else ()
  in
  FStar.Classical.forall_intro aux

(* Theorem: Upper bound property holds after any number of rounds (under no_neg_cycles) *)
let rec bf_upper_bound (#n: nat) (adj: adj_matrix n) (src: nat{src < n}) (rounds: nat)
  : Lemma
    (requires no_neg_cycles adj src)
    (ensures upper_bound_inv adj src (pure_bf adj src rounds))
    (decreases rounds)
  =
  if rounds = 0 then
    init_upper_bound adj src
  else begin
    bf_upper_bound adj src (rounds - 1);
    bf_round_preserves_upper adj src (pure_bf adj src (rounds - 1))
  end

(* ===== Path Relaxation Property (CLRS Lemma 24.2) ===== *)

(* Lemma: After k rounds, dist[v] <= sp_dist_k(src, v, k) for all v *)
let rec bf_correctness_inductive (#n: nat) (adj: adj_matrix n) (src: nat{src < n}) (rounds: nat)
  : Lemma
    (ensures correctness_inv adj src (pure_bf adj src rounds) rounds)
    (decreases rounds)
  =
  if rounds = 0 then
    init_correct adj src
  else begin
    bf_correctness_inductive adj src (rounds - 1);
    let dist_prev = pure_bf adj src (rounds - 1) in
    let dist_curr = pure_bf adj src rounds in
    // dist_curr = pure_bf_round adj dist_prev = relax_all adj dist_prev 0

    let aux (v: nat{v < n})
      : Lemma (match sp_dist_k adj src v rounds with
               | None -> True
               | Some sp -> (match get_dist dist_curr v with
                             | None -> False
                             | Some d -> d <= sp))
      =
      match sp_dist_k adj src v rounds with
      | None -> ()
      | Some sp ->
        // sp = min_over_preds(adj, src, v, rounds, sp_dist_k(src,v,rounds-1), 0, n)
        // We need to show: dist_curr[v] = Some d with d <= sp

        // Step 1: If sp_dist_k(src,v,rounds-1) is Some sp_prev,
        //   then by IH dist_prev[v] = Some d0 with d0 <= sp_prev.
        //   By monotonicity dist_curr[v] <= dist_prev[v], so dist_curr[v] = Some d with d <= sp_prev.
        // Step 2: For each u with sp_dist_k(src,u,rounds-1) = Some sp_u and edge (u,v,w):
        //   by IH dist_prev[u] = Some d_u with d_u <= sp_u.
        //   by relax_all_achieves_edge: dist_curr[v] = Some d with d <= d_u + w <= sp_u + w.
        // Step 3: sp = min over all these candidates, dist_curr[v] <= each, so <= sp.

        // First establish that dist_curr[v] is Some by showing at least one bound gives it
        // We know sp_dist_k(src,v,rounds) = Some sp, so by sp_dist_k definition
        // either sp_dist_k(src,v,rounds-1) = Some sp_prev (with sp <= sp_prev)
        // or some predecessor gives a candidate.
        // In either case, dist_curr[v] is Some.

        // Use relax_all_monotone to get dist_curr[v] <= dist_prev[v]
        relax_all_monotone adj dist_prev 0 v;

        // Check if sp_dist_k(src,v,rounds-1) gives a bound
        (match sp_dist_k adj src v (rounds - 1) with
         | Some sp_prev ->
           // By IH: dist_prev[v] = Some d0 with d0 <= sp_prev
           // By monotonicity: dist_curr[v] <= dist_prev[v]
           // So dist_curr[v] = Some d with d <= sp_prev
           // Now dist_curr[v] is Some d for some d.
           // Use bounded_by_min_over_preds to show d <= sp
           let d = (match get_dist dist_curr v with | Some d -> d) in
           // Show d <= sp_dist_k(src,v,rounds-1)
           // And d <= sp_dist_k(src,u,rounds-1) + w for each u with edge
           let edge_bound (u: nat{u < n /\ u >= 0})
             : Lemma (match sp_dist_k adj src u (rounds-1) with
                      | None -> True
                      | Some d_u ->
                        let w = edge_weight adj u v in
                        w >= inf \/ d <= d_u + w)
             =
             match sp_dist_k adj src u (rounds-1) with
             | None -> ()
             | Some sp_u ->
               let w = edge_weight adj u v in
               if w >= inf then ()
               else begin
                 // By IH: dist_prev[u] = Some d_u with d_u <= sp_u
                 // By relax_all_achieves_edge: dist_curr[v] <= d_u + w <= sp_u + w
                 relax_all_achieves_edge adj dist_prev 0 u v
               end
           in
           FStar.Classical.forall_intro edge_bound;
           bounded_by_min_over_preds adj src v rounds (sp_dist_k adj src v (rounds-1)) 0 n d
         | None ->
           // sp_dist_k(src,v,rounds-1) = None but sp_dist_k(src,v,rounds) = Some sp
           // This means sp comes from some predecessor candidate
           // sp = min_over_preds with best = None
           // Some predecessor u has sp_dist_k(src,u,rounds-1) = Some sp_u and edge (u,v,w)
           // By IH: dist_prev[u] = Some d_u <= sp_u
           // By relax_all_achieves_edge: dist_curr[v] = Some d <= d_u + w
           // Now show d <= sp using bounded_by_min_over_preds

           // First need to show dist_curr[v] is Some.
           // sp = min_over_preds(None, 0, n) = Some sp means some candidate was Some.
           // That means some u has sp_dist_k(src,u,rounds-1) = Some sp_u and edge w < inf.
           // By IH: dist_prev[u] = Some d_u. By relax_all_achieves_edge: dist_curr[v] is Some.

           // We need a witness u for which sp_dist_k(src,u,rounds-1) is Some and edge exists.
           // But we can't extract this witness from the min_over_preds computation directly.
           // Instead, use a helper: if min_over_preds(None, 0, n) = Some sp, then
           // there exists u such that the candidate from u is Some c with c >= sp.
           // This is implied by the structure of min_over_preds.

           // Alternative approach: prove by induction on min_over_preds that
           // if the result is Some, then dist_curr[v] is Some and bounded.

           // For now, let's use a specialized helper for this case.
           // We know sp_dist_k(src,v,rounds) = Some sp and sp_dist_k(src,v,rounds-1) = None.
           // sp_dist_k(src,v,rounds) = min_over_preds(adj, src, v, rounds, None, 0, n)
           // Since result = Some sp and initial best = None, some candidate was Some c <= sp.
           // For that u: by IH dist_prev[u] is Some, by relax_all_achieves_edge dist_curr[v] is Some.

           // The proof is the same bounded_by_min_over_preds approach, just with best = None.
           // We need dist_curr[v] to be Some d for some d. We show this by constructing it.

           // Use the fact that at least one relax_all_achieves_edge gives Some result
           // Since sp_dist_k(src,v,rounds) = Some sp, by the min_over_preds structure,
           // there exists a u* with valid candidate. We iterate to find one such u*.

           // Pragmatic approach: use a recursion to find a witness and establish dist_curr[v] is Some
           let rec find_witness_and_bound (u_iter: nat)
             : Lemma
               (requires u_iter <= n /\
                 (match min_over_preds adj src v rounds None u_iter n with
                  | Some _ -> True | None -> False))
               (ensures (match get_dist dist_curr v with
                         | None -> False
                         | Some d -> True))
               (decreases (n - u_iter))
             = if u_iter >= n then ()
               else begin
                 let dist_to_u = sp_dist_k adj src u_iter (rounds - 1) in
                 let w_u_v = edge_weight adj u_iter v in
                 let candidate = match dist_to_u with
                   | None -> None
                   | Some d_u -> if w_u_v < inf then Some (d_u + w_u_v) else None in
                 let new_best = match candidate, (None <: option int) with
                   | None, _ -> None
                   | Some c, None -> Some c
                   | Some c, Some b -> if c < b then Some c else Some b in
                 match candidate with
                 | Some _ ->
                   // Found a predecessor with valid candidate
                   // dist_prev[u_iter] is Some (by IH on correctness_inv)
                   // relax_all_achieves_edge ensures dist_curr[v] is Some
                   relax_all_achieves_edge adj dist_prev 0 u_iter v
                 | None ->
                   // No candidate from this u, continue
                   find_witness_and_bound (u_iter + 1)
               end
           in
           // sp_dist_k(src,v,rounds) = min_over_preds(None, 0, n) = Some sp
           // So min_over_preds with best=None from 0 gives Some
           find_witness_and_bound 0;
           // Now dist_curr[v] = Some d
           let d = (match get_dist dist_curr v with | Some d -> d) in
           let edge_bound (u: nat{u < n /\ u >= 0})
             : Lemma (match sp_dist_k adj src u (rounds-1) with
                      | None -> True
                      | Some d_u ->
                        let w = edge_weight adj u v in
                        w >= inf \/ d <= d_u + w)
             =
             match sp_dist_k adj src u (rounds-1) with
             | None -> ()
             | Some sp_u ->
               let w = edge_weight adj u v in
               if w >= inf then ()
               else relax_all_achieves_edge adj dist_prev 0 u v
           in
           FStar.Classical.forall_intro edge_bound;
           bounded_by_min_over_preds adj src v rounds (None #int) 0 n d)
    in
    FStar.Classical.forall_intro aux
  end

(* ===== Convergence Theorem ===== *)

//SNIPPET_START: bf_convergence
(* Theorem: After n-1 rounds (no negative cycles), dist[v] = sp_dist(src, v) for all v *)
let bf_convergence (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
  : Lemma
    (requires n > 0 /\ no_neg_cycles adj src)
    (ensures (
      let dist = pure_bf adj src (n - 1) in
      forall (v: nat). v < n ==>
        get_dist dist v == sp_dist adj src v
    ))
  =
  bf_correctness_inductive adj src (n - 1);
  bf_upper_bound adj src (n - 1);
  // correctness_inv gives: sp_dist(src,v) = Some sp -> dist[v] = Some d with d <= sp
  // upper_bound_inv gives: dist[v] = Some d -> sp_dist(src,v) = Some sp with d >= sp
  // Combined: dist[v] = sp_dist(src,v) for all v
  let dist = pure_bf adj src (n - 1) in
  let aux (v: nat{v < n})
    : Lemma (get_dist dist v == sp_dist adj src v)
    =
    match get_dist dist v, sp_dist adj src v with
    | None, None -> ()
    | Some d, Some sp -> ()  // d <= sp and d >= sp, so d = sp
    | Some _, None -> ()     // contradicts upper_bound_inv
    | None, Some _ -> ()     // contradicts correctness_inv (sp_dist = sp_dist_k(n-1))
  in
  FStar.Classical.forall_intro aux
//SNIPPET_END: bf_convergence

(* ===== Negative Cycle Detection ===== *)

(* Predicate: At least one edge can still be relaxed.
   An edge (u,v) is relaxable if dist[u] is reachable and either:
   - dist[v] is unreachable (None), or
   - dist[v] > dist[u] + w *)
let exists_relaxable_edge (#n: nat) (adj: adj_matrix n) (dist: dist_vec n) : prop =
  exists (u v: nat). u < n /\ v < n /\ edge_weight adj u v < inf /\
    (match get_dist dist u with
     | None -> False
     | Some d_u ->
       match get_dist dist v with
       | None -> True  // u reachable but v not: can relax
       | Some d_v -> d_v > d_u + edge_weight adj u v)

(* Helper: If no relaxable edge, pure_relax is a no-op *)
let no_relaxable_relax_noop (#n: nat) (adj: adj_matrix n) (dist: dist_vec n)
    (u v: nat{u < n /\ v < n}) (w: int)
  : Lemma
    (requires ~(exists_relaxable_edge adj dist) /\ w == edge_weight adj u v)
    (ensures Seq.equal (pure_relax dist u v w) dist)
  =
  // ~exists_relaxable_edge means for all (u,v) with w < inf:
  // NOT (d_u is Some AND (d_v is None OR d_v > d_u + w))
  // i.e., d_u is None OR (d_v is Some AND d_v <= d_u + w)
  ()

(* Helper: If no relaxable edge, relax_from_u is identity *)
let rec no_relaxable_from_u_noop (#n: nat) (adj: adj_matrix n) (dist: dist_vec n)
    (u: nat{u < n}) (v_start: nat)
  : Lemma
    (requires ~(exists_relaxable_edge adj dist))
    (ensures Seq.equal (relax_from_u adj dist u v_start) dist)
    (decreases (n - v_start))
  =
  if v_start >= n then ()
  else begin
    no_relaxable_relax_noop adj dist u v_start (edge_weight adj u v_start);
    no_relaxable_from_u_noop adj dist u (v_start + 1)
  end

(* Helper: If no relaxable edge, relax_all is identity *)
let rec no_relaxable_relax_all_noop (#n: nat) (adj: adj_matrix n) (dist: dist_vec n)
    (u_start: nat)
  : Lemma
    (requires ~(exists_relaxable_edge adj dist))
    (ensures Seq.equal (relax_all adj dist u_start) dist)
    (decreases (n - u_start))
  =
  if u_start >= n then ()
  else begin
    no_relaxable_from_u_noop adj dist u_start 0;
    no_relaxable_relax_all_noop adj dist (u_start + 1)
  end

(* Theorem: exists_relaxable_edge <==> extra round changes distances *)
let bf_negative_cycle_detection (#n: nat) (adj: adj_matrix n) (src: nat{src < n})
  : Lemma
    (requires n > 0)
    (ensures (
      let dist = pure_bf adj src (n - 1) in
      let dist_extra = pure_bf_round adj dist in
      (exists_relaxable_edge adj dist <==> (exists (v: nat). v < n /\ get_dist dist_extra v <> get_dist dist v))
    ))
  =
  let dist = pure_bf adj src (n - 1) in
  let dist_extra = pure_bf_round adj dist in

  // Direction (==>): relaxable edge implies distances change
  let fwd ()
    : Lemma (requires exists_relaxable_edge adj dist)
            (ensures exists (v: nat). v < n /\ get_dist dist_extra v <> get_dist dist v)
    =
    // exists_relaxable_edge gives u, v with the relaxation condition
    // relax_all_achieves_edge shows dist_extra[v] ≤ d_u + w
    // Since d_v > d_u + w (or d_v = None), dist_extra[v] ≠ dist[v]
    FStar.Classical.exists_elim
      (exists (v: nat). v < n /\ get_dist dist_extra v <> get_dist dist v)
      (FStar.Squash.get_proof (exists_relaxable_edge adj dist))
      (fun u -> FStar.Classical.exists_elim
        (exists (v: nat). v < n /\ get_dist dist_extra v <> get_dist dist v)
        (FStar.Squash.get_proof (exists (v': nat). v' < n /\ edge_weight adj u v' < inf /\
          (match get_dist dist u with
           | None -> False
           | Some d_u ->
             match get_dist dist v' with
             | None -> True
             | Some d_v -> d_v > d_u + edge_weight adj u v')))
        (fun v ->
          relax_all_achieves_edge adj dist 0 u v;
          ()))
  in

  // Direction (<==): distances change implies relaxable edge (contrapositive)
  let bwd ()
    : Lemma (requires ~(exists_relaxable_edge adj dist))
            (ensures ~(exists (v: nat). v < n /\ get_dist dist_extra v <> get_dist dist v))
    =
    no_relaxable_relax_all_noop adj dist 0;
    // dist_extra = dist
    assert (Seq.equal dist_extra dist)
  in

  FStar.Classical.move_requires fwd ();
  FStar.Classical.move_requires bwd ()

(* ===== Properties of Relaxation Operations (Length preservation) ===== *)

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

   1. [bf_upper_bound] Upper-bound property (requires no_neg_cycles):
      After any number of rounds, dist[v] >= sp_dist(src, v) for all reachable v.
      Distances never go below true shortest paths.

   2. [bf_correctness_inductive] Path relaxation property (CLRS Lemma 24.2):
      After k rounds, dist[v] <= sp_dist_k(src, v, k) for all v.
      Sequential relaxation is at least as good as k-edge shortest paths.

   3. [bf_convergence] Convergence theorem (requires no_neg_cycles):
      After n-1 rounds, dist[v] = sp_dist(src, v) for all vertices v.
      Combines upper and lower bounds.

   4. [bf_negative_cycle_detection] Negative cycle detection:
      exists_relaxable_edge <==> extra round changes some distance.

   These theorems correspond to CLRS Chapter 24.1 theorems:
   - Lemma 24.2 (path-relaxation property): bf_correctness_inductive
   - Corollary 24.3 (upper-bound property): bf_upper_bound
   - Theorem 24.4 (convergence): bf_convergence
   - Corollary 24.5 (negative-cycle detection): bf_negative_cycle_detection
*)
