module CLRS.Ch24.Dijkstra.TriangleInequality

module Seq = FStar.Seq

(*
 * Proof that triangle inequality is a CONSEQUENCE of the relaxation process
 * in Dijkstra's algorithm.
 * 
 * Key insight from CLRS Chapter 24:
 * Dijkstra's algorithm processes vertices in order of increasing distance from the source.
 * When a vertex u is processed (removed from the priority queue), the algorithm relaxes
 * all edges (u,v) emanating from u. This relaxation ensures:
 *   dist[v] <= dist[u] + w(u,v)
 * 
 * After ALL vertices are processed, this property holds for ALL edges in the graph,
 * which is precisely the triangle inequality.
 * 
 * This means:
 * 1. The triangle inequality is NOT a separate verification requirement
 * 2. It follows automatically from the relaxation steps
 * 3. Any separate verification pass is redundant for proving triangle inequality —
 *    it only confirms what must already be true!
 * 
 * This file proves that the triangle inequality holds after Dijkstra completes,
 * allowing us to remove the separate verification pass.
 *)

let is_processed (p: processed_set) (u: nat) : bool = p u

(* Add a vertex to the processed set *)
let add_to_processed (p: processed_set) (u: nat) : processed_set =
  fun v -> p v || v = u

(* ===== Key Property: Relaxation Establishes Triangle Inequality ===== *)

(* Relax a single edge (u,v): update dist[v] to min(dist[v], dist[u] + w(u,v)) *)
let relax_edge (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) 
               (u v: nat{u < n /\ v < n}) : dist_vec n =
  let d_u = Seq.index dist u in
  let d_v = Seq.index dist v in
  let w = Seq.index weights (u * n + v) in
  if w < inf && d_u < inf && d_u + w < d_v
  then Seq.upd dist v (d_u + w)
  else dist

(* Core lemma: After relaxing edge (u,v), the triangle inequality holds for that edge *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let relax_edge_establishes_triangle (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                    (u v: nat{u < n /\ v < n})
  : Lemma
    (requires u <> v)
    (ensures (
      let dist' = relax_edge dist weights u v in
      let d_u' = Seq.index dist' u in
      let d_v' = Seq.index dist' v in
      let w = Seq.index weights (u * n + v) in
      (w < inf /\ d_u' < inf) ==> d_v' <= d_u' + w))
  =
  // When u <> v: dist'[u] = dist[u] (unchanged), dist'[v] = min(dist[v], dist[u]+w)
  // If relaxed: d_v' = d_u + w = d_u' + w. QED.
  // If not relaxed: d_v' = d_v <= d_u + w = d_u' + w (or antecedent is false). QED.
  ()
#pop-options

(* Relax all edges from u to all other vertices *)
let rec relax_from_u (#n: nat) (dist: dist_vec n) (weights: weight_matrix n) 
                     (u: nat{u < n}) (v: nat)
  : Tot (dist_vec n) (decreases (n - v))
  =
  if v >= n then dist
  else relax_from_u (relax_edge dist weights u v) weights u (v + 1)

(* Key structural lemma: relax_from_u starting at v_start preserves dist[j] for j < v_start and j <> u *)
(* Actually, relax_edge only modifies dist[v], never dist[u] when non-negative weights *)
(* So relax_from_u from v_start only modifies dist[v_start], dist[v_start+1], ..., dist[n-1] *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 15"
let rec relax_from_u_preserves_index (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                      (u: nat{u < n}) (v_start: nat) (j: nat{j < n})
  : Lemma
    (requires j < v_start \/ j = u)
    (ensures 
      all_weights_non_negative weights ==>
      Seq.index (relax_from_u dist weights u v_start) j == Seq.index dist j)
    (decreases (n - v_start))
  =
  if v_start >= n then ()
  else begin
    let dist1 = relax_edge dist weights u v_start in
    // relax_edge only modifies dist[v_start]
    // If j < v_start: j <> v_start, so dist1[j] = dist[j]
    // If j = u: need to check if u = v_start. If so, self-loop with non-neg weights means no change.
    //           If u <> v_start, then j = u <> v_start, so dist1[j] = dist[j].
    // In either case, dist1[j] = dist[j]
    // Then by IH: relax_from_u dist1 ... [j] = dist1[j] = dist[j]
    relax_from_u_preserves_index dist1 weights u (v_start + 1) j
  end
#pop-options

(* Self-loop relaxation with non-negative weights doesn't change dist[u] *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let relax_self_loop_noop (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                         (u: nat{u < n})
  : Lemma
    (requires all_weights_non_negative weights)
    (ensures relax_edge dist weights u u == dist)
  =
  let d_u = Seq.index dist u in
  let w = Seq.index weights (u * n + u) in
  // w >= 0 (non-negative weights), so d_u + w >= d_u
  // Therefore d_u + w < d_u is false, so relax_edge returns dist unchanged
  assert (w >= 0);
  if w < inf && d_u < inf && d_u + w < d_u then () // impossible branch
  else ()
#pop-options

(* After relaxing u->v, triangle inequality for edge u->v' (already satisfied) is preserved
   because dist[u] is NOT modified by relax_edge (it only modifies dist[v]) *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 15"
let relax_edge_preserves_triangle_from_u (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                          (u: nat{u < n}) (v v': nat{v < n /\ v' < n})
  : Lemma
    (requires
      edge_satisfies_triangle dist weights u v' /\
      u <> v /\ u <> v')  // u is neither the target of relaxation nor v'
    (ensures
      edge_satisfies_triangle (relax_edge dist weights u v) weights u v')
  =
  // relax_edge only modifies dist[v]
  // Since u <> v: dist'[u] = dist[u]
  // Since v' <> v: dist'[v'] = dist[v']  (if v = v', this doesn't apply, but u <> v' handles that)
  // Actually we need v <> v' OR the change makes dist[v'] smaller
  // Wait: if v = v', dist'[v'] could change. Let's think again.
  // edge_satisfies_triangle dist weights u v' means:
  //   (w(u,v') < inf /\ d_u < inf) ==> d_v' <= d_u + w(u,v')
  // After relaxing u->v: dist'[u] = dist[u] (since u <> v)
  // If v <> v': dist'[v'] = dist[v'], so same inequality holds
  // If v = v': dist'[v'] <= dist[v'] (relaxation only decreases), so still <= d_u + w
  ()
#pop-options

(* Lemma: After relaxing all edges from u, triangle inequality holds for all edges from u *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let rec relax_from_u_establishes_triangle_from_u (#n: nat) (dist: dist_vec n) 
                                                  (weights: weight_matrix n)
                                                  (u: nat{u < n}) (v_start: nat)
  : Lemma 
    (requires all_weights_non_negative weights)
    (ensures (
      let dist' = relax_from_u dist weights u v_start in
      forall (v: nat). v_start <= v /\ v < n /\ u <> v ==> 
        edge_satisfies_triangle dist' weights u v))
    (decreases (n - v_start))
  =
  if v_start >= n then ()
  else if u = v_start then begin
    // Self-loop: relax_edge dist weights u u == dist (non-negative weights)
    relax_self_loop_noop dist weights u;
    assert (relax_edge dist weights u u == dist);
    // So relax_from_u dist weights u v_start = relax_from_u dist weights u (v_start+1)
    relax_from_u_establishes_triangle_from_u dist weights u (v_start + 1)
  end else begin
    // u <> v_start
    let dist1 = relax_edge dist weights u v_start in
    // After relaxing u->v_start: triangle inequality holds for u->v_start
    relax_edge_establishes_triangle dist weights u v_start;
    // Recursively establish for v_start+1, ..., n-1  
    relax_from_u_establishes_triangle_from_u dist1 weights u (v_start + 1);
    // Need to show: earlier edge u->v_start is preserved through later relaxations
    // IH gives us: forall v. v_start+1 <= v < n /\ u <> v ==> edge_satisfies_triangle dist' u v
    // We need: edge_satisfies_triangle dist' u v_start (where dist' = relax_from_u dist1 ...)
    // dist'[u] = dist1[u] because u = u (j = u case of preserves_index)
    relax_from_u_preserves_index dist1 weights u (v_start + 1) u;
    // dist'[v_start] = dist1[v_start] because v_start < v_start + 1
    relax_from_u_preserves_index dist1 weights u (v_start + 1) v_start;
    // So edge_satisfies_triangle dist1 u v_start ==> edge_satisfies_triangle dist' u v_start
    assert (Seq.index (relax_from_u dist1 weights u (v_start + 1)) u == Seq.index dist1 u);
    assert (Seq.index (relax_from_u dist1 weights u (v_start + 1)) v_start == Seq.index dist1 v_start)
  end
#pop-options

(* Corollary: After relaxing all edges from u (starting at 0), all edges from u satisfy triangle inequality *)
let relax_from_u_establishes_all_from_u (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                        (u: nat{u < n})
  : Lemma
    (requires all_weights_non_negative weights)
    (ensures (
      let dist' = relax_from_u dist weights u 0 in
      forall (v: nat). v < n /\ u <> v ==> edge_satisfies_triangle dist' weights u v))
  =
  relax_from_u_establishes_triangle_from_u dist weights u 0

(* ===== Partial Triangle Inequality ===== *)

(* Triangle inequality holds for edges from processed vertices *)
let triangle_inequality_from_processed (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                       (processed: processed_set) : prop =
  forall (u v: nat). u < n /\ v < n /\ is_processed processed u ==>
    edge_satisfies_triangle dist weights u v

(* ===== Preservation Lemmas ===== *)

(* Key insight: Relaxation preserves triangle inequality for already-processed vertices *)
(* When we relax edges from a new vertex u, we only make distances smaller.
   If an edge (x,v) already satisfied d_v <= d_x + w(x,v), and we make d_v smaller,
   the inequality still holds (or becomes even more satisfied). *)

(* Stability precondition: Relaxation from u doesn't reduce distances of processed vertices *)
(* This captures the Dijkstra invariant: processed vertices have optimal distances *)
let relaxation_stable_for_processed (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                    (u: nat{u < n}) (processed: processed_set) : prop =
  forall (x: nat). x < n /\ is_processed processed x ==>
    (let d_u = Seq.index dist u in
     let d_x = Seq.index dist x in
     let w = Seq.index weights (u * n + x) in
     not (w < inf && d_u < inf && d_u + w < d_x))

(* If stability holds, relax_edge from u to a processed vertex x doesn't change dist[x] *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let relax_edge_stable_for_processed (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                    (u: nat{u < n}) (x: nat{x < n})
                                    (processed: processed_set)
  : Lemma
    (requires
      is_processed processed x /\
      relaxation_stable_for_processed dist weights u processed)
    (ensures
      Seq.index (relax_edge dist weights u x) x == Seq.index dist x)
  =
  let d_u = Seq.index dist u in
  let d_x = Seq.index dist x in
  let w = Seq.index weights (u * n + x) in
  // By stability precondition: not (w < inf && d_u < inf && d_u + w < d_x)
  // Therefore relax_edge returns dist unchanged at position x
  ()
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 15"
let relax_edge_preserves_triangle_others (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                          (u v: nat{u < n /\ v < n})
                                          (x y: nat{x < n /\ y < n})
  : Lemma
    (requires 
      edge_satisfies_triangle dist weights x y /\
      all_weights_non_negative weights /\
      x <> v)  // Key: we only preserve triangle inequality for edges NOT starting from v
    (ensures
      edge_satisfies_triangle (relax_edge dist weights u v) weights x y)
  =
  // When x <> v, dist'[x] = dist[x] (relax_edge only modifies dist[v])
  // And dist'[y] <= dist[y] (either unchanged if y <> v, or relaxed if y = v)
  // 
  // Precondition: (w_xy < inf /\ d_x < inf) ==> d_y <= d_x + w_xy
  // Need: (w_xy < inf /\ d_x' < inf) ==> d_y' <= d_x' + w_xy
  //
  // Since x <> v: d_x' = d_x
  // Since d_y' <= d_y, the implication follows
  ()
#pop-options

(* Helper: Stability is preserved after relax_edge *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 15"
let relax_edge_preserves_stability (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                    (u v: nat{u < n /\ v < n})
                                    (processed: processed_set)
  : Lemma
    (requires
      all_weights_non_negative weights /\
      not (is_processed processed u) /\
      relaxation_stable_for_processed dist weights u processed)
    (ensures
      relaxation_stable_for_processed (relax_edge dist weights u v) weights u processed)
  =
  let dist1 = relax_edge dist weights u v in
  
  // For processed x: if x = v, then dist1[x] = dist[x] by stability
  //                  if x <> v, then dist1[x] = dist[x] by definition of relax_edge
  // In either case, dist1[x] = dist[x] for processed x
  // Also dist1[u] = dist[u] (since u is not processed, u <> any processed vertex including v)
  
  // Therefore: for processed x, not (w(u,x) < inf && dist1[u] < inf && dist1[u] + w(u,x) < dist1[x])
  //            iff not (w(u,x) < inf && dist[u] < inf && dist[u] + w(u,x) < dist[x])
  //            which holds by precondition
  
  if is_processed processed v then
    relax_edge_stable_for_processed dist weights u v processed;
  ()
#pop-options

(* Helper: Single relax_edge step preserves triangle inequality for processed vertices *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
let relax_edge_preserves_triangle_from_processed (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                                 (u v: nat{u < n /\ v < n})
                                                 (processed: processed_set)
  : Lemma
    (requires
      triangle_inequality_from_processed dist weights processed /\
      all_weights_non_negative weights /\
      not (is_processed processed u) /\
      relaxation_stable_for_processed dist weights u processed)
    (ensures
      triangle_inequality_from_processed (relax_edge dist weights u v) weights processed)
  =
  let dist1 = relax_edge dist weights u v in
  
  // For processed x = v: stability ensures dist1[x] = dist[x]
  if is_processed processed v then
    relax_edge_stable_for_processed dist weights u v processed;
  
  // Establish triangle inequality for all edges (x, y) where x is processed
  let lemma_aux (x: nat{x < n}) (y: nat{y < n}) : Lemma
    (requires is_processed processed x)
    (ensures edge_satisfies_triangle dist1 weights x y)
    [SMTPat (is_processed processed x); SMTPat (edge_satisfies_triangle dist1 weights x y)]
    =
    if x = v then begin
      // x is processed and being relaxed to
      // By stability: dist1[x] = dist[x]
      // dist1[y] <= dist[y] (relaxation only decreases)
      // Since edge_satisfies_triangle dist weights x y, we have:
      //   (w_xy < inf /\ dist[x] < inf) ==> dist[y] <= dist[x] + w_xy
      // Since dist1[x] = dist[x] and dist1[y] <= dist[y], we get:
      //   (w_xy < inf /\ dist1[x] < inf) ==> dist1[y] <= dist1[x] + w_xy
      ()
    end else begin
      // x <> v: use the preservation lemma
      relax_edge_preserves_triangle_others dist weights u v x y
    end
  in
  ()
#pop-options

(* Relaxing all edges from u preserves triangle inequality for edges from processed vertices *)
(* The key insight: processed vertices != u, and stability ensures their distances don't change *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 35"
let rec relax_from_u_preserves_triangle_from_processed 
                                               (#n: nat) (dist: dist_vec n) 
                                               (weights: weight_matrix n)
                                               (u: nat{u < n}) (v_start: nat)
                                               (processed: processed_set)
  : Lemma
    (requires
      triangle_inequality_from_processed dist weights processed /\
      all_weights_non_negative weights /\
      not (is_processed processed u) /\ // u is not yet processed
      relaxation_stable_for_processed dist weights u processed) // stability for processed vertices
    (ensures
      triangle_inequality_from_processed (relax_from_u dist weights u v_start) weights processed)
    (decreases (n - v_start))
  =
  if v_start >= n then ()
  else begin
    let dist1 = relax_edge dist weights u v_start in
    
    // Establish that triangle inequality holds for dist1 for all processed vertices
    relax_edge_preserves_triangle_from_processed dist weights u v_start processed;
    
    // Establish that stability is preserved for dist1
    relax_edge_preserves_stability dist weights u v_start processed;
    
    // Recursive call
    relax_from_u_preserves_triangle_from_processed dist1 weights u (v_start + 1) processed
  end
#pop-options

(* ===== Main Theorem: Processing All Vertices Establishes Triangle Inequality ===== *)

(* When we process vertex u (relax all edges from u), triangle inequality extends to include u *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let process_vertex_extends_triangle (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                    (processed: processed_set) (u: nat{u < n})
  : Lemma
    (requires
      triangle_inequality_from_processed dist weights processed /\
      all_weights_non_negative weights /\
      not (is_processed processed u) /\
      relaxation_stable_for_processed dist weights u processed)
    (ensures (
      let dist' = relax_from_u dist weights u 0 in
      let processed' = add_to_processed processed u in
      triangle_inequality_from_processed dist' weights processed'))
  =
  let dist' = relax_from_u dist weights u 0 in
  let processed' = add_to_processed processed u in
  
  // Part 1: Triangle inequality for edges from previously processed vertices is preserved
  relax_from_u_preserves_triangle_from_processed dist weights u 0 processed;
  assert (triangle_inequality_from_processed dist' weights processed);
  
  // Part 2: All edges from u satisfy triangle inequality after relaxation
  relax_from_u_establishes_all_from_u dist weights u;
  assert (forall (v: nat). v < n /\ u <> v ==> edge_satisfies_triangle dist' weights u v);
  
  // Part 3: Self-loop u->u (if exists) also satisfies triangle inequality
  // For u->u: we need d_u' <= d_u' + w(u,u), which is always true for non-negative weights
  assert (forall (v: nat). v < n ==> edge_satisfies_triangle dist' weights u v);
  
  // Combine: processed' = processed ∪ {u}
  assert (forall (x v: nat). x < n /\ v < n /\ is_processed processed' x ==>
    edge_satisfies_triangle dist' weights x v)
#pop-options

(* ===== Dijkstra-Order Processing ===== *)

(* Find minimum-distance unprocessed vertex, scanning from index i.
   current_min = n means "no candidate yet". *)
let rec find_min_from (#n: nat) (dist: dist_vec n) (processed: processed_set)
                      (i: nat) (current_min: nat)
  : Tot nat (decreases (n - i))
  = if i >= n then current_min
    else if is_processed processed i then
      find_min_from dist processed (i + 1) current_min
    else if current_min >= n then
      find_min_from dist processed (i + 1) i
    else if Seq.index dist i < Seq.index dist current_min then
      find_min_from dist processed (i + 1) i
    else
      find_min_from dist processed (i + 1) current_min

let find_min (#n: nat) (dist: dist_vec n) (processed: processed_set) : nat =
  find_min_from dist processed 0 n

(* Spec of find_min_from: basic properties *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let rec find_min_from_basic (#n: nat) (dist: dist_vec n) (processed: processed_set)
                            (i: nat) (current_min: nat)
  : Lemma
    (ensures (
      let r = find_min_from dist processed i current_min in
      (r == current_min \/ (i <= r /\ r < n /\ not (is_processed processed r))) /\
      ((current_min < n /\ not (is_processed processed current_min)) ==> r < n) /\
      (r < n /\ r <> current_min ==> not (is_processed processed r)) /\
      (r < n /\ current_min < n /\ not (is_processed processed current_min) ==>
        Seq.index dist r <= Seq.index dist current_min)))
    (decreases (n - i))
  = if i >= n then ()
    else if is_processed processed i then
      find_min_from_basic dist processed (i + 1) current_min
    else if current_min >= n then
      find_min_from_basic dist processed (i + 1) i
    else if Seq.index dist i < Seq.index dist current_min then
      find_min_from_basic dist processed (i + 1) i
    else
      find_min_from_basic dist processed (i + 1) current_min
#pop-options

(* Spec of find_min_from: minimality property *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
let rec find_min_from_min (#n: nat) (dist: dist_vec n) (processed: processed_set)
                          (i: nat) (current_min: nat)
  : Lemma
    (requires current_min >= n \/ not (is_processed processed current_min))
    (ensures (
      let r = find_min_from dist processed i current_min in
      r < n ==>
        ((current_min < n ==> Seq.index dist r <= Seq.index dist current_min) /\
         (forall (j: nat). j >= i /\ j < n /\ not (is_processed processed j) ==>
          Seq.index dist r <= Seq.index dist j))))
    (decreases (n - i))
  = if i >= n then ()
    else begin
      find_min_from_basic dist processed i current_min;
      if is_processed processed i then
        find_min_from_min dist processed (i + 1) current_min
      else if current_min >= n then
        find_min_from_min dist processed (i + 1) i
      else if Seq.index dist i < Seq.index dist current_min then
        find_min_from_min dist processed (i + 1) i
      else
        find_min_from_min dist processed (i + 1) current_min
    end
#pop-options

(* Corollary: find_min returns the global min-distance unprocessed vertex *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 15"
let find_min_spec (#n: nat) (dist: dist_vec n) (processed: processed_set)
  : Lemma
    (ensures (
      let u = find_min dist processed in
      (u < n ==> (
        not (is_processed processed u) /\
        (forall (v: nat). v < n /\ not (is_processed processed v) ==>
          Seq.index dist u <= Seq.index dist v)))))
  = find_min_from_basic dist processed 0 n;
    find_min_from_min dist processed 0 n
#pop-options

(* Process vertices in Dijkstra order (greedy min-distance selection) *)
let rec process_vertices (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                         (processed: processed_set) (remaining: nat)
  : Tot (dist_vec n)
  =
  if remaining = 0 then dist
  else
    let u = find_min dist processed in
    if u >= n then dist
    else
      let dist' = relax_from_u dist weights u 0 in
      process_vertices dist' weights (add_to_processed processed u) (remaining - 1)

(* If there's an unprocessed vertex >= i, find_min_from returns < n *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let rec find_min_from_finds_unprocessed (#n: nat) (dist: dist_vec n) (processed: processed_set)
                                        (i: nat) (current_min: nat) (v: nat)
  : Lemma
    (requires v >= i /\ v < n /\ not (is_processed processed v))
    (ensures find_min_from dist processed i current_min < n)
    (decreases (n - i))
  = if i >= n then () // impossible since v >= i and v < n
    else if i = v then begin
      // i is unprocessed, so find_min_from will pick it (or a better candidate)
      if is_processed processed i then () // impossible since i = v and v is unprocessed
      else if current_min >= n then
        // new current_min = i < n; basic spec says result will be < n
        find_min_from_basic dist processed (i + 1) i
      else if Seq.index dist i < Seq.index dist current_min then
        find_min_from_basic dist processed (i + 1) i
      else
        // current_min < n already; basic spec gives result < n
        find_min_from_basic dist processed (i + 1) current_min
    end else begin
      // i <> v, so v > i, which means v >= i+1
      if is_processed processed i then
        find_min_from_finds_unprocessed dist processed (i + 1) current_min v
      else if current_min >= n then
        find_min_from_finds_unprocessed dist processed (i + 1) i v
      else if Seq.index dist i < Seq.index dist current_min then
        find_min_from_finds_unprocessed dist processed (i + 1) i v
      else
        find_min_from_finds_unprocessed dist processed (i + 1) current_min v
    end
#pop-options

(* When find_min >= n, all vertices are processed *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 15"
let find_min_ge_n_means_all_processed (#n: nat) (dist: dist_vec n) (processed: processed_set)
  : Lemma
    (requires find_min dist processed >= n)
    (ensures forall (v: nat). v < n ==> is_processed processed v)
  =
  // By contrapositive: if there exists v < n with not processed v, then find_min < n.
  // Proved by find_min_from_finds_unprocessed.
  let aux (v: nat) : Lemma (v < n ==> is_processed processed v) =
    if v < n && not (is_processed processed v) then
      find_min_from_finds_unprocessed dist processed 0 n v
    else ()
  in
  FStar.Classical.forall_intro aux
#pop-options

(* Dijkstra ordering: all processed distances <= all unprocessed distances *)
let processed_le_unprocessed (#n: nat) (dist: dist_vec n) (processed: processed_set) : prop =
  forall (x u: nat). x < n /\ u < n /\ is_processed processed x /\ not (is_processed processed u) ==>
    Seq.index dist x <= Seq.index dist u

(* Dijkstra ordering implies stability *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 15"
let ordering_implies_stability (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                               (processed: processed_set) (u: nat{u < n})
  : Lemma
    (requires
      all_weights_non_negative weights /\
      not (is_processed processed u) /\
      processed_le_unprocessed dist processed)
    (ensures
      relaxation_stable_for_processed dist weights u processed)
  =
  // For any processed x: dist[x] <= dist[u] (ordering)
  // w(u,x) >= 0 (non-negative weights)
  // So dist[u] + w(u,x) >= dist[u] >= dist[x]
  // Hence: not (w < inf /\ d_u < inf /\ d_u + w < d_x)
  ()
#pop-options

(* Under stability, relax_from_u preserves distances of all processed vertices *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let rec relax_from_u_preserves_processed_dist (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                               (u: nat{u < n}) (v_start: nat)
                                               (x: nat{x < n})
                                               (processed: processed_set)
  : Lemma
    (requires
      is_processed processed x /\
      not (is_processed processed u) /\
      all_weights_non_negative weights /\
      relaxation_stable_for_processed dist weights u processed)
    (ensures
      Seq.index (relax_from_u dist weights u v_start) x == Seq.index dist x)
    (decreases (n - v_start))
  = if v_start >= n then ()
    else begin
      let dist1 = relax_edge dist weights u v_start in
      // Show dist1[x] = dist[x]
      if v_start = x then
        // x is the target: by stability, no change
        relax_edge_stable_for_processed dist weights u x processed
      else ();
        // x is not the target: relax_edge only changes dist[v_start]
      // Stability preserved for dist1
      relax_edge_preserves_stability dist weights u v_start processed;
      // Recurse
      relax_from_u_preserves_processed_dist dist1 weights u (v_start + 1) x processed
    end
#pop-options

(* After relax_from_u with Dijkstra ordering, unprocessed vertices have dist >= dist[u] *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 25"
let rec relax_from_u_unprocessed_ge_u (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                                       (u: nat{u < n}) (v_start: nat) (v: nat{v < n})
  : Lemma
    (requires
      all_weights_non_negative weights /\
      Seq.index dist v >= Seq.index dist u /\
      v <> u)
    (ensures
      Seq.index (relax_from_u dist weights u v_start) v >= Seq.index dist u)
    (decreases (n - v_start))
  = if v_start >= n then ()
    else begin
      let dist1 = relax_edge dist weights u v_start in
      // dist1[u] = dist[u] (relax_edge only changes target, and self-loop is noop)
      // For v: if v_start = v, dist1[v] = min(dist[v], dist[u]+w) >= dist[u]
      //        if v_start <> v, dist1[v] = dist[v]
      // In both cases: dist1[v] >= dist[u] = dist1[u]
      relax_from_u_unprocessed_ge_u dist1 weights u (v_start + 1) v
    end
#pop-options

(* Dijkstra ordering is preserved after processing the minimum vertex *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
let ordering_preserved (#n: nat) (dist: dist_vec n) (weights: weight_matrix n)
                       (processed: processed_set) (u: nat{u < n})
  : Lemma
    (requires
      all_weights_non_negative weights /\
      not (is_processed processed u) /\
      processed_le_unprocessed dist processed /\
      // u is minimum among unprocessed
      (forall (v: nat). v < n /\ not (is_processed processed v) ==>
        Seq.index dist u <= Seq.index dist v))
    (ensures (
      let dist' = relax_from_u dist weights u 0 in
      let processed' = add_to_processed processed u in
      processed_le_unprocessed dist' processed'))
  =
  let dist' = relax_from_u dist weights u 0 in
  let processed' = add_to_processed processed u in
  // Need: for all processed' x and unprocessed' v: dist'[x] <= dist'[v]
  // processed' = processed ∪ {u}
  // unprocessed' = unprocessed \ {u}
  
  // Derive stability from ordering
  ordering_implies_stability dist weights processed u;
  
  let aux (x: nat) (v: nat) : Lemma
    (requires x < n /\ v < n /\ is_processed processed' x /\ not (is_processed processed' v))
    (ensures Seq.index dist' x <= Seq.index dist' v)
    =
    relax_from_u_unprocessed_ge_u dist weights u 0 v;
    if is_processed processed x then begin
      relax_from_u_preserves_processed_dist dist weights u 0 x processed;
      assert (Seq.index dist x <= Seq.index dist u)
    end else begin
      relax_from_u_preserves_index dist weights u 0 u
    end
  in
  // Instantiate aux for all x, v to establish the universal
  let aux_imp (x: nat) (v: nat) : Lemma
    (x < n /\ v < n /\ is_processed processed' x /\ not (is_processed processed' v) ==>
     Seq.index dist' x <= Seq.index dist' v)
    = if x < n && v < n && is_processed processed' x && not (is_processed processed' v) then
        aux x v
      else ()
  in
  FStar.Classical.forall_intro_2 aux_imp
#pop-options

(* Count of unprocessed vertices in [0, n) *)
let rec count_unprocessed (#n: nat) (processed: processed_set) (i: nat)
  : Tot nat (decreases (n - i))
  = if i >= n then 0
    else (if is_processed processed i then 0 else 1) + count_unprocessed #n processed (i + 1)

(* Adding a vertex to processed decreases count by 1 *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let rec count_unprocessed_add (#n: nat) (processed: processed_set) (u: nat{u < n}) (i: nat)
  : Lemma
    (requires not (is_processed processed u))
    (ensures count_unprocessed #n (add_to_processed processed u) i + 
             (if i <= u then 1 else 0) == count_unprocessed #n processed i)
    (decreases (n - i))
  = if i >= n then ()
    else count_unprocessed_add #n processed u (i + 1)
#pop-options

(* If there's an unprocessed vertex, count >= 1 *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let rec count_unprocessed_pos (#n: nat) (processed: processed_set) (i: nat) (v: nat)
  : Lemma
    (requires v >= i /\ v < n /\ not (is_processed processed v))
    (ensures count_unprocessed #n processed i >= 1)
    (decreases (n - i))
  = if i >= n then ()
    else if i = v then ()
    else count_unprocessed_pos #n processed (i + 1) v
#pop-options

(* After processing all vertices in Dijkstra order, triangle inequality holds *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec process_all_vertices_establishes_triangle (#n: nat) (dist: dist_vec n) 
                                                   (weights: weight_matrix n)
                                                   (processed: processed_set)
                                                   (remaining: nat)
  : Lemma
    (requires
      remaining >= count_unprocessed #n processed 0 /\
      all_weights_non_negative weights /\
      triangle_inequality_from_processed dist weights processed /\
      processed_le_unprocessed dist processed)
    (ensures (
      let dist' = process_vertices dist weights processed remaining in
      triangle_inequality dist' weights))
    (decreases remaining)
  =
  if remaining = 0 then begin
    // remaining >= count_unprocessed, and remaining = 0, so count_unprocessed = 0
    // This means all vertices are processed.
    find_min_spec dist processed;
    let u = find_min dist processed in
    if u >= n then
      find_min_ge_n_means_all_processed dist processed
    else begin
      // u < n and not processed u => count_unprocessed >= 1 => remaining >= 1. Contradiction.
      count_unprocessed_pos #n processed 0 u;
      assert (false)
    end
  end
  else begin
    find_min_spec dist processed;
    let u = find_min dist processed in
    if u >= n then
      find_min_ge_n_means_all_processed dist processed
    else begin
      let dist1 = relax_from_u dist weights u 0 in
      let processed1 = add_to_processed processed u in
      
      ordering_implies_stability dist weights processed u;
      process_vertex_extends_triangle dist weights processed u;
      ordering_preserved dist weights processed u;
      
      // count_unprocessed decreases by 1
      count_unprocessed_add #n processed u 0;
      
      process_all_vertices_establishes_triangle dist1 weights processed1 (remaining - 1)
    end
  end
#pop-options

(* Initially all vertices are unprocessed *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 15"
let rec count_unprocessed_initial (#n: nat) (i: nat)
  : Lemma
    (ensures count_unprocessed #n initial_processed i == (if i >= n then 0 else n - i))
    (decreases (n - i))
  = if i >= n then ()
    else count_unprocessed_initial #n (i + 1)
#pop-options

(* Main theorem: After running Dijkstra (processing all vertices), triangle inequality holds *)
let dijkstra_establishes_triangle_inequality (#n: nat) (dist_init: dist_vec n) 
                                             (weights: weight_matrix n)
  : Lemma
    (requires
      n > 0 /\
      all_weights_non_negative weights /\
      triangle_inequality_from_processed dist_init weights initial_processed /\
      processed_le_unprocessed dist_init initial_processed)
    (ensures (
      let dist_final = process_vertices dist_init weights initial_processed n in
      triangle_inequality dist_final weights))
  =
  count_unprocessed_initial #n 0;
  process_all_vertices_establishes_triangle dist_init weights initial_processed n

(* ===== Corollary for Dijkstra Implementation ===== *)

(* After initialization (dist[source] = 0, all others = inf), 
   triangle inequality from empty processed set holds trivially *)
let dijkstra_init_satisfies_triangle (#n: nat) (source: nat{source < n}) : Lemma
  (requires n > 0)
  (ensures
    (let dist_init = Seq.create n inf in
     let dist_init = Seq.upd dist_init source 0 in
     forall (weights: weight_matrix n). 
       all_weights_non_negative weights ==>
       triangle_inequality_from_processed dist_init weights initial_processed))
  =
  ()

(* Initial ordering: no processed vertices, so ordering holds vacuously *)
let dijkstra_init_ordering (#n: nat) (source: nat{source < n}) : Lemma
  (requires n > 0)
  (ensures
    (let dist_init : dist_vec n = Seq.upd (Seq.create n inf) source 0 in
     processed_le_unprocessed dist_init initial_processed))
  =
  ()

(* Combined: Dijkstra's algorithm automatically establishes triangle inequality *)
let dijkstra_algorithm_establishes_triangle (#n: nat) (source: nat{source < n})
                                            (weights: weight_matrix n)
  : Lemma
    (requires
      n > 0 /\
      all_weights_non_negative weights)
    (ensures
      (let dist_init = Seq.upd (Seq.create n inf) source 0 in
       let dist_final = process_vertices dist_init weights initial_processed n in
       triangle_inequality dist_final weights))
  =
  let dist_init = Seq.upd (Seq.create n inf) source 0 in
  dijkstra_init_satisfies_triangle #n source;
  dijkstra_init_ordering #n source;
  dijkstra_establishes_triangle_inequality dist_init weights

(*
 * ===== Summary and Application to Pulse Implementation =====
 * 
 * In CLRS.Ch24.Dijkstra.fst, the implementation establishes the triangle
 * inequality through the main relaxation loop. Key observation:
 * 
 * Key results from this file:
 * 
 * 1. [relax_edge_establishes_triangle]
 *    When we relax an edge (u,v), that edge automatically satisfies the
 *    triangle inequality afterwards.
 * 
 * 2. [process_vertex_extends_triangle]
 *    When we process vertex u (relax all edges from u), triangle inequality
 *    extends to cover all edges from u, while preserving it for already-processed vertices.
 * 
 * 3. [dijkstra_algorithm_establishes_triangle]
 *    After processing all vertices (main Dijkstra loop completes),
 *    triangle inequality holds for ALL edges automatically.
 * 
 * 4. Any separate verification pass is REDUNDANT for establishing
 *    triangle inequality. It can only confirm what must already be true!
 * 
 * Practical impact:
 * - Triangle inequality follows directly from the main relaxation loop
 * - The postcondition can state: triangle_inequality sweights sdist' (SZ.v n)
 *   and this follows from the main loop by [dijkstra_algorithm_establishes_triangle]
 *)
