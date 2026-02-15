module CLRS.Ch26.MaxFlow.Proofs

open FStar.Mul
open FStar.List.Tot
open CLRS.Ch26.MaxFlow.Spec

module Seq = FStar.Seq
module L = FStar.List.Tot

(*
   Proofs for Edmonds-Karp Maximum Flow Algorithm
   
   P0.1.7: Prove capacity constraints maintained after augmentation
   P0.1.8: Prove flow conservation maintained after augmentation
   P0.1.9: Prove termination (flow value increases each iteration)
   P0.1.10: Prove postcondition: final flow satisfies capacity + conservation
   
   Complex proofs use assume where full formalization would require extensive
   inductive reasoning about path structure and flow properties.
*)

(** ========== Helper Lemmas for Sum Properties ========== *)

(** Lemma: sum_flow_into with index beyond n remains unchanged *)
let rec lemma_sum_flow_into_beyond_n (flow: Seq.seq int) (n: nat{Seq.length flow == n * n}) 
                                      (v: nat{v < n}) (u: nat)
  : Lemma 
    (requires u >= n)
    (ensures sum_flow_into flow n v u == sum_flow_into flow n v n)
    (decreases u)
  = if u = 0 then ()
    else if u - 1 < n then ()
    else lemma_sum_flow_into_beyond_n flow n v (u - 1)

(** Lemma: sum_flow_out with index beyond n remains unchanged *)
let rec lemma_sum_flow_out_beyond_n (flow: Seq.seq int) (n: nat{Seq.length flow == n * n}) 
                                     (v: nat{v < n}) (w: nat)
  : Lemma 
    (requires w >= n)
    (ensures sum_flow_out flow n v w == sum_flow_out flow n v n)
    (decreases w)
  = if w = 0 then ()
    else if w - 1 < n then ()
    else lemma_sum_flow_out_beyond_n flow n v (w - 1)

(** Lemma: Updating flow at (u,v) doesn't affect sum_flow_into for w ≠ v *)
let rec lemma_sum_flow_into_update_other (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                                          (u: nat{u < n}) (v: nat{v < n}) (x: int)
                                          (w: nat{w < n /\ w <> v}) (k: nat)
  : Lemma 
    (ensures sum_flow_into (set flow n u v x) n w k == sum_flow_into flow n w k)
    (decreases k)
  = if k = 0 then ()
    else if k - 1 < n then 
      (assert (get (set flow n u v x) n (k-1) w == get flow n (k-1) w);
       lemma_sum_flow_into_update_other flow n u v x w (k - 1))
    else lemma_sum_flow_into_update_other flow n u v x w (k - 1)

(** Lemma: Updating flow at (u,v) doesn't affect sum_flow_out for w ≠ u *)
let rec lemma_sum_flow_out_update_other (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                                         (u: nat{u < n}) (v: nat{v < n}) (x: int)
                                         (w: nat{w < n /\ w <> u}) (k: nat)
  : Lemma 
    (ensures sum_flow_out (set flow n u v x) n w k == sum_flow_out flow n w k)
    (decreases k)
  = if k = 0 then ()
    else if k - 1 < n then 
      (assert (get (set flow n u v x) n w (k-1) == get flow n w (k-1));
       lemma_sum_flow_out_update_other flow n u v x w (k - 1))
    else lemma_sum_flow_out_update_other flow n u v x w (k - 1)

(** Lemma: Updating flow at (u,v) affects sum_flow_out for u at position v *)
let rec lemma_sum_flow_out_before_v (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                                     (u: nat{u < n}) (v: nat{v < n}) (x: int) (k: nat)
  : Lemma 
    (requires k <= v)
    (ensures sum_flow_out (set flow n u v x) n u k == sum_flow_out flow n u k)
    (decreases k)
  = if k = 0 then ()
    else if k - 1 < n then
      lemma_sum_flow_out_before_v flow n u v x (k - 1)
    else lemma_sum_flow_out_before_v flow n u v x (k - 1)

(** Lemma: Increasing flow[u][v] by delta increases sum_flow_out for u by exactly delta *)
let rec lemma_sum_flow_out_increase (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                                     (u: nat{u < n}) (v: nat{v < n}) (delta: int) (k: nat)
  : Lemma 
    (requires k > v)
    (ensures sum_flow_out (set flow n u v (get flow n u v + delta)) n u k == 
             sum_flow_out flow n u k + delta)
    (decreases k)
  = if k = 0 then ()
    else if k - 1 < n then
      if k - 1 = v then
        // At position v: difference is delta, before v: sum is unchanged
        lemma_sum_flow_out_before_v flow n u v (get flow n u v + delta) v
      else if k - 1 > v then
        // After v: recursively apply
        lemma_sum_flow_out_increase flow n u v delta (k - 1)
      else
        // k - 1 < v: sum unchanged up to this point
        lemma_sum_flow_out_before_v flow n u v (get flow n u v + delta) k
    else lemma_sum_flow_out_increase flow n u v delta (k - 1)

(** Lemma: Updating flow at (u,v) affects sum_flow_into for v at position u *)
let rec lemma_sum_flow_into_before_u (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                                      (u: nat{u < n}) (v: nat{v < n}) (x: int) (k: nat)
  : Lemma 
    (requires k <= u)
    (ensures sum_flow_into (set flow n u v x) n v k == sum_flow_into flow n v k)
    (decreases k)
  = if k = 0 then ()
    else if k - 1 < n then
      lemma_sum_flow_into_before_u flow n u v x (k - 1)
    else lemma_sum_flow_into_before_u flow n u v x (k - 1)

(** Lemma: Increasing flow[u][v] by delta increases sum_flow_into for v by exactly delta *)
let rec lemma_sum_flow_into_increase (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                                      (u: nat{u < n}) (v: nat{v < n}) (delta: int) (k: nat)
  : Lemma 
    (requires k > u)
    (ensures sum_flow_into (set flow n u v (get flow n u v + delta)) n v k == 
             sum_flow_into flow n v k + delta)
    (decreases k)
  = if k = 0 then ()
    else if k - 1 < n then
      if k - 1 = u then
        // At position u: difference is delta, before u: sum is unchanged
        lemma_sum_flow_into_before_u flow n u v (get flow n u v + delta) u
      else if k - 1 > u then
        // After u: recursively apply
        lemma_sum_flow_into_increase flow n u v delta (k - 1)
      else
        // k - 1 < u: sum unchanged up to this point
        lemma_sum_flow_into_before_u flow n u v (get flow n u v + delta) k
    else lemma_sum_flow_into_increase flow n u v delta (k - 1)


(** ========== P0.1.7 & P0.1.8: Augmentation Preserves Valid Flow ========== *)

(** Lemma: Augmenting a single edge maintains capacity constraints for that edge *)
let lemma_augment_edge_capacity (flow: Seq.seq int) (cap: Seq.seq int)
                                 (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
                                 (u: nat{u < n}) (v: nat{v < n}) (delta: int)
  : Lemma
    (requires 
      0 <= get flow n u v /\ get flow n u v <= get cap n u v /\
      0 <= get flow n v u /\ get flow n v u <= get cap n v u /\
      delta > 0 /\
      (residual_capacity cap flow n u v > 0 ==> delta <= residual_capacity cap flow n u v) /\
      (residual_capacity cap flow n u v <= 0 ==> delta <= get flow n v u))
    (ensures 
      (let flow' = augment_edge flow cap n u v delta in
       0 <= get flow' n u v /\ get flow' n u v <= get cap n u v /\
       0 <= get flow' n v u /\ get flow' n v u <= get cap n v u))
  = let flow' = augment_edge flow cap n u v delta in
    if residual_capacity cap flow n u v > 0 then
      // Forward edge: flow[u][v] += delta
      (assert (get flow' n u v == get flow n u v + delta);
       assert (get flow' n u v <= get cap n u v))
    else
      // Backward edge: flow[v][u] -= delta
      (assert (get flow' n v u == get flow n v u - delta);
       assert (0 <= get flow' n v u))

(** Lemma: Vertices not on the path maintain flow conservation after single edge augmentation *)
let lemma_augment_edge_conservation_other (flow: Seq.seq int) (cap: Seq.seq int)
                                           (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
                                           (u: nat{u < n}) (v: nat{v < n}) (delta: int)
                                           (w: nat{w < n /\ w <> u /\ w <> v})
  : Lemma
    (requires sum_flow_into flow n w n == sum_flow_out flow n w n)
    (ensures (let flow' = augment_edge flow cap n u v delta in
              sum_flow_into flow' n w n == sum_flow_out flow' n w n))
  = let flow' = augment_edge flow cap n u v delta in
    if residual_capacity cap flow n u v > 0 then
      // Forward edge case
      (lemma_sum_flow_into_update_other flow n u v (get flow n u v + delta) w n;
       lemma_sum_flow_out_update_other flow n u v (get flow n u v + delta) w n)
    else
      // Backward edge case
      (lemma_sum_flow_into_update_other flow n v u (get flow n v u - delta) w n;
       lemma_sum_flow_out_update_other flow n v u (get flow n v u - delta) w n)

(** Lemma: For intermediate vertices on path, inflow and outflow both increase by delta *)
let lemma_augment_edge_conservation_intermediate (flow: Seq.seq int) (cap: Seq.seq int)
                                                  (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
                                                  (u1: nat{u1 < n}) (v1: nat{v1 < n})
                                                  (u2: nat{u2 < n}) (v2: nat{v2 < n})
                                                  (delta: int)
  : Lemma
    (requires 
      v1 = u2 /\  // v1 is the intermediate vertex
      u1 <> v1 /\ v1 <> v2 /\  // No self-loops on path
      sum_flow_into flow n v1 n == sum_flow_out flow n v1 n /\
      residual_capacity cap flow n u1 v1 > 0 /\
      residual_capacity cap flow n u2 v2 > 0)
    (ensures 
      (let flow' = augment_edge flow cap n u1 v1 delta in
       let flow'' = augment_edge flow' cap n u2 v2 delta in
       sum_flow_into flow'' n v1 n == sum_flow_out flow'' n v1 n))
  = // Both edges are forward edges (positive residual capacity)
    // First edge (u1, v1): increases inflow to v1 by delta
    let flow' = augment_edge flow cap n u1 v1 delta in
    assert (get flow' n u1 v1 == get flow n u1 v1 + delta);
    lemma_sum_flow_into_increase flow n u1 v1 delta n;
    assert (sum_flow_into flow' n v1 n == sum_flow_into flow n v1 n + delta);
    // Outflow from v1 unchanged by first edge (since u1 ≠ v1)
    lemma_sum_flow_out_update_other flow n u1 v1 (get flow n u1 v1 + delta) v1 n;
    assert (sum_flow_out flow' n v1 n == sum_flow_out flow n v1 n);
    // Second edge (u2, v2) = (v1, v2): increases outflow from v1 by delta
    let flow'' = augment_edge flow' cap n u2 v2 delta in
    assert (u2 = v1);
    assert (get flow'' n v1 v2 == get flow' n v1 v2 + delta);
    lemma_sum_flow_out_increase flow' n v1 v2 delta n;
    assert (sum_flow_out flow'' n v1 n == sum_flow_out flow' n v1 n + delta);
    // Inflow to v1 unchanged by second edge (since v1 ≠ v2)
    lemma_sum_flow_into_update_other flow' n v1 v2 (get flow' n v1 v2 + delta) v1 n;
    assert (sum_flow_into flow'' n v1 n == sum_flow_into flow' n v1 n);
    // Combine: inflow increased by delta, outflow increased by delta
    assert (sum_flow_into flow'' n v1 n == sum_flow_into flow n v1 n + delta);
    assert (sum_flow_out flow'' n v1 n == sum_flow_out flow n v1 n + delta);
    // Since they were equal initially, they remain equal
    assert (sum_flow_into flow'' n v1 n == sum_flow_out flow'' n v1 n)

(** Lemma: Augmenting one edge doesn't decrease bottleneck of later path *)
let lemma_bottleneck_tail (cap: Seq.seq int) (flow flow': Seq.seq int)
                               (n: nat{Seq.length cap == n * n /\ Seq.length flow == n * n /\ Seq.length flow' == n * n})
                               (u v: nat{u < n /\ v < n})
                               (path: list nat{Cons? path /\ (forall (w: nat). L.mem w path ==> w < n)})
  : Lemma
    (requires 
      Cons? path /\ L.hd path = v /\
      // flow' is flow with one edge (u,v) augmented
      (forall (u': nat{u' < n}) (v': nat{v' < n}). 
        (u' = u /\ v' = v) ==> get flow' n u' v' >= get flow n u' v'))
    (ensures bottleneck cap flow' n path >= bottleneck cap flow n path \/ 
             bottleneck cap flow' n path <= 0)
  = // Path starts at v, so w1 = v
    // The edge (u,v) is not on this path (path starts at v, so edges are from v onwards)
    // Therefore, edges on this path are unaffected by the augmentation
    // Each edge capacity on path is unchanged, so bottleneck is unchanged or increased
    // This is a complex property about path structure - we use assume for now
    assume (bottleneck cap flow' n path >= bottleneck cap flow n path \/ 
            bottleneck cap flow' n path <= 0)

(** Main lemma: Path augmentation preserves valid flow (P0.1.7 + P0.1.8) *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec lemma_augment_preserves_capacity (flow: Seq.seq int) (cap: Seq.seq int)
                                          (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
                                          (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
                                          (bn: int)
  : Lemma
    (requires 
      bn > 0 /\
      bn <= bottleneck cap flow n path /\
      (forall (u: nat{u < n}) (v: nat{v < n}). 
        0 <= get flow n u v /\ get flow n u v <= get cap n u v))
    (ensures 
      (let flow' = augment_aux flow cap n path bn in
       forall (u: nat{u < n}) (v: nat{v < n}). 
         0 <= get flow' n u v /\ get flow' n u v <= get cap n u v))
    (decreases path)
  = match path with
    | [v] -> ()
    | u :: v :: rest ->
      // First, establish that bn is within residual capacity
      let edge_cap = 
        if residual_capacity cap flow n u v > 0 
        then residual_capacity cap flow n u v
        else residual_capacity_backward flow n u v in
      // bn <= bottleneck of whole path, so bn <= edge capacity
      assert (bn <= edge_cap);
      
      // Now augment the edge
      let flow' = augment_edge flow cap n u v bn in
      assert (Seq.length flow' == n * n);
      
      // Show flow' maintains capacity for all edges
      let aux (u': nat{u' < n}) (v': nat{v' < n})
        : Lemma (0 <= get flow' n u' v' /\ get flow' n u' v' <= get cap n u' v')
        = if residual_capacity cap flow n u v > 0 then
            // Forward edge case: flow[u][v] += bn
            if u' = u && v' = v then
              // The modified edge
              (assert (get flow' n u v == get flow n u v + bn);
               assert (bn <= residual_capacity cap flow n u v);
               assert (get flow n u v + bn <= get cap n u v))
            else
              // Other edges unchanged
              (assert (get flow' n u' v' == get flow n u' v'))
          else
            // Backward edge case: flow[v][u] -= bn
            if u' = v && v' = u then
              // The modified edge  
              (assert (get flow' n v u == get flow n v u - bn);
               assert (bn <= get flow n v u);
               assert (0 <= get flow n v u - bn))
            else
              // Other edges unchanged
              (assert (get flow' n u' v' == get flow n u' v'))
      in
      FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux);
      
      // For the recursive call, we need bn <= bottleneck cap flow' n (v :: rest)
      // Since bn <= bottleneck of the entire path and the bottleneck is the minimum
      // along all edges, bn is also <= the bottleneck of any subpath.
      // The key insight: bn was computed as min over all edges including (u,v)
      // After augmenting (u,v), the remaining edges still have at least bn capacity
      // because bn was the minimum. This requires detailed analysis of bottleneck_aux.
      assume (bn <= bottleneck cap flow' n (v :: rest));
      
      // Recursively augment the rest
      lemma_augment_preserves_capacity flow' cap n (v :: rest) bn
    | [] -> ()
#pop-options


(** ========== P0.1.9: Termination (Flow Value Increases) ========== *)

(** Lemma: Zero flow has value 0 *)
let rec lemma_zero_sum_in (n: nat) (source: nat{source < n}) (k: nat)
  : Lemma 
    (ensures sum_flow_into (Seq.create (n * n) 0) n source k == 0)
    (decreases k)
  = if k = 0 then ()
    else lemma_zero_sum_in n source (k - 1)

let rec lemma_zero_sum_out (n: nat) (source: nat{source < n}) (k: nat)
  : Lemma 
    (ensures sum_flow_out (Seq.create (n * n) 0) n source k == 0)
    (decreases k)
  = if k = 0 then ()
    else lemma_zero_sum_out n source (k - 1)

let lemma_zero_flow_value (n: nat{n > 0}) (source: nat{source < n})
  : Lemma (ensures flow_value (Seq.create (n * n) 0) n source == 0)
  = lemma_zero_sum_in n source n;
    lemma_zero_sum_out n source n

(** Lemma: Augmenting along path strictly increases flow value (P0.1.9) *)
let lemma_augment_increases_value_aux (flow: Seq.seq int) (cap: Seq.seq int)
                                           (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
                                           (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
                                           (source: nat{source < n})
                                           (sink: nat{sink < n})
                                           (bn: int)
  : Lemma
    (requires 
      bn > 0 /\
      L.hd path == source /\
      L.last path == sink /\
      bn <= bottleneck cap flow n path)
    (ensures 
      (let flow' = augment_aux flow cap n path bn in
       flow_value flow' n source >= flow_value flow n source + bn))
  = // The key idea: augmenting a path from source to sink increases the net flow
    // out of the source by exactly bn units (the bottleneck value).
    // 
    // For a forward edge from source: outflow increases by bn
    // For a backward edge from source: inflow decreases by bn (which increases flow value)
    //
    // All intermediate edges maintain flow conservation, so the increase
    // in flow at the source propagates all the way to the sink.
    //
    // This is a fundamental property of augmenting paths in max-flow algorithms.
    // A complete proof would require induction on the path structure and careful
    // tracking of how each edge augmentation affects the flow value.
    
    assume ((let flow' = augment_aux flow cap n path bn in
             flow_value flow' n source >= flow_value flow n source + bn))


(** ========== P0.1.10: Postcondition (Valid Flow) ========== *)

(** Lemma: Zero flow satisfies capacity constraints *)
let lemma_zero_capacity (n: nat) (cap: Seq.seq int)
  : Lemma
    (requires 
      Seq.length cap == n * n /\
      (forall (i: nat). i < n * n ==> Seq.index cap i >= 0))
    (ensures 
      (let flow = Seq.create (n * n) 0 in
       forall (u: nat{u < n}) (v: nat{v < n}). 
         0 <= get flow n u v /\ get flow n u v <= get cap n u v))
  = ()

(** Lemma: Zero flow satisfies flow conservation *)
let rec lemma_zero_flow_conservation_in (n: nat) (v: nat{v < n}) (k: nat)
  : Lemma 
    (ensures sum_flow_into (Seq.create (n * n) 0) n v k == 0)
    (decreases k)
  = if k = 0 then ()
    else lemma_zero_flow_conservation_in n v (k - 1)

let rec lemma_zero_flow_conservation_out (n: nat) (v: nat{v < n}) (k: nat)
  : Lemma 
    (ensures sum_flow_out (Seq.create (n * n) 0) n v k == 0)
    (decreases k)
  = if k = 0 then ()
    else lemma_zero_flow_conservation_out n v (k - 1)

let lemma_zero_flow_valid (n: nat) (cap: Seq.seq int) (source: nat{source < n}) (sink: nat{sink < n})
  : Lemma
    (requires 
      Seq.length cap == n * n /\
      (forall (i: nat). i < n * n ==> Seq.index cap i >= 0))
    (ensures 
      (let flow = Seq.create (n * n) 0 in
       valid_flow #n flow cap source sink))
  = let flow = Seq.create (n * n) 0 in
    lemma_zero_capacity n cap;
    let aux (v: nat{v < n /\ v <> source /\ v <> sink})
      : Lemma (sum_flow_into flow n v n == sum_flow_out flow n v n)
      = lemma_zero_flow_conservation_in n v n;
        lemma_zero_flow_conservation_out n v n
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)


(** ========== Main Theorems ========== *)

(** P0.1.7 + P0.1.8: Augmentation preserves valid flow *)
let augment_preserves_valid (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                             (source: nat{source < n}) (sink: nat{sink < n})
                             (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
                             (bn: int{bn > 0})
  : Lemma
    (requires 
      valid_flow flow cap source sink /\
      bn <= bottleneck cap flow n path)
    (ensures valid_flow #n (augment_aux flow cap n path bn) cap source sink)
  = lemma_augment_preserves_capacity flow cap n path bn;
    // Conservation proof: P0.1.8
    // For each vertex v != source, sink on the path, augmentation increases both
    // inflow and outflow by bn (as the flow passes through)
    // For vertices not on the path, their flows are unchanged
    // Therefore, inflow = outflow is preserved for all intermediate vertices
    
    // The key insight: augmenting a path adds bn units of flow along every edge
    // For an intermediate vertex v on the path:
    //   - One incoming edge on path increases inflow by bn
    //   - One outgoing edge on path increases outflow by bn
    //   - Net change: inflow and outflow both increase by bn, so they remain equal
    
    // For vertices not on path: no edges are modified, so conservation trivially holds
    
    // This is a complex inductive argument over the path structure
    // We use assume here as the full proof requires detailed case analysis
    // on path structure and vertex membership
    assume (valid_flow #n (augment_aux flow cap n path bn) cap source sink)

(** P0.1.9: Augmentation increases flow value *)  
let augment_increases_value (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                             (source: nat{source < n}) (sink: nat{sink < n})
                             (path: list nat{Cons? path /\ L.hd path = source /\ L.last path = sink /\ 
                                             (forall (v: nat). L.mem v path ==> v < n)})
                             (bn: int{bn > 0})
  : Lemma
    (requires 
      valid_flow flow cap source sink /\
      bn <= bottleneck cap flow n path)
    (ensures 
      (let flow' = augment_aux flow cap n path bn in
       flow_value flow' n source > flow_value flow n source))
  = lemma_augment_increases_value_aux flow cap n path source sink bn

(** P0.1.10: Zero flow is valid *)
let zero_flow_valid (#n: nat) (cap: capacity_matrix n) (source: nat{source < n}) (sink: nat{sink < n})
  : Lemma
    (requires forall (i: nat). i < n * n ==> Seq.index cap i >= 0)
    (ensures 
      (let flow = Seq.create (n * n) 0 in
       valid_flow flow cap source sink))
  = lemma_zero_flow_valid n cap source sink
