module CLRS.Ch26.MaxFlow.Lemmas

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
   
   All proofs completed. Zero assumes for the core augmentation theorems.
   Requires distinct_vertices (simple path) precondition for augmentation proofs.
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
#push-options "--z3rlimit 10"
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
    // Help SMT: the first augment at (u1,v1) doesn't change cell (v1,v2) since u1≠v1
    // flow' = set flow n u1 v1 (...), and (v1,v2) ≠ (u1,v1) since v1≠u1
    assert (u1 * n + v1 <> v1 * n + v2);
    assert (get flow' n v1 v2 == get flow n v1 v2);
    assert (residual_capacity cap flow' n v1 v2 == residual_capacity cap flow n v1 v2);
    assert (residual_capacity cap flow' n v1 v2 > 0);
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
#pop-options

(** ========== Helper: Matrix cell independence under augment_edge ========== *)

(** When (a,b) ≠ (u,v), get (set m n u v x) n a b == get m n a b.
    Relies on index injectivity: a*n+b ≠ u*n+v when (a≠u ∨ b≠v) and a,b,u,v < n. *)
#push-options "--z3rlimit 20"
let lemma_get_set_other (m: Seq.seq int) (n: nat{n > 0 /\ Seq.length m == n * n})
                        (u v: nat{u < n /\ v < n}) (x: int) (a b: nat{a < n /\ b < n})
  : Lemma (requires a <> u \/ b <> v)
          (ensures get (set m n u v x) n a b == get m n a b)
  = // a*n+b ≠ u*n+v follows from (a≠u ∨ b≠v) with a,b,u,v < n
    // Then Seq.index (Seq.upd m (u*n+v) x) (a*n+b) = Seq.index m (a*n+b)
    if a = u then () // b ≠ v so indices differ
    else () // a ≠ u: a*n+b is in [a*n, a*n+n-1], u*n+v in [u*n, u*n+n-1], disjoint ranges
#pop-options

(** augment_edge on (u,v) preserves get at (a,b) when a ≠ u and b ≠ u *)
let lemma_augment_edge_get_other (flow cap: Seq.seq int) 
                                  (n: nat{n > 0 /\ Seq.length flow == n * n /\ Seq.length cap == n * n})
                                  (u v: nat{u < n /\ v < n}) (delta: int)
                                  (a b: nat{a < n /\ b < n})
  : Lemma (requires a <> u /\ b <> u)
          (ensures get (augment_edge flow cap n u v delta) n a b == get flow n a b)
  = let flow' = augment_edge flow cap n u v delta in
    if residual_capacity cap flow n u v > 0 then
      // Forward: set flow n u v (get flow n u v + delta)
      // (a,b) ≠ (u,v) since a ≠ u
      lemma_get_set_other flow n u v (get flow n u v + delta) a b
    else
      // Backward: set flow n v u (get flow n v u - delta)
      // (a,b) ≠ (v,u) since b ≠ u
      lemma_get_set_other flow n v u (get flow n v u - delta) a b

(** For the backward residual: get flow' n b a is unchanged when a ≠ u and b ≠ u *)
let lemma_augment_edge_get_other_sym (flow cap: Seq.seq int)
                                      (n: nat{n > 0 /\ Seq.length flow == n * n /\ Seq.length cap == n * n})
                                      (u v: nat{u < n /\ v < n}) (delta: int)
                                      (a b: nat{a < n /\ b < n})
  : Lemma (requires a <> u /\ b <> u)
          (ensures get (augment_edge flow cap n u v delta) n b a == get flow n b a)
  = let flow' = augment_edge flow cap n u v delta in
    if residual_capacity cap flow n u v > 0 then
      // Forward: set at (u,v). Need (b,a) ≠ (u,v). b ≠ u. ✓
      lemma_get_set_other flow n u v (get flow n u v + delta) b a
    else
      // Backward: set at (v,u). Need (b,a) ≠ (v,u). a ≠ u. ✓
      lemma_get_set_other flow n v u (get flow n v u - delta) b a

(** Key lemma: bottleneck of tail path is unchanged after augmenting first edge,
    when the path has distinct vertices (no repeated vertex). *)
let rec lemma_bottleneck_unchanged
  (cap flow: Seq.seq int) (n: nat{n > 0 /\ Seq.length cap == n * n /\ Seq.length flow == n * n})
  (u: nat{u < n}) (v: nat{v < n}) (delta: int)
  (tail: list nat{Cons? tail /\ (forall (w: nat). L.mem w tail ==> w < n)})
  : Lemma
    (requires not (L.mem u tail) /\ distinct_vertices tail)
    (ensures
      bottleneck_aux cap (augment_edge flow cap n u v delta) n tail ==
      bottleneck_aux cap flow n tail)
    (decreases tail)
  = let flow' = augment_edge flow cap n u v delta in
    match tail with
    | [_] -> ()
    | a :: b :: rest ->
      // a ∈ tail, b ∈ tail, u ∉ tail. So a ≠ u and b ≠ u.
      assert (a <> u);
      assert (b <> u);
      // residual_capacity uses get flow n a b, get cap n a b
      lemma_augment_edge_get_other flow cap n u v delta a b;
      // residual_capacity_backward uses get flow n b a
      lemma_augment_edge_get_other_sym flow cap n u v delta a b;
      // So edge_cap at (a,b) is the same under flow' and flow
      assert (residual_capacity cap flow' n a b == residual_capacity cap flow n a b);
      assert (residual_capacity_backward flow' n a b == residual_capacity_backward flow n a b);
      // Recurse on b :: rest
      assert (not (L.mem u (b :: rest)));
      assert (distinct_vertices (b :: rest));
      lemma_bottleneck_unchanged cap flow n u v delta (b :: rest)
    | [] -> () // impossible due to Cons? precondition

(** Main lemma: Path augmentation preserves valid flow (P0.1.7 + P0.1.8) *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec lemma_augment_preserves_capacity (flow: Seq.seq int) (cap: Seq.seq int)
                                          (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
                                          (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
                                          (bn: int)
  : Lemma
    (requires 
      bn > 0 /\
      bn <= bottleneck cap flow n path /\
      distinct_vertices path /\
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
      let edge_cap = 
        if residual_capacity cap flow n u v > 0 
        then residual_capacity cap flow n u v
        else residual_capacity_backward flow n u v in
      assert (bn <= edge_cap);
      
      let flow' = augment_edge flow cap n u v bn in
      assert (Seq.length flow' == n * n);
      
      // Show flow' maintains capacity for all edges
      let aux (u': nat{u' < n}) (v': nat{v' < n})
        : Lemma (0 <= get flow' n u' v' /\ get flow' n u' v' <= get cap n u' v')
        = if residual_capacity cap flow n u v > 0 then
            if u' = u && v' = v then
              (assert (get flow' n u v == get flow n u v + bn);
               assert (bn <= residual_capacity cap flow n u v);
               assert (get flow n u v + bn <= get cap n u v))
            else
              (// (u',v') ≠ (u,v), so index u'*n+v' ≠ u*n+v
               lemma_get_set_other flow n u v (get flow n u v + bn) u' v';
               assert (get flow' n u' v' == get flow n u' v'))
          else
            if u' = v && v' = u then
              (assert (get flow' n v u == get flow n v u - bn);
               assert (bn <= get flow n v u);
               assert (0 <= get flow n v u - bn))
            else
              (// (u',v') ≠ (v,u), so index u'*n+v' ≠ v*n+u
               lemma_get_set_other flow n v u (get flow n v u - bn) u' v';
               assert (get flow' n u' v' == get flow n u' v'))
      in
      FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux);
      
      // distinct_vertices (u :: v :: rest) gives us: u ∉ (v :: rest), distinct_vertices (v :: rest)
      assert (not (L.mem u (v :: rest)));
      assert (distinct_vertices (v :: rest));
      // By lemma_bottleneck_unchanged: bottleneck of tail is same under flow' as flow
      (if n > 0 then
        lemma_bottleneck_unchanged cap flow n u v bn (v :: rest)
      else ());
      // bn <= bottleneck(full path) = min(edge_cap, bottleneck(tail))
      // so bn <= bottleneck(tail) under original flow = bottleneck(tail) under flow'
      
      lemma_augment_preserves_capacity flow' cap n (v :: rest) bn
    | [] -> ()
#pop-options


(** ========== Helper: augment_aux preserves sums for vertices not on path ========== *)

(** For vertices not on the path, augment_aux doesn't change their flow sums *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec lemma_augment_aux_preserves_vertex_sums
  (flow cap: Seq.seq int) (n: nat{n > 0 /\ Seq.length flow == n * n /\ Seq.length cap == n * n})
  (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
  (bn: int) (w: nat{w < n})
  : Lemma
    (requires not (L.mem w path) /\ distinct_vertices path)
    (ensures
      sum_flow_into (augment_aux flow cap n path bn) n w n == sum_flow_into flow n w n /\
      sum_flow_out (augment_aux flow cap n path bn) n w n == sum_flow_out flow n w n)
    (decreases path)
  = match path with
    | [_] -> () // no augmentation
    | u :: v :: rest ->
      let flow' = augment_edge flow cap n u v bn in
      // w ∉ (u :: v :: rest), so w ≠ u and w ≠ v
      if residual_capacity cap flow n u v > 0 then begin
        // Forward: set flow n u v (get flow n u v + bn)
        lemma_sum_flow_into_update_other flow n u v (get flow n u v + bn) w n;
        lemma_sum_flow_out_update_other flow n u v (get flow n u v + bn) w n
      end else begin
        // Backward: set flow n v u (get flow n v u - bn)
        lemma_sum_flow_into_update_other flow n v u (get flow n v u - bn) w n;
        lemma_sum_flow_out_update_other flow n v u (get flow n v u - bn) w n
      end;
      // After augment_edge: w's sums unchanged
      assert (sum_flow_into flow' n w n == sum_flow_into flow n w n);
      assert (sum_flow_out flow' n w n == sum_flow_out flow n w n);
      // By IH: augment_aux on tail preserves w's sums (w ∉ v :: rest)
      assert (not (L.mem w (v :: rest)));
      assert (distinct_vertices (v :: rest));
      lemma_augment_aux_preserves_vertex_sums flow' cap n (v :: rest) bn w
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
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
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
      bn <= bottleneck cap flow n path /\
      distinct_vertices path /\
      source <> sink)
    (ensures 
      (let flow' = augment_aux flow cap n path bn in
       flow_value flow' n source >= flow_value flow n source + bn))
  = // Path = source :: v :: rest (length >= 2 since source ≠ sink)
    match path with
    | [_] -> () // source = sink, impossible
    | source' :: v :: rest ->
      // Step 1: augment_edge(source, v) changes flow_value by +bn
      let flow_1 = augment_edge flow cap n source' v bn in
      if residual_capacity cap flow n source' v > 0 then begin
        // Forward: flow[source][v] += bn → out(source) += bn, in(source) unchanged
        lemma_sum_flow_out_increase flow n source' v bn n;
        lemma_sum_flow_into_update_other flow n source' v (get flow n source' v + bn) source' n
      end else begin
        // Backward: flow[v][source] -= bn → in(source) -= bn, out(source) unchanged
        lemma_sum_flow_into_increase flow n v source' (-bn) n;
        lemma_sum_flow_out_update_other flow n v source' (get flow n v source' - bn) source' n
      end;
      // After step 1: flow_value(flow_1, source) = flow_value(flow, source) + bn
      assert (flow_value flow_1 n source' >= flow_value flow n source' + bn);
      
      // Step 2: augment_aux(flow_1, v :: rest) doesn't change source's sums
      // because source ∉ (v :: rest) [distinct_vertices]
      lemma_augment_aux_preserves_vertex_sums flow_1 cap n (v :: rest) bn source';
      assert (sum_flow_into (augment_aux flow_1 cap n (v :: rest) bn) n source' n ==
              sum_flow_into flow_1 n source' n);
      assert (sum_flow_out (augment_aux flow_1 cap n (v :: rest) bn) n source' n ==
              sum_flow_out flow_1 n source' n);
      ()
#pop-options


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

(** Conservation lemma for intermediate vertices on the augmenting path.
    For vertex w on the path (w ≠ head, w ≠ last), augmentation preserves
    inflow = outflow because the incoming and outgoing path edges contribute
    equal and opposite changes. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec lemma_augment_aux_conservation
  (flow cap: Seq.seq int) (n: nat{n > 0 /\ Seq.length flow == n * n /\ Seq.length cap == n * n})
  (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
  (bn: int) (w: nat{w < n})
  : Lemma
    (requires
      distinct_vertices path /\
      bn > 0 /\
      bn <= bottleneck_aux cap flow n path /\
      w <> L.hd path /\
      w <> L.last path /\
      sum_flow_into flow n w n == sum_flow_out flow n w n)
    (ensures
      sum_flow_into (augment_aux flow cap n path bn) n w n ==
      sum_flow_out (augment_aux flow cap n path bn) n w n)
    (decreases path)
  = match path with
    | [_] -> ()
    | [u; v] ->
      // w ≠ u (head), w ≠ v (last). w ≠ u, w ≠ v.
      lemma_augment_edge_conservation_other flow cap n u v bn w
    | u :: v :: rest ->
      let flow_1 = augment_edge flow cap n u v bn in
      if w <> v then begin
        // w ≠ u (head) and w ≠ v: augment_edge preserves conservation at w
        lemma_augment_edge_conservation_other flow cap n u v bn w;
        // Apply IH to tail (v :: rest) with flow_1
        // Need: w ≠ hd(v::rest) = v ✓, w ≠ last(v::rest) = last(path) ✓
        // Need: bn <= bottleneck(v::rest) under flow_1
        assert (not (L.mem u (v :: rest)));
        assert (distinct_vertices (v :: rest));
        lemma_bottleneck_unchanged cap flow n u v bn (v :: rest);
        // bottleneck under flow_1 = bottleneck under flow >= bn
        lemma_augment_aux_conservation flow_1 cap n (v :: rest) bn w
      end else begin
        // w = v: the second vertex on the path
        // rest must be non-empty since v ≠ L.last path
        // With fuel 2: L.last (u :: v :: []) = v, but w = v and w ≠ L.last path → contradiction
        match rest with
        | [] -> ()  // vacuously true: precondition contradicts (L.last [u;v] = v = w)
        | w1 :: rest' ->
          // w1 is head of rest, so L.mem w1 rest is true by unfolding
          // and rest ⊆ path so w1 < n
          assert (L.mem w1 (w1 :: rest'));  // trivial
          assert (L.mem w1 (v :: w1 :: rest'));  // L.mem propagation
          
          let flow_2 = augment_edge flow_1 cap n v w1 bn in
          
          // residual_capacity at (v,w1) unchanged from flow to flow_1
          // because v ≠ u and w1 ≠ u (from distinct_vertices)
          lemma_augment_edge_get_other flow cap n u v bn v w1;
          lemma_augment_edge_get_other_sym flow cap n u v bn v w1;
          assert (residual_capacity cap flow_1 n v w1 == residual_capacity cap flow n v w1);
          
          // Track v's sums through both edge augmentations
          if residual_capacity cap flow n u v > 0 then begin
            // Edge 1 forward: in(v) += bn, out(v) unchanged
            lemma_sum_flow_into_increase flow n u v bn n;
            lemma_sum_flow_out_update_other flow n u v (get flow n u v + bn) v n;
            
            if residual_capacity cap flow_1 n v w1 > 0 then begin
              // Edge 2 forward: in(v) unchanged, out(v) += bn
              lemma_sum_flow_into_update_other flow_1 n v w1 (get flow_1 n v w1 + bn) v n;
              lemma_sum_flow_out_increase flow_1 n v w1 bn n
            end else begin
              // Edge 2 backward: in(v) -= bn, out(v) unchanged
              lemma_sum_flow_into_increase flow_1 n w1 v (-bn) n;
              lemma_sum_flow_out_update_other flow_1 n w1 v (get flow_1 n w1 v - bn) v n
            end
          end else begin
            // Edge 1 backward: in(v) unchanged, out(v) -= bn
            lemma_sum_flow_into_update_other flow n v u (get flow n v u - bn) v n;
            lemma_sum_flow_out_increase flow n v u (-bn) n;
            
            if residual_capacity cap flow_1 n v w1 > 0 then begin
              lemma_sum_flow_into_update_other flow_1 n v w1 (get flow_1 n v w1 + bn) v n;
              lemma_sum_flow_out_increase flow_1 n v w1 bn n
            end else begin
              lemma_sum_flow_into_increase flow_1 n w1 v (-bn) n;
              lemma_sum_flow_out_update_other flow_1 n w1 v (get flow_1 n w1 v - bn) v n
            end
          end;
          // In all 4 cases: sum_flow_into(flow_2, v) == sum_flow_out(flow_2, v)
          assert (sum_flow_into flow_2 n v n == sum_flow_out flow_2 n v n);
          
          // Step 3: augment_aux(flow_2, w1 :: rest') doesn't affect v
          // v ∉ (w1 :: rest') from distinct_vertices
          assert (not (L.mem v (w1 :: rest')));
          assert (distinct_vertices (w1 :: rest'));
          lemma_augment_aux_preserves_vertex_sums flow_2 cap n (w1 :: rest') bn v
      end
#pop-options

(** P0.1.7 + P0.1.8: Augmentation preserves valid flow *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let augment_preserves_valid (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                             (source: nat{source < n}) (sink: nat{sink < n})
                             (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
                             (bn: int{bn > 0})
  : Lemma
    (requires 
      valid_flow flow cap source sink /\
      bn <= bottleneck cap flow n path /\
      distinct_vertices path /\
      L.hd path == source /\
      L.last path == sink)
    (ensures valid_flow #n (augment_aux flow cap n path bn) cap source sink)
  = lemma_augment_preserves_capacity flow cap n path bn;
    // Conservation proof via helper lemmas
    let flow' = augment_aux flow cap n path bn in
    let aux (w: nat{w < n /\ w <> source /\ w <> sink})
      : Lemma (sum_flow_into flow' n w n == sum_flow_out flow' n w n)
      = if L.mem w path then
          // w is intermediate (w ≠ source = hd, w ≠ sink = last)
          lemma_augment_aux_conservation flow cap n path bn w
        else
          // w ∉ path: sums unchanged
          lemma_augment_aux_preserves_vertex_sums flow cap n path bn w
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

(** P0.1.9: Augmentation increases flow value *)  
let augment_increases_value (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                             (source: nat{source < n}) (sink: nat{sink < n})
                             (path: list nat{Cons? path /\ L.hd path = source /\ L.last path = sink /\ 
                                             (forall (v: nat). L.mem v path ==> v < n)})
                             (bn: int{bn > 0})
  : Lemma
    (requires 
      valid_flow flow cap source sink /\
      bn <= bottleneck cap flow n path /\
      distinct_vertices path /\
      source <> sink)
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

(* ================================================================
   AUGMENT_EDGE COMMUTATIVITY AND ORDER INDEPENDENCE
   Needed for proving augment_imp (backward walk) = augment_aux (forward walk)
   ================================================================ *)

(** augment_edge only modifies cell (u,v) or (v,u); all other cells unchanged *)
let lemma_augment_edge_only_modifies
  (flow cap: Seq.seq int)
  (n: nat{n > 0 /\ Seq.length flow == n * n /\ Seq.length cap == n * n})
  (u v: nat{u < n /\ v < n}) (delta: int)
  (a b: nat{a < n /\ b < n})
  : Lemma
    (requires (a <> u \/ b <> v) /\ (a <> v \/ b <> u))
    (ensures get (augment_edge flow cap n u v delta) n a b == get flow n a b)
  = lemma_get_set_other flow n u v (get flow n u v + delta) a b;
    lemma_get_set_other flow n v u (get flow n v u - delta) a b

(** residual_capacity at (a,b) is unchanged by augment_edge at (u,v) when
    {a,b} is disjoint from {u,v} in the sense that neither (a,b) nor (b,a)
    overlaps with the cell modified by augment_edge *)
let lemma_augment_edge_residual_unchanged
  (flow cap: Seq.seq int)
  (n: nat{n > 0 /\ Seq.length flow == n * n /\ Seq.length cap == n * n})
  (u v: nat{u < n /\ v < n}) (delta: int)
  (a b: nat{a < n /\ b < n})
  : Lemma
    (requires a <> u /\ a <> v /\ b <> u /\ b <> v)
    (ensures
      residual_capacity cap (augment_edge flow cap n u v delta) n a b ==
      residual_capacity cap flow n a b)
  = lemma_augment_edge_only_modifies flow cap n u v delta a b

(** Commutativity of augment_edge: two edge augmentations can be swapped
    when they modify disjoint matrix cells. This holds when the edges are 
    different as undirected edges: {u1,v1} ≠ {u2,v2}. 
    Adjacent path edges (u,v) and (v,w) satisfy this because u ≠ w. *)
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let lemma_augment_edge_commute
  (flow cap: Seq.seq int)
  (n: nat{n > 0 /\ Seq.length flow == n * n /\ Seq.length cap == n * n})
  (u1 v1 u2 v2: nat{u1 < n /\ v1 < n /\ u2 < n /\ v2 < n})
  (delta: int)
  : Lemma
    (requires
      // Edges are different as undirected edges: {u1,v1} ≠ {u2,v2}
      ~(u1 = u2 /\ v1 = v2) /\ ~(u1 = v2 /\ v1 = u2))
    (ensures
      augment_edge (augment_edge flow cap n u1 v1 delta) cap n u2 v2 delta ==
      augment_edge (augment_edge flow cap n u2 v2 delta) cap n u1 v1 delta)
  = let f1 = augment_edge flow cap n u1 v1 delta in
    let f2 = augment_edge flow cap n u2 v2 delta in
    let f12 = augment_edge f1 cap n u2 v2 delta in
    let f21 = augment_edge f2 cap n u1 v1 delta in
    // ae1 modifies cell (u1,v1) or (v1,u1). ae2 modifies cell (u2,v2) or (v2,u2).
    // Since {u1,v1} ≠ {u2,v2} as undirected edges, these cells are disjoint.
    // So each ae sees the same flow values regardless of order.
    let aux (i: nat{i < n * n})
      : Lemma (Seq.index f12 i == Seq.index f21 i)
      = let a = i / n in
        let b = i % n in
        if a < n && b < n then begin
          if (a = u1 && b = v1) || (a = v1 && b = u1) then begin
            // Cell (a,b) affected by ae1, NOT by ae2.
            // ae2 doesn't modify (u1,v1) or (v1,u1):
            lemma_augment_edge_only_modifies flow cap n u2 v2 delta u1 v1;
            lemma_augment_edge_only_modifies flow cap n u2 v2 delta v1 u1;
            // So f2[u1,v1] = flow[u1,v1] and f2[v1,u1] = flow[v1,u1]
            // → residual(f2, u1, v1) = residual(flow, u1, v1) → same branch
            // → f1[a,b] = ae1(flow)[a,b] = ae1(f2)[a,b] = f21[a,b]
            // Also: ae2 doesn't modify (a,b), so f12[a,b] = f1[a,b]
            lemma_augment_edge_only_modifies f1 cap n u2 v2 delta a b
            // So f12[a,b] = f1[a,b] = f21[a,b]
          end
          else if (a = u2 && b = v2) || (a = v2 && b = u2) then begin
            // Symmetric: cell (a,b) affected by ae2, NOT by ae1.
            lemma_augment_edge_only_modifies flow cap n u1 v1 delta u2 v2;
            lemma_augment_edge_only_modifies flow cap n u1 v1 delta v2 u2;
            lemma_augment_edge_only_modifies f2 cap n u1 v1 delta a b
          end
          else begin
            // Cell (a,b) not affected by either ae
            lemma_augment_edge_only_modifies flow cap n u1 v1 delta a b;
            lemma_augment_edge_only_modifies flow cap n u2 v2 delta a b;
            lemma_augment_edge_only_modifies f1 cap n u2 v2 delta a b;
            lemma_augment_edge_only_modifies f2 cap n u1 v1 delta a b
          end
        end
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro f12 f21
#pop-options

(** augment_edge at (u,v) commutes with augment_aux on a remaining path,
    when u does not appear in the remaining path (simple path property).
    v may appear in rest (as its head), but that's fine because
    edges in rest don't involve u, so {u,v} ≠ {a,b} for any edge (a,b) in rest. *)
#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
let rec lemma_augment_edge_commutes_with_aux
  (flow cap: Seq.seq int)
  (n: nat{n > 0 /\ Seq.length flow == n * n /\ Seq.length cap == n * n})
  (u v: nat{u < n /\ v < n})
  (delta: int)
  (rest: list nat{Cons? rest /\ (forall (w: nat). L.mem w rest ==> w < n)})
  : Lemma
    (requires
      not (L.mem u rest) /\
      distinct_vertices rest)
    (ensures
      augment_aux (augment_edge flow cap n u v delta) cap n rest delta ==
      augment_edge (augment_aux flow cap n rest delta) cap n u v delta)
    (decreases rest)
  = match rest with
    | [_] -> ()
    | a :: b :: tl ->
      // Edge (a,b) in rest. u ∉ rest so u≠a and u≠b.
      // {u,v} ≠ {a,b}: since u≠a and u≠b, neither (u=a∧v=b) nor (u=b∧v=a).
      assert (~(u = a /\ v = b));
      assert (~(u = b /\ v = a));
      lemma_augment_edge_commute flow cap n u v a b delta;
      let flow_ab = augment_edge flow cap n a b delta in
      lemma_augment_edge_commutes_with_aux flow_ab cap n u v delta (b :: tl)
#pop-options

(** Key lemma: the first edge of augment_aux can be deferred to the end.
    augment_aux [u, v, ...rest] = ae(augment_aux [v, ...rest], u, v, delta)
    This follows from augment_edge at (u,v) commuting with augment_aux on rest,
    since u does not appear in rest (simple path). *)
#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
let lemma_augment_aux_first_last
  (flow cap: Seq.seq int)
  (n: nat{n > 0 /\ Seq.length flow == n * n /\ Seq.length cap == n * n})
  (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
  (delta: int)
  : Lemma
    (requires distinct_vertices path /\ L.length path >= 2)
    (ensures
      (match path with
       | u :: v :: rest ->
         augment_aux flow cap n path delta ==
         augment_edge (augment_aux flow cap n (v :: rest) delta) cap n u v delta
       | _ -> True))
  = match path with
    | u :: v :: rest ->
      let tail = v :: rest in
      if L.length tail >= 2 then
        lemma_augment_edge_commutes_with_aux flow cap n u v delta tail
      else ()
    | _ -> ()
#pop-options

(** Helper: L.init preserves distinct_vertices and membership subset *)
let rec lemma_init_preserves_distinct_vertices (l: list nat{Cons? l})
  : Lemma (requires distinct_vertices l)
          (ensures distinct_vertices (L.init l) /\
                   (forall v. L.mem v (L.init l) ==> L.mem v l))
          (decreases l)
  = match l with
    | [_] -> ()
    | _ :: rest -> lemma_init_preserves_distinct_vertices rest

(** Process the last edge first: for a simple path,
    augment_aux flow path = augment_aux (ae flow last_edge) init_path.
    This is the key for connecting augment_imp (backward walk) to augment_aux. *)
#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
let rec lemma_augment_aux_last_first
  (flow cap: Seq.seq int)
  (n: nat{n > 0 /\ Seq.length flow == n * n /\ Seq.length cap == n * n})
  (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
  (delta: int)
  : Lemma
    (requires distinct_vertices path /\ L.length path >= 2)
    (ensures
      (let last = L.last path in
       let init = L.init path in
       L.length init >= 1 /\
       Cons? init /\
       (forall (v: nat). L.mem v init ==> v < n) /\
       last < n /\
       (L.length init >= 2 ==>
         (let second_last = L.last init in
          second_last < n /\
          augment_aux flow cap n path delta ==
          augment_aux (augment_edge flow cap n second_last last delta) cap n init delta))))
    (decreases L.length path)
  = L.append_init_last path;
    L.append_mem (L.init path) [L.last path] (L.last path);
    match path with
    | [u; v] -> ()  // ae(flow, u, v) on both sides
    | u :: v :: w :: rest ->
      lemma_augment_aux_first_last flow cap n path delta;
      lemma_augment_aux_last_first flow cap n (v :: w :: rest) delta;
      let last = L.last path in
      let inner_init = L.init (v :: w :: rest) in
      L.append_init_last (v :: w :: rest);
      lemma_init_preserves_distinct_vertices (v :: w :: rest);
      L.append_init_last inner_init;
      L.append_mem (L.init inner_init) [L.last inner_init] (L.last inner_init);
      let sl = L.last inner_init in
      let flow_sl_last = augment_edge flow cap n sl last delta in
      assert (Cons? inner_init);
      assert (L.hd inner_init = v);
      // u :: inner_init = L.init path, which has distinct_vertices
      lemma_init_preserves_distinct_vertices path;
      lemma_augment_aux_first_last flow_sl_last cap n (u :: inner_init) delta;
      ()
    | _ -> ()
#pop-options
