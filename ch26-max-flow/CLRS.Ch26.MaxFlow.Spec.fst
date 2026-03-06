module CLRS.Ch26.MaxFlow.Spec

open FStar.Mul
open FStar.List.Tot

module Seq = FStar.Seq
module L = FStar.List.Tot

(*
   Pure F* Specification for Ford-Fulkerson/Edmonds-Karp Max Flow Algorithm
   Based on CLRS §26.2-26.3
   
   This module defines the mathematical foundations for max flow:
   - Flow network representation (capacity matrix, flow matrix)
   - Flow validity properties (capacity constraint, flow conservation)
   - Residual graphs and augmenting paths
   - Ford-Fulkerson augmentation
   - Cut definitions (s-t cut, cut capacity, net flow across cut)
   
   Proofs are in separate modules:
   - Augmentation lemmas: CLRS.Ch26.MaxFlow.Lemmas
   - Max-flow min-cut theorem: CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut
*)

(** 1. Capacity matrix: n×n matrix stored as flat sequence *)
let capacity_matrix (n: nat) = s:Seq.seq int{Seq.length s == n * n}

(** 2. Flow matrix: n×n matrix stored as flat sequence *)
let flow_matrix (n: nat) = s:Seq.seq int{Seq.length s == n * n}

(** 3. Matrix indexing: get element at (u,v) in n×n matrix *)
let get (m: Seq.seq int) (n: nat{Seq.length m == n * n}) (u: nat{u < n}) (v: nat{v < n}) : int =
  Seq.index m (u * n + v)

(** Helper: set element at (u,v) in n×n matrix *)
let set (m: Seq.seq int) (n: nat{Seq.length m == n * n}) (u: nat{u < n}) (v: nat{v < n}) (x: int)
  : s:Seq.seq int{Seq.length s == n * n}
  = Seq.upd m (u * n + v) x

(** Sum of flow into vertex v from all vertices *)
let rec sum_flow_into (flow: Seq.seq int) (n: nat{Seq.length flow == n * n}) (v: nat{v < n}) (u: nat) 
  : Tot int (decreases u)
  = if u = 0 then 0
    else if u - 1 < n then get flow n (u - 1) v + sum_flow_into flow n v (u - 1)
    else sum_flow_into flow n v (u - 1)

(** Sum of flow out of vertex v to all vertices *)
let rec sum_flow_out (flow: Seq.seq int) (n: nat{Seq.length flow == n * n}) (v: nat{v < n}) (w: nat)
  : Tot int (decreases w)
  = if w = 0 then 0
    else if w - 1 < n then get flow n v (w - 1) + sum_flow_out flow n v (w - 1)
    else sum_flow_out flow n v (w - 1)

(** 4. Valid flow: satisfies capacity constraint and flow conservation (CLRS Definition 26.1) *)
let valid_flow (#n: nat) (flow: flow_matrix n) (cap: capacity_matrix n) (source: nat{source < n}) (sink: nat{sink < n}) : prop =
  // Capacity constraint: 0 ≤ f(u,v) ≤ c(u,v) for all u,v
  (forall (u: nat{u < n}) (v: nat{v < n}). 
    0 <= get flow n u v /\ get flow n u v <= get cap n u v) /\
  // Flow conservation: Σ f(v,u) = Σ f(u,v) for all u ≠ source, sink
  (forall (u: nat{u < n /\ u <> source /\ u <> sink}).
    sum_flow_into flow n u n == sum_flow_out flow n u n)

(** 5. Flow value: |f| = Σ_v f(source,v) - Σ_v f(v,source) (CLRS page 710) *)
let flow_value (flow: Seq.seq int) (n: nat{Seq.length flow == n * n}) (source: nat{source < n}) : int =
  sum_flow_out flow n source n - sum_flow_into flow n source n

(** 6. Residual capacity: c_f(u,v) = c(u,v) - f(u,v) (CLRS Definition 26.2) 
    Note: In the residual graph, we also have backward edges with capacity f(u,v).
    For simplicity, this function returns the forward residual capacity. *)
let residual_capacity (cap: Seq.seq int) (flow: Seq.seq int) 
                      (n: nat{Seq.length cap == n * n /\ Seq.length flow == n * n}) 
                      (u: nat{u < n}) (v: nat{v < n}) : int =
  get cap n u v - get flow n u v

(** Residual capacity for backward edges: f(u,v) *)
let residual_capacity_backward (flow: Seq.seq int)
                               (n: nat{Seq.length flow == n * n})
                               (u: nat{u < n}) (v: nat{v < n}) : int =
  get flow n v u  // flow from v to u gives backward capacity from u to v

(** Check if edge (u,v) has positive residual capacity (forward or backward) *)
let has_residual_capacity (cap: Seq.seq int) (flow: Seq.seq int)
                          (n: nat{Seq.length cap == n * n /\ Seq.length flow == n * n})
                          (u: nat{u < n}) (v: nat{v < n}) : bool =
  residual_capacity cap flow n u v > 0 || residual_capacity_backward flow n u v > 0

(** 7. Augmenting path: a path in the residual graph G_f from source to sink
    Represented as a list of vertices [v0; v1; ...; vk] where v0 = source, vk = sink,
    and each consecutive pair has positive residual capacity. *)
type augmenting_path (cap: Seq.seq int) (flow: Seq.seq int) (n: nat{Seq.length cap == n * n /\ Seq.length flow == n * n})
                     (source: nat{source < n}) (sink: nat{sink < n}) =
  path:list nat{
    Cons? path /\  // Non-empty path
    L.hd path == source /\  // Path starts at source
    L.last path == sink /\  // Path ends at sink
    // All vertices in path are valid
    (forall (v: nat). L.mem v path ==> v < n)
  }

(** 8. Bottleneck: minimum residual capacity along a path (CLRS page 715) *)
let rec bottleneck_aux (cap: Seq.seq int) (flow: Seq.seq int)
                       (n: nat{Seq.length cap == n * n /\ Seq.length flow == n * n})
                       (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
  : Tot int (decreases path)
  = match path with
    | [v] -> FStar.Int.max_int 32  // Single vertex, no edge
    | u :: v :: rest ->
      let edge_capacity = 
        if residual_capacity cap flow n u v > 0 
        then residual_capacity cap flow n u v
        else residual_capacity_backward flow n u v in
      let rest_capacity = bottleneck_aux cap flow n (v :: rest) in
      if edge_capacity < rest_capacity then edge_capacity else rest_capacity
    | [] -> FStar.Int.max_int 32  // Should not happen due to precondition

let bottleneck (cap: Seq.seq int) (flow: Seq.seq int)
               (n: nat{Seq.length cap == n * n /\ Seq.length flow == n * n})
               (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)}) : int =
  bottleneck_aux cap flow n path

(** Helper: augment flow along a single edge by delta *)
let augment_edge (flow: Seq.seq int) (cap: Seq.seq int)
                 (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
                 (u: nat{u < n}) (v: nat{v < n}) (delta: int)
  : s:Seq.seq int{Seq.length s == n * n}
  = if residual_capacity cap flow n u v > 0 then
      // Forward edge: increase flow from u to v
      set flow n u v (get flow n u v + delta)
    else
      // Backward edge: decrease flow from v to u
      set flow n v u (get flow n v u - delta)

(** 9. Augment flow along path by bottleneck amount (CLRS page 715) *)
let rec augment_aux (flow: Seq.seq int) (cap: Seq.seq int)
                    (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
                    (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
                    (bn: int)
  : Tot (s:Seq.seq int{Seq.length s == n * n}) (decreases path)
  = match path with
    | [v] -> flow  // Single vertex, no augmentation
    | u :: v :: rest ->
      let flow' = augment_edge flow cap n u v bn in
      augment_aux flow' cap n (v :: rest) bn
    | [] -> flow  // Should not happen

let augment (#n: nat) (flow: flow_matrix n) (cap: capacity_matrix n)
            (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
            (bn: int)
  : s:Seq.seq int{Seq.length s == n * n}
  = augment_aux flow cap n path bn

(** Helper: check if all vertices in path are within bounds *)
let rec all_vertices_in_bounds (path: list nat) (n: nat) : Tot bool (decreases path) =
  match path with
  | [] -> true
  | hd :: tl -> hd < n && all_vertices_in_bounds tl n

(** Lemma: all_vertices_in_bounds implies the logical property *)
let rec lemma_all_vertices_in_bounds (path: list nat) (n: nat)
  : Lemma (requires all_vertices_in_bounds path n)
          (ensures forall (v: nat). L.mem v path ==> v < n)
          (decreases path)
  = match path with
    | [] -> ()
    | hd :: tl -> lemma_all_vertices_in_bounds tl n

(** Simple path: no vertex appears more than once (required for augmentation proofs) *)
let rec distinct_vertices (path: list nat) : Tot bool (decreases path) =
  match path with
  | [] -> true
  | x :: rest -> not (L.mem x rest) && distinct_vertices rest

(** Lemma: distinct_vertices (u :: v :: rest) implies u does not appear in (v :: rest) *)
let lemma_distinct_head (u: nat) (tl: list nat)
  : Lemma (requires distinct_vertices (u :: tl))
          (ensures not (L.mem u tl) /\ distinct_vertices tl)
  = ()

(** Lemma: distinct_vertices of a cons implies distinct tail *)
let lemma_distinct_tail (x: nat) (rest: list nat)
  : Lemma (requires distinct_vertices (x :: rest))
          (ensures distinct_vertices rest)
  = ()

(** 10. Ford-Fulkerson step: perform one augmentation if path exists *)
let ford_fulkerson_step (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                        (source: nat{source < n}) (sink: nat{sink < n})
                        (path_opt: option (list nat))
  : option (flow_matrix n)
  = match path_opt with
    | None -> None  // No augmenting path found
    | Some path ->
      if Cons? path && L.hd path = source && L.last path = sink &&
         all_vertices_in_bounds path n then
        (lemma_all_vertices_in_bounds path n;
         let bn = bottleneck cap flow n path in
         if bn > 0 then
           Some (augment flow cap path bn)
         else None)
      else None

(** 11. Ford-Fulkerson algorithm: iterate augmentation until no path exists 
    This is a simplified version that takes a list of paths (computed externally).
    A full implementation would compute BFS-based augmenting paths (Edmonds-Karp). *)
let rec ford_fulkerson (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                       (source: nat{source < n}) (sink: nat{sink < n})
                       (paths: list (option (list nat)))
  : Tot (flow_matrix n) (decreases paths)
  = match paths with
    | [] -> flow  // No more paths
    | path_opt :: rest ->
      match ford_fulkerson_step cap flow source sink path_opt with
      | None -> flow  // No augmentation possible, done
      | Some flow' -> ford_fulkerson cap flow' source sink rest

(** Alternative: Ford-Fulkerson with fuel-based termination *)
let rec ford_fulkerson_fuel (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                            (source: nat{source < n}) (sink: nat{sink < n})
                            (find_path: capacity_matrix n -> flow_matrix n -> nat -> nat -> 
                                        option (path:list nat{Cons? path ==> (forall (v: nat). L.mem v path ==> v < n)}))
                            (fuel: nat)
  : Tot (flow_matrix n) (decreases fuel)
  = if fuel = 0 then flow
    else
      match find_path cap flow source sink with
      | None -> flow  // No augmenting path, done
      | Some path ->
        if Cons? path then
          (let bn = bottleneck cap flow n path in
           if bn > 0 then
             let flow' = augment flow cap path bn in
             ford_fulkerson_fuel cap flow' source sink find_path (fuel - 1)
           else flow)
        else flow

(** 12. Key lemma: augmenting along a valid path preserves flow validity
    PROOF: See CLRS.Ch26.MaxFlow.Lemmas.augment_preserves_valid (fully proven, zero assumes) *)
(* Removed: lemma body was a forward declaration with assume.
   The actual proof lives in CLRS.Ch26.MaxFlow.Lemmas which has full proofs
   for capacity constraints and flow conservation under augmentation. *)

(** 13. Key lemma: augmenting strictly increases flow value (when path is source-sink)
    PROOF: See CLRS.Ch26.MaxFlow.Lemmas.augment_increases_value (fully proven, zero assumes) *)
(* Removed: lemma body was a forward declaration with assume.
   The actual proof lives in CLRS.Ch26.MaxFlow.Lemmas using the fact that
   the first edge augmentation changes flow_value by +bn and subsequent
   augmentations don't affect the source vertex's sums (distinct_vertices). *)

(** Helper lemma: zero flow is valid *)
let rec lemma_sum_flow_into_zero (n: nat) (v: nat{v < n}) (k: nat)
  : Lemma (ensures sum_flow_into (Seq.create (n * n) 0) n v k == 0)
          (decreases k)
  = if k = 0 then ()
    else if k - 1 < n then lemma_sum_flow_into_zero n v (k - 1)
    else lemma_sum_flow_into_zero n v (k - 1)

let rec lemma_sum_flow_out_zero (n: nat) (v: nat{v < n}) (k: nat)
  : Lemma (ensures sum_flow_out (Seq.create (n * n) 0) n v k == 0)
          (decreases k)
  = if k = 0 then ()
    else if k - 1 < n then lemma_sum_flow_out_zero n v (k - 1)
    else lemma_sum_flow_out_zero n v (k - 1)

let zero_flow_valid (#n: nat) (cap: capacity_matrix n) (source: nat{source < n}) (sink: nat{sink < n})
  : Lemma
    (requires forall (i: nat). i < n * n ==> Seq.index cap i >= 0)
    (ensures (let flow = Seq.create (n * n) 0 in
              valid_flow flow cap source sink))
  = let flow = Seq.create (n * n) 0 in
    // Capacity constraint: 0 <= 0 <= c(u,v) for all edges (trivial)
    assert (forall (u: nat{u < n}) (v: nat{v < n}). 
             0 <= get flow n u v /\ get flow n u v <= get cap n u v);
    // Flow conservation: inflow = outflow = 0 for all intermediate vertices
    let aux (u: nat{u < n /\ u <> source /\ u <> sink})
      : Lemma (sum_flow_into flow n u n == sum_flow_out flow n u n)
      = lemma_sum_flow_into_zero n u n;
        lemma_sum_flow_out_zero n u n
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

(** Helper lemma: flow value of zero flow is zero *)
let zero_flow_value (n: nat{n > 0}) (source: nat{source < n})
  : Lemma
    (ensures (let flow = Seq.create (n * n) 0 in
              flow_value flow n source == 0))
  = let flow = Seq.create (n * n) 0 in
    lemma_sum_flow_out_zero n source n;
    lemma_sum_flow_into_zero n source n;
    assert (flow_value flow n source == 0 - 0)

(** ========== Max-Flow Min-Cut Definitions and Theorem ========== *)

(** An s-t cut: set S contains source, set T = V \ S contains sink.
    Represented as a boolean function: S(v) = true iff v ∈ S *)
let is_st_cut (s_set: nat -> bool) (n: nat) (source: nat{source < n}) (sink: nat{sink < n}) : prop =
  s_set source == true /\
  s_set sink == false

(** Cut capacity: Σ c(u,v) for u ∈ S, v ∈ T (CLRS Definition 26.4) *)
let rec cut_capacity_inner (cap: Seq.seq int) (n: nat{Seq.length cap == n * n})
                           (s_set: nat -> bool) (u: nat{u < n}) (v: nat)
  : Tot int (decreases v)
  = if v = 0 then 0
    else if v - 1 < n then
      (if not (s_set (v - 1)) then get cap n u (v - 1) else 0) +
      cut_capacity_inner cap n s_set u (v - 1)
    else cut_capacity_inner cap n s_set u (v - 1)

let rec cut_capacity_aux (cap: Seq.seq int) (n: nat{Seq.length cap == n * n})
                         (s_set: nat -> bool) (u: nat)
  : Tot int (decreases u)
  = if u = 0 then 0
    else if u - 1 < n then
      (if s_set (u - 1) then cut_capacity_inner cap n s_set (u - 1) n else 0) +
      cut_capacity_aux cap n s_set (u - 1)
    else cut_capacity_aux cap n s_set (u - 1)

let cut_capacity (#n: nat) (cap: capacity_matrix n) (s_set: nat -> bool) : int =
  cut_capacity_aux cap n s_set n

(** Net flow across a cut: Σ f(u,v) - Σ f(v,u) for u ∈ S, v ∈ T *)
let rec net_flow_inner (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                       (s_set: nat -> bool) (u: nat{u < n}) (v: nat)
  : Tot int (decreases v)
  = if v = 0 then 0
    else if v - 1 < n then
      (if not (s_set (v - 1)) then
        get flow n u (v - 1) - get flow n (v - 1) u
      else 0) +
      net_flow_inner flow n s_set u (v - 1)
    else net_flow_inner flow n s_set u (v - 1)

let rec net_flow_aux (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                     (s_set: nat -> bool) (u: nat)
  : Tot int (decreases u)
  = if u = 0 then 0
    else if u - 1 < n then
      (if s_set (u - 1) then net_flow_inner flow n s_set (u - 1) n else 0) +
      net_flow_aux flow n s_set (u - 1)
    else net_flow_aux flow n s_set (u - 1)

let net_flow_across_cut (#n: nat) (flow: flow_matrix n) (s_set: nat -> bool) : int =
  net_flow_aux flow n s_set n

(** No augmenting path exists: every source-to-sink path has bottleneck ≤ 0.
    This is the key precondition of the max-flow min-cut theorem (CLRS Theorem 26.6). *)
let no_augmenting_path (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                        (source: nat{source < n}) (sink: nat{sink < n}) : prop =
  forall (path: list nat).
    Cons? path /\ L.hd path = source /\ L.last path = sink /\
    (forall (v: nat). L.mem v path ==> v < n) ==>
    bottleneck cap flow n path <= 0
