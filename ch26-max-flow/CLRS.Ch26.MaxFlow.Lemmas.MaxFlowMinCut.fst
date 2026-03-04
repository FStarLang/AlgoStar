module CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut

open FStar.Mul
open FStar.List.Tot
open CLRS.Ch26.MaxFlow.Spec

module Seq = FStar.Seq
module L = FStar.List.Tot

(*
   Max-Flow Min-Cut Theorem and supporting lemmas (CLRS Theorem 26.6).

   Key results:
   - CLRS Lemma 26.4: |f| = net flow across any cut
   - CLRS Corollary 26.5: Weak duality |f| ≤ c(S,T)
   - CLRS Theorem 26.6: Max-flow min-cut (strong duality)

   All proofs are complete with zero admits.
   Depends only on Spec definitions (flow, augmentation, cuts).
*)

(** ========== CLRS Lemma 26.4: flow_value = net_flow_across_cut ========== *)

(** S-filtered inner sum: Σ_{v<w, v∈S} (f(u,v) - f(v,u)) *)
let rec ss_inner (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                 (s_set: nat -> bool) (u: nat{u < n}) (w: nat)
  : Tot int (decreases w)
  = if w = 0 then 0
    else if w - 1 < n then
      (if s_set (w - 1) then get flow n u (w - 1) - get flow n (w - 1) u else 0)
      + ss_inner flow n s_set u (w - 1)
    else ss_inner flow n s_set u (w - 1)

(** Splitting: sum_out - sum_in = net_flow_inner + ss_inner *)
let rec lemma_splitting_inner
  (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
  (s_set: nat -> bool) (u: nat{u < n}) (w: nat)
  : Lemma
    (ensures sum_flow_out flow n u w - sum_flow_into flow n u w ==
             net_flow_inner flow n s_set u w + ss_inner flow n s_set u w)
    (decreases w)
  = if w = 0 then ()
    else if w - 1 < n then lemma_splitting_inner flow n s_set u (w - 1)
    else lemma_splitting_inner flow n s_set u (w - 1)

(** Sum of (out - in) over S vertices *)
let rec sum_excess_S (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                     (s_set: nat -> bool) (k: nat)
  : Tot int (decreases k)
  = if k = 0 then 0
    else if k - 1 < n && s_set (k - 1) then
      (sum_flow_out flow n (k - 1) n - sum_flow_into flow n (k - 1) n)
      + sum_excess_S flow n s_set (k - 1)
    else sum_excess_S flow n s_set (k - 1)

(** Sum of ss_inner over S vertices *)
let rec ss_outer (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                 (s_set: nat -> bool) (k: nat)
  : Tot int (decreases k)
  = if k = 0 then 0
    else if k - 1 < n && s_set (k - 1) then
      ss_inner flow n s_set (k - 1) n + ss_outer flow n s_set (k - 1)
    else ss_outer flow n s_set (k - 1)

(** Aggregation: sum_excess_S = net_flow_aux + ss_outer *)
let rec lemma_aggregation
  (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
  (s_set: nat -> bool) (k: nat)
  : Lemma
    (ensures sum_excess_S flow n s_set k ==
             net_flow_aux flow n s_set k + ss_outer flow n s_set k)
    (decreases k)
  = if k = 0 then ()
    else if k - 1 < n && s_set (k - 1) then begin
      lemma_aggregation flow n s_set (k - 1);
      lemma_splitting_inner flow n s_set (k - 1) n
    end else
      lemma_aggregation flow n s_set (k - 1)

(** Conservation collapse: sum_excess_S(n) = flow_value *)
#push-options "--z3rlimit 30"
let rec lemma_conservation_collapse
  (flow cap: Seq.seq int) (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
  (source: nat{source < n}) (sink: nat{sink < n}) (s_set: nat -> bool) (k: nat)
  : Lemma
    (requires valid_flow #n flow cap source sink /\ is_st_cut s_set n source sink)
    (ensures sum_excess_S flow n s_set k ==
             (if source < k then sum_flow_out flow n source n - sum_flow_into flow n source n else 0))
    (decreases k)
  = if k = 0 then ()
    else begin
      lemma_conservation_collapse flow cap n source sink s_set (k - 1);
      if k - 1 < n && s_set (k - 1) && k - 1 <> source then
        assert (k - 1 <> sink)
    end
#pop-options

(** ---- S×S cancellation ---- *)

(** Count elements in S below k *)
let rec count_S (s_set: nat -> bool) (k: nat) : Tot nat (decreases k)
  = if k = 0 then 0
    else (if s_set (k - 1) then 1 else 0) + count_S s_set (k - 1)

(** Finding an element in S *)
let rec find_S (s_set: nat -> bool) (k: nat{count_S s_set k > 0})
  : Tot (a:nat{a < k /\ s_set a}) (decreases k)
  = if s_set (k - 1) then k - 1
    else find_S s_set (k - 1)

(** count_S is positive when an element exists *)
let rec lemma_count_S_pos (s_set: nat -> bool) (a: nat) (k: nat)
  : Lemma (requires a < k /\ s_set a)
          (ensures count_S s_set k > 0)
          (decreases k)
  = if k - 1 = a then () else lemma_count_S_pos s_set a (k - 1)

(** Removing element decreases count *)
let rec lemma_count_S_remove (s_set: nat -> bool) (a: nat{s_set a}) (k: nat)
  : Lemma (ensures count_S (fun v -> s_set v && v <> a) k ==
                   count_S s_set k - (if a < k then 1 else 0))
          (decreases k)
  = if k = 0 then ()
    else lemma_count_S_remove s_set a (k - 1)

(** Extract element a from ss_inner: ss_inner(u,w,S) = ss_inner(u,w,S\{a}) + contribution of a *)
let rec lemma_extract_from_ss_inner
  (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
  (s_set: nat -> bool) (a: nat{a < n /\ s_set a}) (u: nat{u < n}) (w: nat)
  : Lemma
    (ensures ss_inner flow n s_set u w ==
             ss_inner flow n (fun v -> s_set v && v <> a) u w +
             (if a < w then get flow n u a - get flow n a u else 0))
    (decreases w)
  = if w = 0 then ()
    else if w - 1 < n then
      lemma_extract_from_ss_inner flow n s_set a u (w - 1)
    else
      lemma_extract_from_ss_inner flow n s_set a u (w - 1)

(** Column-sum of differences: Σ_{u<k, u∈S'} (f(u,a) - f(a,u)) *)
let rec col_diff (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                 (s_set: nat -> bool) (a: nat{a < n}) (k: nat)
  : Tot int (decreases k)
  = if k = 0 then 0
    else if k - 1 < n && s_set (k - 1) then
      (get flow n (k - 1) a - get flow n a (k - 1)) + col_diff flow n s_set a (k - 1)
    else col_diff flow n s_set a (k - 1)

(** ss_inner(a, w, S') = -(col_diff S' a w) — antisymmetric cancellation *)
let rec lemma_ss_inner_neg_col_diff
  (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
  (s_set: nat -> bool) (a: nat{a < n}) (w: nat)
  : Lemma (ensures ss_inner flow n s_set a w == -(col_diff flow n s_set a w))
          (decreases w)
  = if w = 0 then ()
    else if w - 1 < n then lemma_ss_inner_neg_col_diff flow n s_set a (w - 1)
    else lemma_ss_inner_neg_col_diff flow n s_set a (w - 1)

(** Decomposition: ss_outer(n,S) = ss_outer(n,S') + ss_inner(a,n,S') + col_diff(S',a,n) *)
#push-options "--z3rlimit 40"
let rec lemma_ss_outer_decompose
  (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
  (s_set: nat -> bool) (a: nat{a < n /\ s_set a}) (k: nat)
  : Lemma
    (ensures (let s' = (fun v -> s_set v && v <> a) in
              ss_outer flow n s_set k ==
              ss_outer flow n s' k +
              (if a < k then ss_inner flow n s' a n else 0) +
              col_diff flow n s' a k))
    (decreases k)
  = let s' = (fun v -> s_set v && v <> a) in
    if k = 0 then ()
    else begin
      lemma_ss_outer_decompose flow n s_set a (k - 1);
      if k - 1 < n && s_set (k - 1) then begin
        lemma_extract_from_ss_inner flow n s_set a (k - 1) n;
        if k - 1 = a then
          // u = a: ss_inner(a,n,S) = ss_inner(a,n,S') + (f(a,a)-f(a,a)) = ss_inner(a,n,S')
          ()
        else
          // u ≠ a, u ∈ S: ss_inner(u,n,S) = ss_inner(u,n,S') + (f(u,a)-f(a,u))
          ()
      end
    end
#pop-options

(** Main cancellation: ss_outer(n) = 0 by induction on |S| *)
#push-options "--z3rlimit 40"
let rec lemma_ss_outer_zero
  (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
  (s_set: nat -> bool)
  : Lemma (ensures ss_outer flow n s_set n == 0)
          (decreases (count_S s_set n))
  = if count_S s_set n = 0 then begin
      // S is empty: no terms in outer sum
      let rec aux (j: nat) : Lemma (ensures ss_outer flow n s_set j == 0) (decreases j)
        = if j = 0 then ()
          else begin
            aux (j - 1);
            if j - 1 < n && s_set (j - 1) then
              lemma_count_S_pos s_set (j - 1) n
          end
      in aux n
    end else begin
      let a = find_S s_set n in
      let s' = (fun v -> s_set v && v <> a) in
      lemma_count_S_remove s_set a n;
      // IH: ss_outer(n, S') = 0
      lemma_ss_outer_zero flow n s';
      // Decompose: ss_outer(n,S) = ss_outer(n,S') + ss_inner(a,n,S') + col_diff(S',a,n)
      lemma_ss_outer_decompose flow n s_set a n;
      // ss_inner(a,n,S') = -col_diff(S',a,n)
      lemma_ss_inner_neg_col_diff flow n s' a n
    end
#pop-options

(** Helper: each term f(u,v)-f(v,u) ≤ c(u,v) by capacity constraints *)
let rec lemma_net_flow_inner_le_cut_inner
  (flow cap: Seq.seq int)
  (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
  (s_set: nat -> bool) (u: nat{u < n}) (v: nat)
  : Lemma
    (requires forall (a: nat{a < n}) (b: nat{b < n}).
      0 <= get flow n a b /\ get flow n a b <= get cap n a b)
    (ensures net_flow_inner flow n s_set u v <= cut_capacity_inner cap n s_set u v)
    (decreases v)
  = if v = 0 then ()
    else if v - 1 < n then
      lemma_net_flow_inner_le_cut_inner flow cap n s_set u (v - 1)
    else
      lemma_net_flow_inner_le_cut_inner flow cap n s_set u (v - 1)

(** Helper: Σ_{u∈S} net_flow_inner(u) ≤ Σ_{u∈S} cut_capacity_inner(u) *)
let rec lemma_net_flow_aux_le_cut_aux
  (flow cap: Seq.seq int)
  (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
  (s_set: nat -> bool) (u: nat)
  : Lemma
    (requires forall (a: nat{a < n}) (b: nat{b < n}).
      0 <= get flow n a b /\ get flow n a b <= get cap n a b)
    (ensures net_flow_aux flow n s_set u <= cut_capacity_aux cap n s_set u)
    (decreases u)
  = if u = 0 then ()
    else if u - 1 < n then begin
      lemma_net_flow_aux_le_cut_aux flow cap n s_set (u - 1);
      if s_set (u - 1) then
        lemma_net_flow_inner_le_cut_inner flow cap n s_set (u - 1) n
    end else
      lemma_net_flow_aux_le_cut_aux flow cap n s_set (u - 1)

(** net_flow_across_cut ≤ cut_capacity *)
let lemma_net_flow_le_cut_capacity
  (#n: nat) (flow: flow_matrix n) (cap: capacity_matrix n) (s_set: nat -> bool)
  : Lemma
    (requires forall (a: nat{a < n}) (b: nat{b < n}).
      0 <= get flow n a b /\ get flow n a b <= get cap n a b)
    (ensures net_flow_across_cut flow s_set <= cut_capacity cap s_set)
  = lemma_net_flow_aux_le_cut_aux flow cap n s_set n

(** CLRS Lemma 26.4: |f| = net flow across any cut *)
let lemma_flow_value_eq_net_flow
  (#n: nat) (flow: flow_matrix n) (cap: capacity_matrix n)
  (source: nat{source < n}) (sink: nat{sink < n}) (s_set: nat -> bool)
  : Lemma
    (requires valid_flow flow cap source sink /\ is_st_cut s_set n source sink)
    (ensures flow_value flow n source == net_flow_across_cut flow s_set)
  = // flow_value = sum_excess_S(n) by conservation
    lemma_conservation_collapse flow cap n source sink s_set n;
    // sum_excess_S(n) = net_flow_aux(n) + ss_outer(n) by aggregation
    lemma_aggregation flow n s_set n;
    // ss_outer(n) = 0 by S×S cancellation
    lemma_ss_outer_zero flow n s_set

(** Weak duality: |f| ≤ c(S,T) for any valid flow and s-t cut (CLRS Corollary 26.5) *)
let weak_duality (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                  (source: nat{source < n}) (sink: nat{sink < n})
                  (s_set: nat -> bool)
  : Lemma
    (requires valid_flow flow cap source sink /\
              is_st_cut s_set n source sink)
    (ensures flow_value flow n source <= cut_capacity cap s_set)
  = lemma_flow_value_eq_net_flow flow cap source sink s_set;
    lemma_net_flow_le_cut_capacity flow cap s_set

(** ========== CLRS Theorem 26.6: Max-flow min-cut theorem ========== *)

(** Structural check that all consecutive pairs have positive residual *)
let rec all_edges_traversable (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (p: list nat) : prop =
  match p with
  | [] | [_] -> True
  | u :: v :: rest ->
    u < n /\ v < n /\ has_residual_capacity cap flow n u v /\
    all_edges_traversable cap flow (v :: rest)

(** Path in residual graph *)
let path_in_residual (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source target: nat{source < n /\ target < n}) (p: list nat) : prop =
  Cons? p /\ L.hd p = source /\ L.last p = target /\
  (forall (w: nat). L.mem w p ==> w < n) /\
  all_edges_traversable cap flow p

(** Reachable from source in the residual graph *)
let reachable_in_Gf (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source v: nat{source < n /\ v < n}) : prop =
  exists (p: list nat). path_in_residual cap flow source v p

(** Appending a traversable edge preserves traversability *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let rec lemma_append_edge_traversable
  (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (p: list nat) (v: nat{v < n})
  : Lemma
    (requires Cons? p /\ (forall (w: nat). L.mem w p ==> w < n) /\
              all_edges_traversable cap flow p /\
              L.last p < n /\ has_residual_capacity cap flow n (L.last p) v)
    (ensures all_edges_traversable cap flow (L.append p [v]))
    (decreases p)
  = match p with
    | [u] -> ()
    | u :: v' :: rest -> lemma_append_edge_traversable cap flow (v' :: rest) v

(** Path extension: if u reachable and (u,v) traversable, then v reachable *)
let lemma_extend_reachable
  (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source u: nat{source < n /\ u < n}) (v: nat{v < n})
  (p: list nat)
  : Lemma
    (requires path_in_residual cap flow source u p /\
              has_residual_capacity cap flow n u v)
    (ensures reachable_in_Gf cap flow source v)
  = lemma_append_edge_traversable cap flow p v;
    L.lemma_append_last p [v];
    L.append_mem_forall p [v];
    assert (path_in_residual cap flow source v (L.append p [v]))

(** Traversable path implies positive bottleneck *)
let rec lemma_traversable_bottleneck
  (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (p: list nat{Cons? p /\ (forall (w: nat). L.mem w p ==> w < n)})
  : Lemma
    (requires all_edges_traversable cap flow p)
    (ensures bottleneck cap flow n p > 0)
    (decreases p)
  = match p with
    | [v] -> ()
    | u :: v :: rest -> lemma_traversable_bottleneck cap flow (v :: rest)

(** Sink not reachable when no augmenting path exists *)
let lemma_sink_not_reachable
  (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source sink: nat{source < n /\ sink < n}) (p: list nat)
  : Lemma
    (requires
      (forall (path: list nat).
        Cons? path /\ L.hd path = source /\ L.last path = sink /\
        (forall (v: nat). L.mem v path ==> v < n) ==>
        bottleneck cap flow n path <= 0) /\
      path_in_residual cap flow source sink p)
    (ensures False)
  = lemma_traversable_bottleneck cap flow p

(** Saturated edge: if no residual, then f(u,v) = c(u,v) and f(v,u) = 0 *)
let lemma_saturated_edge
  (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source sink: nat{source < n /\ sink < n}) (u v: nat{u < n /\ v < n})
  : Lemma
    (requires valid_flow flow cap source sink /\
              not (has_residual_capacity cap flow n u v))
    (ensures get flow n u v == get cap n u v /\ get flow n v u == 0)
  = ()

(** net_flow_inner = cut_capacity_inner when all S→T edges saturated *)
let rec lemma_saturated_inner
  (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source sink: nat{source < n /\ sink < n})
  (s_set: nat -> bool) (u: nat{u < n}) (w: nat)
  : Lemma
    (requires valid_flow flow cap source sink /\ s_set u == true /\
      (forall (v: nat{v < n}). s_set v == false ==> not (has_residual_capacity cap flow n u v)))
    (ensures net_flow_inner flow n s_set u w == cut_capacity_inner cap n s_set u w)
    (decreases w)
  = if w = 0 then ()
    else if w - 1 < n then begin
      lemma_saturated_inner cap flow source sink s_set u (w - 1);
      if not (s_set (w - 1)) then lemma_saturated_edge cap flow source sink u (w - 1)
    end
    else lemma_saturated_inner cap flow source sink s_set u (w - 1)

(** net_flow_aux = cut_capacity_aux when S→T edges saturated for all u ∈ S *)
let rec lemma_saturated_aux
  (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source sink: nat{source < n /\ sink < n})
  (s_set: nat -> bool) (k: nat)
  : Lemma
    (requires valid_flow flow cap source sink /\
      (forall (u: nat{u < n}). s_set u == true ==>
        (forall (v: nat{v < n}). s_set v == false ==> not (has_residual_capacity cap flow n u v))))
    (ensures net_flow_aux flow n s_set k == cut_capacity_aux cap n s_set k)
    (decreases k)
  = if k = 0 then ()
    else if k - 1 < n then begin
      lemma_saturated_aux cap flow source sink s_set (k - 1);
      if s_set (k - 1) then lemma_saturated_inner cap flow source sink s_set (k - 1) n
    end
    else lemma_saturated_aux cap flow source sink s_set (k - 1)
#pop-options

(** Bounded reachability via mutual recursion (avoids higher-order SMT issues) *)
let rec is_reachable (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source: nat{source < n}) (fuel: nat) (v: nat)
  : Tot bool (decreases %[fuel; (n + 1)])
  = if v >= n then false
    else if v = source then true
    else if fuel = 0 then false
    else check_any_predecessor cap flow source fuel v 0

and check_any_predecessor (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source: nat{source < n}) (fuel: nat{fuel > 0}) (v: nat{v < n /\ v <> source}) (u: nat)
  : Tot bool (decreases %[fuel; n - u])
  = if u >= n then false
    else if is_reachable cap flow source (fuel - 1) u && has_residual_capacity cap flow n u v then true
    else check_any_predecessor cap flow source fuel v (u + 1)

(** check_any_predecessor succeeds when a specific predecessor is reachable *)
let rec lemma_check_any_found (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source: nat{source < n}) (fuel: nat{fuel > 0}) (v: nat{v < n /\ v <> source})
  (u0: nat{u0 < n}) (start: nat)
  : Lemma
    (requires is_reachable cap flow source (fuel - 1) u0 /\
              has_residual_capacity cap flow n u0 v /\ start <= u0)
    (ensures check_any_predecessor cap flow source fuel v start)
    (decreases (n - start))
  = if start >= n then ()
    else if is_reachable cap flow source (fuel - 1) start &&
            has_residual_capacity cap flow n start v then ()
    else if start = u0 then ()
    else lemma_check_any_found cap flow source fuel v u0 (start + 1)

(** check_any_predecessor is monotone in the predecessor reachability *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let rec lemma_check_any_mono (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source: nat{source < n}) (fuel: nat{fuel > 0}) (v: nat{v < n /\ v <> source}) (u: nat)
  : Lemma
    (requires check_any_predecessor cap flow source fuel v u /\
              (forall (w: nat). is_reachable cap flow source (fuel - 1) w ==>
                                is_reachable cap flow source fuel w))
    (ensures check_any_predecessor cap flow source (fuel + 1) v u)
    (decreases (n - u))
  = if u >= n then ()
    else if is_reachable cap flow source (fuel - 1) u && has_residual_capacity cap flow n u v then ()
    else lemma_check_any_mono cap flow source fuel v (u + 1)

(** Reachability is monotone in fuel *)
let rec lemma_reachable_mono (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source: nat{source < n}) (fuel: nat) (v: nat)
  : Lemma
    (requires is_reachable cap flow source fuel v)
    (ensures is_reachable cap flow source (fuel + 1) v)
    (decreases %[fuel; n + 1])
  = if v >= n || v = source then ()
    else if fuel = 0 then ()
    else begin
      let aux (w: nat) : Lemma (requires is_reachable cap flow source (fuel - 1) w)
                                (ensures is_reachable cap flow source fuel w) =
        lemma_reachable_mono cap flow source (fuel - 1) w
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
      lemma_check_any_mono cap flow source fuel v 0
    end

(** Step reachable: if u reachable in fuel-1 and has_residual(u,v), then v reachable in fuel *)
let lemma_step_reachable (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source: nat{source < n}) (fuel: nat{fuel > 0}) (u: nat{u < n}) (v: nat{v < n /\ v <> source})
  : Lemma
    (requires is_reachable cap flow source (fuel - 1) u /\
              has_residual_capacity cap flow n u v)
    (ensures is_reachable cap flow source fuel v)
  = lemma_check_any_found cap flow source fuel v u 0
#pop-options

(** Reachable ⟹ path in residual graph (for bottleneck contradiction) *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let rec lemma_check_any_path (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source: nat{source < n}) (fuel: nat{fuel > 0})
  (v: nat{v < n /\ v <> source}) (u: nat)
  : Lemma
    (requires check_any_predecessor cap flow source fuel v u /\
              (forall (w: nat{w < n}). is_reachable cap flow source (fuel - 1) w ==>
                                       reachable_in_Gf cap flow source w))
    (ensures reachable_in_Gf cap flow source v)
    (decreases (n - u))
  = if u >= n then ()
    else if is_reachable cap flow source (fuel - 1) u && has_residual_capacity cap flow n u v then begin
      let p = FStar.IndefiniteDescription.indefinite_description_ghost
        (list nat) (fun p -> path_in_residual cap flow source u p) in
      lemma_extend_reachable cap flow source u v p
    end
    else lemma_check_any_path cap flow source fuel v (u + 1)

let rec lemma_reachable_implies_path (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source: nat{source < n}) (fuel: nat) (v: nat{v < n})
  : Lemma
    (requires is_reachable cap flow source fuel v)
    (ensures reachable_in_Gf cap flow source v)
    (decreases fuel)
  = if v = source then
      assert (path_in_residual cap flow source source [source])
    else if fuel = 0 then ()
    else begin
      let aux (w: nat{w < n})
        : Lemma (requires is_reachable cap flow source (fuel - 1) w)
                (ensures reachable_in_Gf cap flow source w) =
        lemma_reachable_implies_path cap flow source (fuel - 1) w
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
      lemma_check_any_path cap flow source fuel v 0
    end
#pop-options

(** init preserves traversability *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let rec lemma_init_traversable (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (p: list nat)
  : Lemma
    (requires L.length p > 1 /\ (forall (w: nat). L.mem w p ==> w < n) /\
              all_edges_traversable cap flow p)
    (ensures Cons? (L.init p) /\ all_edges_traversable cap flow (L.init p) /\
             L.hd (L.init p) = L.hd p /\
             (forall (w: nat). L.mem w (L.init p) ==> w < n))
    (decreases p)
  = match p with
    | [u; v] -> ()
    | u :: v :: w :: rest -> lemma_init_traversable cap flow (v :: w :: rest)

(** Last edge of a traversable path *)
let rec lemma_last_edge (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (p: list nat)
  : Lemma
    (requires L.length p > 1 /\ (forall (w: nat). L.mem w p ==> w < n) /\
              all_edges_traversable cap flow p)
    (ensures L.last (L.init p) < n /\ L.last p < n /\
             has_residual_capacity cap flow n (L.last (L.init p)) (L.last p))
    (decreases p)
  = match p with
    | [u; v] -> ()
    | u :: v :: w :: rest -> lemma_last_edge cap flow (v :: w :: rest)
#pop-options

let rec lemma_init_length (#a: Type) (p: list a{Cons? p})
  : Lemma (ensures L.length (L.init p) = L.length p - 1) (decreases p)
  = match p with | [_] -> () | _ :: rest -> lemma_init_length rest

(** Path with ≤ fuel+1 vertices implies is_reachable *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let rec lemma_path_implies_reachable (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source: nat{source < n}) (v: nat{v < n}) (fuel: nat)
  (p: list nat)
  : Lemma
    (requires Cons? p /\ L.hd p = source /\ L.last p = v /\
              (forall (w: nat). L.mem w p ==> w < n) /\
              all_edges_traversable cap flow p /\
              L.length p <= fuel + 1)
    (ensures is_reachable cap flow source fuel v)
    (decreases fuel)
  = if v = source then ()
    else begin
      lemma_init_traversable cap flow p;
      lemma_last_edge cap flow p;
      lemma_init_length p;
      let init_p = L.init p in
      let u = L.last init_p in
      (if u = source then ()
       else lemma_path_implies_reachable cap flow source u (fuel - 1) init_p);
      if v <> source then
        lemma_step_reachable cap flow source fuel u v
    end
#pop-options

(** Path shortening: any path can be shortened to ≤ n vertices
    (by removing cycles via pigeonhole principle). *)

(** Take first k elements of a list *)
let rec take (#a: Type) (k: nat) (l: list a{k <= L.length l})
  : Tot (r: list a{L.length r = k}) (decreases k)
  = if k = 0 then []
    else L.hd l :: take (k - 1) (L.tl l)

(** Drop first k elements of a list *)
let rec drop (#a: Type) (k: nat) (l: list a{k <= L.length l})
  : Tot (r: list a{L.length r = L.length l - k}) (decreases k)
  = if k = 0 then l
    else drop (k - 1) (L.tl l)

(** take preserves traversability *)
let rec lemma_take_traversable (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (k: nat{k > 0}) (p: list nat{k <= L.length p})
  : Lemma
    (requires (forall (w: nat). L.mem w p ==> w < n) /\ all_edges_traversable cap flow p)
    (ensures all_edges_traversable cap flow (take k p) /\
             (forall (w: nat). L.mem w (take k p) ==> w < n))
    (decreases k)
  = if k = 1 then ()
    else match p with
    | u :: v :: rest -> lemma_take_traversable cap flow (k - 1) (v :: rest)

(** drop preserves traversability *)
let rec lemma_drop_traversable (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (k: nat) (p: list nat{k <= L.length p})
  : Lemma
    (requires (forall (w: nat). L.mem w p ==> w < n) /\ all_edges_traversable cap flow p)
    (ensures all_edges_traversable cap flow (drop k p) /\
             (forall (w: nat). L.mem w (drop k p) ==> w < n))
    (decreases k)
  = if k = 0 then ()
    else match p with | u :: rest -> lemma_drop_traversable cap flow (k - 1) rest

(** take k has last element = index k-1 *)
let rec lemma_take_last (k: nat{k > 0}) (l: list nat{k <= L.length l})
  : Lemma (ensures L.last (take k l) = L.index l (k - 1)) (decreases k)
  = if k = 1 then () else lemma_take_last (k - 1) (L.tl l)

(** drop k has head = index k *)
let rec lemma_drop_hd (k: nat) (l: list nat{k < L.length l})
  : Lemma (ensures L.hd (drop k l) = L.index l k) (decreases k)
  = if k = 0 then () else lemma_drop_hd (k - 1) (L.tl l)

(** drop preserves last *)
let rec lemma_drop_last (k: nat) (l: list nat{k < L.length l})
  : Lemma (ensures L.last (drop k l) = L.last l) (decreases k)
  = if k = 0 then () else lemma_drop_last (k - 1) (L.tl l)

(** Concatenation of traversable paths at shared junction vertex *)
let rec lemma_concat_traversable (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (p1 p2: list nat)
  : Lemma
    (requires Cons? p1 /\ Cons? p2 /\
              (forall (w: nat). L.mem w p1 ==> w < n) /\
              (forall (w: nat). L.mem w p2 ==> w < n) /\
              all_edges_traversable cap flow p1 /\
              all_edges_traversable cap flow p2 /\
              L.last p1 = L.hd p2)
    (ensures all_edges_traversable cap flow (L.append (L.init p1) p2) /\
             (forall (w: nat). L.mem w (L.append (L.init p1) p2) ==> w < n))
    (decreases p1)
  = match p1 with
    | [u] -> ()
    | [u; v] -> assert (L.init [u; v] == [u]); assert (L.append [u] p2 == u :: p2)
    | u :: v :: w :: rest -> lemma_concat_traversable cap flow (v :: w :: rest) p2

(** Cycle removal: given a path with repeated vertex at positions i < j,
    remove the cycle p[i+1..j] to get a shorter valid path *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 120"
let lemma_cycle_remove (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source: nat{source < n}) (v: nat{v < n})
  (p: list nat) (i j: nat)
  : Lemma
    (requires Cons? p /\ L.hd p = source /\ L.last p = v /\
              (forall (w: nat). L.mem w p ==> w < n) /\
              all_edges_traversable cap flow p /\
              i < j /\ j < L.length p /\ L.index p i = L.index p j)
    (ensures exists (p': list nat).
        Cons? p' /\ L.hd p' = source /\ L.last p' = v /\
        (forall (w: nat). L.mem w p' ==> w < n) /\
        all_edges_traversable cap flow p' /\
        L.length p' < L.length p)
  = let prefix = take (i + 1) p in
    let suffix = drop j p in
    lemma_take_traversable cap flow (i + 1) p;
    lemma_drop_traversable cap flow j p;
    lemma_take_last (i + 1) p;
    lemma_drop_hd j p;
    assert (L.last prefix = L.hd suffix);
    lemma_concat_traversable cap flow prefix suffix;
    let p' = L.append (L.init prefix) suffix in
    lemma_drop_last j p;
    if i = 0 then begin
      assert (p' == suffix);
      assert (L.hd p' = L.index p j);
      assert (L.index p j = L.index p 0);
      assert (L.index p 0 = source)
    end else begin
      L.append_l_cons (L.hd (L.init prefix)) (L.tl (L.init prefix)) suffix;
      assert (L.hd (L.init prefix) = L.hd prefix);
      L.lemma_append_last (L.init prefix) suffix
    end;
    lemma_init_length prefix;
    L.append_length (L.init prefix) suffix;
    assert (L.length p' = i + (L.length p - j));
    assert (L.length p' < L.length p)
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 120"
let rec lemma_shorten_path (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source: nat{source < n}) (v: nat{v < n})
  (p: list nat)
  : Lemma
    (requires Cons? p /\ L.hd p = source /\ L.last p = v /\
              (forall (w: nat). L.mem w p ==> w < n) /\
              all_edges_traversable cap flow p)
    (ensures exists (p': list nat).
              Cons? p' /\ L.hd p' = source /\ L.last p' = v /\
              (forall (w: nat). L.mem w p' ==> w < n) /\
              all_edges_traversable cap flow p' /\
              L.length p' <= n)
    (decreases (L.length p))
  = if L.length p <= n then ()
    else begin
      // Path has > n vertices, all in {0,...,n-1}. By pigeonhole, repeated vertex.
      let seq_p : FStar.Seq.seq (FStar.Fin.under n) =
        FStar.Seq.init (L.length p) (fun (i: nat{i < L.length p}) ->
          L.lemma_index_memP p i; (L.index p i <: FStar.Fin.under n)) in
      let (i, j) = FStar.Fin.pigeonhole #n seq_p in
      // i < j, L.index p i = L.index p j — remove cycle
      lemma_cycle_remove cap flow source v p i j;
      let p' = FStar.IndefiniteDescription.indefinite_description_ghost
        (list nat) (fun p' ->
          Cons? p' /\ L.hd p' = source /\ L.last p' = v /\
          (forall (w: nat). L.mem w p' ==> w < n) /\
          all_edges_traversable cap flow p' /\
          L.length p' < L.length p) in
      lemma_shorten_path cap flow source v p'
    end
#pop-options

(** Fixed point: reachable_in_Gf ⟹ is_reachable source n *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 120"
let lemma_reachable_iff_bounded (#n: nat{n > 0}) (cap: capacity_matrix n) (flow: flow_matrix n)
  (source: nat{source < n}) (v: nat{v < n})
  : Lemma
    (requires reachable_in_Gf cap flow source v)
    (ensures is_reachable cap flow source n v)
  = let p = FStar.IndefiniteDescription.indefinite_description_ghost
      (list nat) (fun p -> path_in_residual cap flow source v p) in
    lemma_shorten_path cap flow source v p;
    let p' = FStar.IndefiniteDescription.indefinite_description_ghost
      (list nat) (fun p' ->
        Cons? p' /\ L.hd p' = source /\ L.last p' = v /\
        (forall (w: nat). L.mem w p' ==> w < n) /\
        all_edges_traversable cap flow p' /\
        L.length p' <= n) in
    lemma_path_implies_reachable cap flow source v (n - 1) p';
    lemma_reachable_mono cap flow source (n - 1) v
#pop-options

(** Max-flow min-cut theorem (CLRS Theorem 26.6):
    The following are equivalent:
    1. f is a maximum flow
    2. The residual graph G_f has no augmenting path
    3. |f| = c(S,T) for some cut (S,T)

    We state: when no augmenting path exists in G_f, the flow value equals
    the capacity of some cut, which is therefore the minimum cut. *)
let max_flow_min_cut_theorem (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
                              (source: nat{source < n}) (sink: nat{sink < n})
  : Lemma
    (requires
      valid_flow flow cap source sink /\
      // No augmenting path exists: all paths from source have a zero-residual-capacity edge
      (forall (path: list nat).
        Cons? path /\ L.hd path = source /\ L.last path = sink /\
        (forall (v: nat). L.mem v path ==> v < n) ==>
        bottleneck cap flow n path <= 0))
    (ensures
      // Flow value equals some cut capacity (strong duality)
      (exists (s_set: nat -> bool).
        is_st_cut s_set n source sink /\
        flow_value flow n source == cut_capacity cap s_set))
  = if n = 0 then () else begin
    // Step 1: Define S = {v : reachable from source in ≤ n steps in G_f}
    let s_set (v: nat) : Tot bool = is_reachable cap flow source n v in
    // Step 2: Source ∈ S
    assert (s_set source == true);
    // Step 3: Sink ∉ S (by contradiction via bottleneck)
    (if s_set sink then begin
      lemma_reachable_implies_path cap flow source n sink;
      let p = FStar.IndefiniteDescription.indefinite_description_ghost
        (list nat) (fun p -> path_in_residual cap flow source sink p) in
      lemma_sink_not_reachable cap flow source sink p
    end);
    assert (s_set sink == false);
    // Step 4: For u ∈ S, v ∈ T: no residual capacity
    let no_cross_residual (u: nat{u < n}) (v: nat{v < n})
      : Lemma (requires s_set u == true /\ s_set v == false)
              (ensures not (has_residual_capacity cap flow n u v))
      = if has_residual_capacity cap flow n u v then begin
          // u reachable ⟹ reachable_in_Gf ⟹ extend path ⟹ v reachable_in_Gf ⟹ is_reachable n v
          lemma_reachable_implies_path cap flow source n u;
          let p = FStar.IndefiniteDescription.indefinite_description_ghost
            (list nat) (fun p -> path_in_residual cap flow source u p) in
          lemma_extend_reachable cap flow source u v p;
          lemma_reachable_iff_bounded cap flow source v
          // Now is_reachable source n v = true, contradicting s_set v = false
        end
    in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 no_cross_residual);
    // Step 5: net_flow_across_cut = cut_capacity (since all S→T edges saturated)
    lemma_saturated_aux cap flow source sink s_set n;
    // Step 6: flow_value = net_flow_across_cut (CLRS Lemma 26.4)
    lemma_flow_value_eq_net_flow flow cap source sink s_set;
    assert (flow_value flow n source == cut_capacity cap s_set);
    assert (is_st_cut s_set n source sink)
  end
