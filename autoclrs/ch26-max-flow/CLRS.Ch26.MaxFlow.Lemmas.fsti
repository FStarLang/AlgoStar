module CLRS.Ch26.MaxFlow.Lemmas

open FStar.Mul
open FStar.List.Tot
open CLRS.Ch26.MaxFlow.Spec

module Seq = FStar.Seq
module L = FStar.List.Tot

(*
   Interface for Edmonds-Karp augmentation lemmas.
   
   All lemmas are fully proven (zero assumes).
   See CLRS.Ch26.MaxFlow.Lemmas.fst for implementations.
*)

(** Sum-flow update lemmas for augmentation reasoning *)
val lemma_sum_flow_into_update_other (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                                      (u: nat{u < n}) (v: nat{v < n}) (x: int)
                                      (w: nat{w < n /\ w <> v}) (k: nat)
  : Lemma (ensures sum_flow_into (set flow n u v x) n w k == sum_flow_into flow n w k)

val lemma_sum_flow_out_update_other (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                                     (u: nat{u < n}) (v: nat{v < n}) (x: int)
                                     (w: nat{w < n /\ w <> u}) (k: nat)
  : Lemma (ensures sum_flow_out (set flow n u v x) n w k == sum_flow_out flow n w k)

val lemma_sum_flow_out_increase (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                                 (u: nat{u < n}) (v: nat{v < n}) (delta: int) (k: nat)
  : Lemma (requires k > v)
          (ensures sum_flow_out (set flow n u v (get flow n u v + delta)) n u k == 
                   sum_flow_out flow n u k + delta)

val lemma_sum_flow_into_increase (flow: Seq.seq int) (n: nat{Seq.length flow == n * n})
                                  (u: nat{u < n}) (v: nat{v < n}) (delta: int) (k: nat)
  : Lemma (requires k > u)
          (ensures sum_flow_into (set flow n u v (get flow n u v + delta)) n v k == 
                   sum_flow_into flow n v k + delta)

(** Augmenting a single edge maintains capacity constraints *)
val lemma_augment_edge_capacity (flow: Seq.seq int) (cap: Seq.seq int)
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

(** Conservation preserved at vertices w ≠ u and w ≠ v after augmenting edge (u,v) *)
val lemma_augment_edge_conservation_other (flow: Seq.seq int) (cap: Seq.seq int)
                                           (n: nat{Seq.length flow == n * n /\ Seq.length cap == n * n})
                                           (u: nat{u < n}) (v: nat{v < n}) (delta: int)
                                           (w: nat{w < n /\ w <> u /\ w <> v})
  : Lemma
    (requires sum_flow_into flow n w n == sum_flow_out flow n w n)
    (ensures (let flow' = augment_edge flow cap n u v delta in
              sum_flow_into flow' n w n == sum_flow_out flow' n w n))

(** get/set non-interference: setting (u,v) doesn't affect get (a,b) when (a,b) ≠ (u,v) *)
val lemma_get_set_other (m: Seq.seq int) (n: nat{n > 0 /\ Seq.length m == n * n})
                         (u v: nat{u < n /\ v < n}) (x: int) (a b: nat{a < n /\ b < n})
  : Lemma (requires a <> u \/ b <> v)
          (ensures get (set m n u v x) n a b == get m n a b)

(** augment_edge preserves get at (a,b) when a ≠ u and b ≠ u *)
val lemma_augment_edge_get_other (flow cap: Seq.seq int) 
                                  (n: nat{n > 0 /\ Seq.length flow == n * n /\ Seq.length cap == n * n})
                                  (u v: nat{u < n /\ v < n}) (delta: int)
                                  (a b: nat{a < n /\ b < n})
  : Lemma (requires a <> u /\ b <> u)
          (ensures get (augment_edge flow cap n u v delta) n a b == get flow n a b)

(** augment_edge preserves get at (b,a) when a ≠ u and b ≠ u *)
val lemma_augment_edge_get_other_sym (flow cap: Seq.seq int)
                                      (n: nat{n > 0 /\ Seq.length flow == n * n /\ Seq.length cap == n * n})
                                      (u v: nat{u < n /\ v < n}) (delta: int)
                                      (a b: nat{a < n /\ b < n})
  : Lemma (requires a <> u /\ b <> u)
          (ensures get (augment_edge flow cap n u v delta) n b a == get flow n b a)

(** Bottleneck of tail path is unchanged after augmenting the first edge,
    when the path has distinct vertices. *)
val lemma_bottleneck_unchanged
  (cap flow: Seq.seq int) (n: nat{n > 0 /\ Seq.length cap == n * n /\ Seq.length flow == n * n})
  (u: nat{u < n}) (v: nat{v < n}) (delta: int)
  (tail: list nat{Cons? tail /\ (forall (w: nat). L.mem w tail ==> w < n)})
  : Lemma
    (requires not (L.mem u tail) /\ distinct_vertices tail)
    (ensures
      bottleneck_aux cap (augment_edge flow cap n u v delta) n tail ==
      bottleneck_aux cap flow n tail)

(** Augmentation preserves valid flow (CLRS §26.2).
    If flow is valid, path is a simple source-to-sink path with distinct vertices,
    and bn ≤ bottleneck, then the augmented flow is also valid. *)
val augment_preserves_valid (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
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

(** Augmentation strictly increases flow value. *)
val augment_increases_value (#n: nat) (cap: capacity_matrix n) (flow: flow_matrix n)
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

(** Zero flow is a valid flow for any network with non-negative capacities. *)
val zero_flow_valid (#n: nat) (cap: capacity_matrix n) (source: nat{source < n}) (sink: nat{sink < n})
  : Lemma
    (requires forall (i: nat). i < n * n ==> Seq.index cap i >= 0)
    (ensures 
      (let flow = Seq.create (n * n) 0 in
       valid_flow flow cap source sink))

(** Augmenting path edges can be reordered: process last edge first.
    Key for relating augment_imp (reverse walk) to augment_aux (forward walk). *)
val lemma_augment_aux_last_first
  (flow cap: Seq.seq int)
  (n: nat{n > 0 /\ Seq.length flow == n * n /\ Seq.length cap == n * n})
  (path: list nat{Cons? path /\ (forall (v: nat). L.mem v path ==> v < n)})
  (delta: int)
  : Lemma
    (requires distinct_vertices path /\ L.length path >= 2)
    (ensures
      (let last = L.last path in
       let init = L.init path in
       L.length init >= 1 /\ Cons? init /\
       (forall (v: nat). L.mem v init ==> v < n) /\
       last < n /\
       (L.length init >= 2 ==>
         (let second_last = L.last init in
          second_last < n /\
          augment_aux flow cap n path delta ==
          augment_aux (augment_edge flow cap n second_last last delta) cap n init delta))))
