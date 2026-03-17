(*
   Bellman-Ford Single-Source Shortest Paths — Implementation Interface

   Pulse function signature for the verified Bellman-Ford algorithm,
   providing both full correctness and O(V³) complexity guarantees
   in a single function via ghost tick counting.

   Uses adjacency matrix representation (n×n flat array, SP.inf = no edge/∞).
   Requires weights_in_range: each finite edge weight w satisfies
   |w|*(n-1) < inf, ensuring all simple-path weights are representable.

   Postcondition guarantees:
   - dist[source] == 0
   - Valid distances (< SP.inf or == SP.inf)
   - If no negative cycle: triangle inequality + upper bound (CLRS Cor 24.3)
   - Negative-cycle detection (CLRS Cor 24.5)
   - Shortest-path equality under no negative cycles (CLRS Thm 24.4)
   - O(V³) complexity bound via ghost counter

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

// ========== Definitions ==========

/// Triangle inequality: for each edge (u,v), dist[v] <= dist[u] + w(u,v) when finite
let triangle_inequality (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : prop =
  Seq.length dist == n /\
  forall (u v: nat). u < n /\ v < n /\
    (u * n + v) < Seq.length weights ==>
    (let d_u = Seq.index dist u in
     let d_v = Seq.index dist v in
     let w = Seq.index weights (u * n + v) in
     (w < SP.inf /\ d_u < SP.inf) ==> d_v <= d_u + w)

/// Weights in range: each finite edge weight w satisfies |w| * (n-1) < inf,
/// ensuring all simple-path weights are representable (< inf).
let weights_in_range = SP.weights_in_range

/// All distances are either finite (< inf) or equal to inf (unreachable)
let valid_distances (dist: Seq.seq int) (n: nat) : prop =
  Seq.length dist == n /\
  forall (v: nat). v < n ==> 
    (let d = Seq.index dist v in d < SP.inf \/ d == SP.inf)

/// Exists a violating edge: some edge (u,v) has dist[v] > dist[u] + w(u,v)
let exists_violation (dist: Seq.seq int) (weights: Seq.seq int) (n: nat) : prop =
  Seq.length dist == n /\
  Seq.length weights == n * n /\
  (exists (u v: nat). u < n /\ v < n /\
    (let d_u = Seq.index dist u in
     let d_v = Seq.index dist v in
     let w = Seq.index weights (u * n + v) in
     w < SP.inf /\ d_u < SP.inf /\ d_v > d_u + w))

/// Lower bound invariant: dist[v] >= sp_dist[v] for all v
let lower_bound_inv (dist: Seq.seq int) (weights: Seq.seq int) (n source: nat) : prop =
  Seq.length dist == n /\
  (forall (v: nat). v < n ==>
    Seq.index dist v >= SP.sp_dist weights n source v)

// ========== Complexity Bounds ==========

/// Total iteration count for Bellman-Ford with adjacency matrix
let bellman_ford_iterations (n: nat) : nat =
  n + (if n >= 1 then (n - 1) * n * n else 0) + n * n

/// Complexity bound predicate: connects ghost counter to iteration count
let bellman_ford_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ (n >= 1 ==> cf - c0 == n + n * n * n)

/// O(n³) bound: total iterations ≤ 2n³
val bellman_ford_cubic_bound (n: nat) : Lemma
  (requires n >= 1)
  (ensures bellman_ford_iterations n <= 2 * n * n * n)

/// Ghost counter proves O(n³): cf - c0 ≤ 2n³
val bellman_ford_complexity_is_cubic (cf c0 n: nat) : Lemma
  (requires bellman_ford_complexity_bounded cf c0 n /\ n >= 1)
  (ensures cf - c0 <= 2 * n * n * n)

// ========== Algorithm: Correctness + Complexity ==========

//SNIPPET_START: bellman_ford_sig
/// Bellman-Ford SSSP — correctness + O(V³) complexity in one function
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
      weights_in_range sweights (SZ.v n)
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
      (no_neg_cycle == true ==>
        (forall (v: nat). v < SZ.v n ==>
          Seq.index sdist' v <= SP.sp_dist sweights (SZ.v n) (SZ.v source) v)) /\
      (no_neg_cycle == false ==> exists_violation sdist' sweights (SZ.v n)) /\
      (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==>
        lower_bound_inv sdist' sweights (SZ.v n) (SZ.v source)) /\
      (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) /\ no_neg_cycle == true ==>
        (forall (v: nat). v < SZ.v n ==>
          Seq.index sdist' v == SP.sp_dist sweights (SZ.v n) (SZ.v source) v)) /\
      (SP.no_neg_cycles_flat sweights (SZ.v n) (SZ.v source) ==> no_neg_cycle == true) /\
      bellman_ford_complexity_bounded cf (reveal c0) (SZ.v n)
    )
//SNIPPET_END: bellman_ford_sig
