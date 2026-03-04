(*
   Dijkstra's Algorithm — Complexity Interface

   Ghost-tick instrumented Dijkstra proves exact complexity: n + 2n² ticks.
   
   CLRS §24.3: With adjacency matrix and array-based min-priority queue:
   - n EXTRACT-MIN: O(n) each → O(n²) total
   - n × n relaxations → O(n²) total
   - Overall: O(V²)

   Bound: n + 2n² ≤ 3n²
*)

module CLRS.Ch24.Dijkstra.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Vec
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// All weights are non-negative
val all_weights_non_negative (sweights: Seq.seq int) : prop

/// All distances are non-negative
val all_non_negative (sdist: Seq.seq int) : prop

/// All distances bounded: 0 ≤ d ≤ 1000000
val all_bounded (sdist: Seq.seq int) : prop

/// Total iteration count: n + 2n²
val dijkstra_iterations (n: nat) : nat

/// Quadratic bound: n + 2n² ≤ 3n²
val dijkstra_quadratic_bound (n: nat) : Lemma
  (ensures dijkstra_iterations n <= 3 * n * n)

/// Complexity predicate connecting pure math to ghost counter
val dijkstra_complexity_bounded (cf c0 n: nat) : prop

/// O(V²) bound via complexity predicate
val dijkstra_complexity_is_quadratic (cf c0 n: nat) : Lemma
  (requires dijkstra_complexity_bounded cf c0 n)
  (ensures cf - c0 <= 3 * n * n)

//SNIPPET_START: dijkstra_complexity_sig
/// Dijkstra with ghost-tick complexity instrumentation
fn dijkstra_complexity
  (weights: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (dist: A.array int)
  (#sweights: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to weights sweights **
    A.pts_to dist sdist **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sweights == SZ.v n * SZ.v n /\
      Seq.length sdist == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      all_weights_non_negative sweights
    )
  ensures exists* sdist' (cf: nat).
    A.pts_to weights sweights **
    A.pts_to dist sdist' **
    GR.pts_to ctr cf **
    pure (
      Seq.length sdist' == SZ.v n /\
      SZ.v source < Seq.length sdist' /\
      Seq.index sdist' (SZ.v source) == 0 /\
      all_non_negative sdist' /\
      all_bounded sdist' /\
      dijkstra_complexity_bounded cf (reveal c0) (SZ.v n)
    )
//SNIPPET_END: dijkstra_complexity_sig
