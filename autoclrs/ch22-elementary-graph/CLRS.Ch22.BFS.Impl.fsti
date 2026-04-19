(*
 * CLRS Chapter 22 — BFS Implementation Interface
 *
 * Exposes the queue-based BFS function signature (CLRS §22.2).
 *)
module CLRS.Ch22.BFS.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open Pulse.Lib.WithPure

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

open CLRS.Ch22.Graph.Common

fn queue_bfs
  (adj: A.array int)
  (n: SZ.t)
  (source: SZ.t)
  (color: A.array int)
  (dist: A.array int)
  (pred: A.array int)
  (queue_data: A.array SZ.t)
  (ctr: GR.ref nat)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sdist: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#squeue: erased (Seq.seq SZ.t))
  (#c0: erased nat)
  requires
    A.pts_to adj sadj **
    A.pts_to color scolor **
    A.pts_to dist sdist **
    A.pts_to pred spred **
    A.pts_to queue_data squeue **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      SZ.v source < SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sadj <= A.length adj /\
      Seq.length scolor == SZ.v n /\
      Seq.length scolor <= A.length color /\
      Seq.length sdist == SZ.v n /\
      Seq.length sdist <= A.length dist /\
      Seq.length spred == SZ.v n /\
      Seq.length spred <= A.length pred /\
      Seq.length squeue == SZ.v n /\
      Seq.length squeue <= A.length queue_data /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  ensures exists* scolor' sdist' spred' squeue' (cf: nat).
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    A.pts_to dist sdist' **
    A.pts_to pred spred' **
    A.pts_to queue_data squeue' **
    GR.pts_to ctr cf **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sdist' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length squeue' == SZ.v n /\
      SZ.v source < SZ.v n /\
      // Source is visited (BLACK after BFS completion)
      Seq.index scolor' (SZ.v source) <> 0 /\
      // Distance of source is 0
      Seq.index sdist' (SZ.v source) == 0 /\
      // Distance soundness: visited vertices have valid distances
      (forall (w: nat). w < SZ.v n /\ Seq.index scolor' w <> 0 ==>
        Seq.index sdist' w >= 0) /\
      // Reachability: every discovered vertex is reachable from source,
      // witnessed by dist[w] steps in the adjacency graph
      (forall (w: nat). w < SZ.v n /\ Seq.index scolor' w <> 0 ==>
        reachable_in sadj (SZ.v n) (SZ.v source) w (Seq.index sdist' w)) /\
      // Completeness: every reachable vertex is discovered
      (forall (v: nat) (k: nat). v < SZ.v n /\ reachable_in sadj (SZ.v n) (SZ.v source) v k ==>
        Seq.index scolor' v <> 0) /\
      // Predecessor distance consistency: for discovered non-source vertices,
      // dist[v] = dist[pred[v]] + 1 and pred[v] is also discovered
      (forall (v: nat). v < SZ.v n /\ Seq.index scolor' v <> 0 /\
        Seq.index spred' v >= 0 /\ Seq.index spred' v < SZ.v n ==>
        Seq.index scolor' (Seq.index spred' v) <> 0 /\
        Seq.index sdist' v == Seq.index sdist' (Seq.index spred' v) + 1) /\
      // Optimality: distances are shortest paths
      (forall (w: nat) (k: nat). w < SZ.v n /\ reachable_in sadj (SZ.v n) (SZ.v source) w k ==>
        Seq.index sdist' w <= k) /\
      // Complexity: at most 2 * n² ticks
      cf >= reveal c0 /\
      cf - reveal c0 <= 2 * (SZ.v n * SZ.v n)
    )
