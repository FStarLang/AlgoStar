(*
 * CLRS Chapter 22 — DFS Implementation Interface
 *
 * Exposes the stack-based DFS function signature (CLRS §22.3).
 *
 * ## White-Path Theorem Connection
 *
 * The White-Path Theorem (CLRS Theorem 22.9) is fully proven in
 * CLRS.Ch22.DFS.WhitePath.fst for the pure spec representation
 * (2D adjacency Seq.seq (Seq.seq int), Seq.seq nat timestamps).
 *
 * Flat-array versions of the white-path vocabulary are available in
 * CLRS.Ch22.Graph.Common: dfs_ancestor_flat, white_at_time_flat,
 * path_all_white_flat, white_path_exists_flat. These use the same
 * Seq.seq int representation as this interface's postcondition.
 *
 * The lemma pred_implies_tree_or_forward (Graph.Common) connects
 * the predecessor array to the DFS ancestor relation: for any vertex v
 * with a valid predecessor, pred[v] is an ancestor of v in the DFS
 * forest (i.e., is_tree_or_forward_edge sd sf pred[v] v == true).
 *
 * A full bridge (proving impl computes the same timestamps as the
 * spec function dfs) is left as future work. See WhitePath.fst for
 * the proven theorem:
 *   dfs_ancestor d f u v <==> white_path_exists adj n d u v d[u]
 *)
module CLRS.Ch22.DFS.Impl
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

fn stack_dfs
  (adj: A.array int)
  (n: SZ.t)
  (color: A.array int)
  (d: A.array int)
  (f: A.array int)
  (pred: A.array int)
  (stack_data: A.array SZ.t)
  (scan_idx: A.array SZ.t)
  (ctr: GR.ref nat)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#sf: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  (#c0: erased nat)
  requires
    A.pts_to adj sadj **
    A.pts_to color scolor **
    A.pts_to d sd **
    A.pts_to f sf **
    A.pts_to pred spred **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sadj <= A.length adj /\
      Seq.length scolor == SZ.v n /\
      Seq.length scolor <= A.length color /\
      Seq.length sd == SZ.v n /\
      Seq.length sd <= A.length d /\
      Seq.length sf == SZ.v n /\
      Seq.length sf <= A.length f /\
      Seq.length spred == SZ.v n /\
      Seq.length spred <= A.length pred /\
      Seq.length sstack == SZ.v n /\
      Seq.length sstack <= A.length stack_data /\
      Seq.length sscan == SZ.v n /\
      Seq.length sscan <= A.length scan_idx /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  ensures exists* scolor' sd' sf' spred' sstack' sscan' (cf: nat).
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    A.pts_to d sd' **
    A.pts_to f sf' **
    A.pts_to pred spred' **
    A.pts_to stack_data sstack' **
    A.pts_to scan_idx sscan' **
    GR.pts_to ctr cf **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sd' == SZ.v n /\
      Seq.length sf' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length sstack' == SZ.v n /\
      Seq.length sscan' == SZ.v n /\
      // All vertices eventually colored BLACK (finished)
      (forall (u: nat). u < SZ.v n ==> Seq.index scolor' u == 2) /\
      // Discovery and finish times are positive
      (forall (u: nat). u < SZ.v n ==> Seq.index sd' u > 0) /\
      (forall (u: nat). u < SZ.v n ==> Seq.index sf' u > 0) /\
      // Discovery time < finish time (parenthesis theorem)
      (forall (u: nat). u < SZ.v n ==> Seq.index sd' u < Seq.index sf' u) /\
      // Timestamp bounds: all timestamps ≤ 2*n
      (forall (u: nat). u < SZ.v n ==> Seq.index sd' u <= 2 * SZ.v n) /\
      (forall (u: nat). u < SZ.v n ==> Seq.index sf' u <= 2 * SZ.v n) /\
      // Predecessor tree: pred[v] >= 0 implies edge from pred[v] to v, d[pred[v]] < d[v]
      pred_edge_ok sadj (SZ.v n) scolor' sd' spred' /\
      // Predecessor finish ordering: children finish before parents
      (forall (v: nat). v < SZ.v n /\ Seq.index spred' v >= 0 /\ Seq.index spred' v < SZ.v n ==>
        Seq.index sf' v < Seq.index sf' (Seq.index spred' v)) /\
      // Complexity: at most 2 * n² ticks
      cf >= reveal c0 /\
      cf - reveal c0 <= 2 * (SZ.v n * SZ.v n)
    )
