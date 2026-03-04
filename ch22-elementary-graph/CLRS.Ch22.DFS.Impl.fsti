(*
 * CLRS Chapter 22 — DFS Implementation Interface
 *
 * Exposes the stack-based DFS function signature (CLRS §22.3).
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
      // Complexity: at most 2 * n² ticks
      cf >= reveal c0 /\
      cf - reveal c0 <= 2 * (SZ.v n * SZ.v n)
    )
