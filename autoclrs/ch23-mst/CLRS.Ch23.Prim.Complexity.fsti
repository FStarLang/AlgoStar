(*
   CLRS Chapter 23: Prim's Algorithm — Complexity Interface

   Ghost-tick instrumented Prim proves ticks ≤ 3·V².
   
   CLRS §23.2: With adjacency matrix:
   - V iterations × (V for extract-min + V for key update) = 2V²
   - Bound of 3V² accounts for overhead

   ============================================================
   WARNING — DISCONNECTED / WORK IN PROGRESS
   ============================================================
   This module is NOT connected to Prim.Impl. It re-implements
   Prim's algorithm from scratch with ghost tick counters for
   complexity analysis. The postcondition only proves
   `prim_correct` (a weaker local predicate) and
   `complexity_bounded_prim` — it does NOT prove the result
   relates to `prim_spec` or MST properties from Prim.Spec.

   To fully connect this module:
   1. Import and use the Prim.Impl postcondition predicates
   2. Add the MST-related postcondition from Prim.Spec
   3. Or: add ghost tick counting directly to Prim.Impl
   ============================================================
*)

module CLRS.Ch23.Prim.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open Pulse.Lib.Reference

module SZ = FStar.SizeT
module Seq = FStar.Seq

/// Complexity bound: ticks ≤ 3·V²
let complexity_bounded_prim (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= 3 * n * n
