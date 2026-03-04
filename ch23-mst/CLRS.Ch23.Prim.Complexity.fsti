(*
   CLRS Chapter 23: Prim's Algorithm — Complexity Interface

   Ghost-tick instrumented Prim proves ticks ≤ 3·V².
   
   CLRS §23.2: With adjacency matrix:
   - V iterations × (V for extract-min + V for key update) = 2V²
   - Bound of 3V² accounts for overhead
*)

module CLRS.Ch23.Prim.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open Pulse.Lib.Reference
open FStar.Mul

module SZ = FStar.SizeT
module Seq = FStar.Seq

/// Complexity bound: ticks ≤ 3·V²
let complexity_bounded_prim (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= 3 * n * n
