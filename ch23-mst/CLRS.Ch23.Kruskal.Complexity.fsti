(*
   CLRS Chapter 23: Kruskal's Algorithm — Complexity Interface

   Ghost-tick instrumented Kruskal proves ticks ≤ 4·V³.
   
   CLRS §23.2: With adjacency matrix (V²-scan per round variant):
   - (V-1) rounds, each scanning V² entries + O(V) union-find
   - Total: O(V³)
*)

module CLRS.Ch23.Kruskal.Complexity
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
module V = Pulse.Lib.Vec

/// Complexity bound: ticks ≤ 4·V³
let complexity_bounded_kruskal (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 <= 4 * n * n * n
