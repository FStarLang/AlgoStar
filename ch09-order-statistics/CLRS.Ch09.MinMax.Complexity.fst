(*
   CLRS Chapter 9.1: MINIMUM / MAXIMUM — Complexity Proofs

   Ghost tick infrastructure for counting comparisons.
   find_minimum and find_maximum each use exactly n-1 comparisons.

   NO admits. NO assumes.
*)
module CLRS.Ch09.MinMax.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}
