(*
   CLRS Chapter 9.1: MINIMUM / MAXIMUM — Complexity Signatures

   Ghost tick infrastructure for counting comparisons.
   find_minimum and find_maximum each use exactly n-1 comparisons.
*)
module CLRS.Ch09.MinMax.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

/// Increment erased nat by 1
val incr_nat (n: erased nat) : erased nat

/// Ghost tick: increment counter by 1
ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
