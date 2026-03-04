(*
   CLRS Chapter 9.1: Simultaneous Min and Max — Complexity Proofs

   Ghost tick infrastructure for counting comparisons.

   NO admits. NO assumes.
*)
module CLRS.Ch09.SimultaneousMinMax.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)
let add_nat (n: erased nat) (k: nat) : erased nat = hide (Prims.op_Addition (reveal n) k)

let add_nat_reveal (n: erased nat) (k: nat)
  : Lemma (reveal (add_nat n k) == reveal n + k)
    [SMTPat (add_nat n k)]
  = ()

let incr_nat_reveal (n: erased nat)
  : Lemma (reveal (incr_nat n) == reveal n + 1)
    [SMTPat (incr_nat n)]
  = ()

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

ghost
fn add_ticks (ctr: GR.ref nat) (#n: erased nat) (k: nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (add_nat n k)
{
  GR.(ctr := add_nat n k)
}
