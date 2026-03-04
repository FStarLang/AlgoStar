(*
   CLRS Chapter 9.1: Simultaneous Min and Max — Complexity Signatures

   Ghost tick infrastructure for counting comparisons.
*)
module CLRS.Ch09.SimultaneousMinMax.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

/// Increment erased nat by 1
val incr_nat (n: erased nat) : erased nat

/// Add k to erased nat
val add_nat (n: erased nat) (k: nat) : erased nat

/// SMTPat: reveal (add_nat n k) == reveal n + k
val add_nat_reveal (n: erased nat) (k: nat)
  : Lemma (reveal (add_nat n k) == reveal n + k)
    [SMTPat (add_nat n k)]

/// SMTPat: reveal (incr_nat n) == reveal n + 1
val incr_nat_reveal (n: erased nat)
  : Lemma (reveal (incr_nat n) == reveal n + 1)
    [SMTPat (incr_nat n)]

/// Ghost tick: increment counter by 1
ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)

/// Ghost add_ticks: increment counter by k
ghost
fn add_ticks (ctr: GR.ref nat) (#n: erased nat) (k: nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (add_nat n k)
