(*
   Complexity Bound Framework for Pulse Programs

   Provides ghost tick counting primitives for proving running time
   complexity bounds. The tick counter is a mutable nat ref that is
   threaded through computations. Each "unit of work" increments the
   counter, and postconditions express upper bounds on total ticks.

   Convention: we count "dominant operations" per algorithm:
     - Comparisons for sorting and searching
     - Arithmetic ops for number theory
     - Array accesses for general algorithms

   Usage pattern:
     fn my_algorithm (... ctr: ref nat ...)
       requires R.pts_to ctr c0 ** ...
       ensures  R.pts_to ctr c1 ** ... ** pure (c1 - c0 <= bound)

   NO admits. NO assumes.
*)

module CLRS.Common.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference

module R = Pulse.Lib.Reference

(* ---------- tick: increment the ghost tick counter by 1 ---------- *)

fn tick (ctr: ref nat) (#n: erased nat)
  requires R.pts_to ctr n
  ensures  R.pts_to ctr (n + 1)
{
  let v = !ctr;
  ctr := v + 1
}

(* ---------- ticks: increment by k ---------- *)

fn ticks (ctr: ref nat) (k: nat) (#n: erased nat)
  requires R.pts_to ctr n
  ensures  R.pts_to ctr (n + k)
{
  let v = !ctr;
  ctr := v + k
}

(* ---------- Pure helpers for complexity bounds ---------- *)

// Triangular number: 1 + 2 + ... + n = n*(n+1)/2
let triangle (n: nat) : nat = op_Multiply n (n + 1) / 2

let rec lemma_triangle_sum (n: nat)
  : Lemma (ensures triangle n == (if n = 0 then 0 else triangle (n - 1) + n))
          (decreases n)
  = if n = 0 then ()
    else if n = 1 then ()
    else lemma_triangle_sum (n - 1)

// log2_floor for binary search bound
let rec log2_floor (n: pos) : Tot nat (decreases n) =
  if n = 1 then 0
  else 1 + log2_floor (n / 2)

// Key property: 2^(log2_floor n) <= n < 2^(log2_floor n + 1)
let rec lemma_log2_floor_bound (n: pos)
  : Lemma (ensures pow2 (log2_floor n) <= n /\ n < pow2 (log2_floor n + 1))
          (decreases n)
  = if n = 1 then ()
    else (
      lemma_log2_floor_bound (n / 2);
      FStar.Math.Lemmas.pow2_plus 1 (log2_floor (n / 2));
      FStar.Math.Lemmas.pow2_plus 1 (log2_floor (n / 2) + 1)
    )

// Halving reduces log2_floor
let lemma_log2_half (n: pos)
  : Lemma (requires n > 1)
          (ensures log2_floor (n / 2) == log2_floor n - 1 /\ log2_floor n > 0)
  = ()
