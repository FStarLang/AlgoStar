(*
   Complexity Bound Framework for Pulse Programs

   Provides ghost tick counting primitives for proving running time
   complexity bounds. The tick counter is a ghost nat ref that is
   threaded through computations and fully erased at runtime. Each
   "unit of work" increments the counter, and postconditions express
   upper bounds on total ticks.

   Convention: we count "dominant operations" per algorithm:
     - Comparisons for sorting and searching
     - Arithmetic ops for number theory
     - Array accesses for general algorithms

   Usage pattern:
     fn my_algorithm (... ctr: GR.ref nat ...)
       requires GR.pts_to ctr c0 ** ...
       ensures  GR.pts_to ctr c1 ** ... ** pure (c1 - c0 <= bound)

   NO admits. NO assumes.
*)

module CLRS.Common.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.GhostReference

module GR = Pulse.Lib.GhostReference

(* ---------- helpers for erased arithmetic ---------- *)

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)
let add_nat (n: erased nat) (k: nat) : erased nat = hide (Prims.op_Addition (reveal n) k)

let incr_nat_reveal (n: erased nat)
  : Lemma (reveal (incr_nat n) == reveal n + 1)
    [SMTPat (incr_nat n)]
  = ()

let add_nat_reveal (n: erased nat) (k: nat)
  : Lemma (reveal (add_nat n k) == reveal n + k)
    [SMTPat (add_nat n k)]
  = ()

(* ---------- tick: increment the ghost tick counter by 1 ---------- *)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

(* ---------- ticks: increment by k ---------- *)

ghost
fn ticks (ctr: GR.ref nat) (k: nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (add_nat n k)
{
  GR.(ctr := add_nat n k)
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
