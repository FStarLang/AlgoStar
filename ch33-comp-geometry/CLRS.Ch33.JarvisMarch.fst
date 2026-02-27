(*
   Jarvis's March (Gift Wrapping) — CLRS Chapter 33, Section 33.3

   Computes the convex hull of a set of 2D points using the gift-wrapping
   algorithm. Each iteration selects the most clockwise point as the next
   hull vertex, using cross-product orientation tests.

   Implements:
   1. find_leftmost: Find the starting point (minimum x, then minimum y)
   2. find_next: Find the next hull vertex by cross-product comparison

   Complexity: O(nh) where n = number of input points, h = number of hull vertices.

   NO admits. NO assumes.
*)

module CLRS.Ch33.JarvisMarch
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Pure Specifications ==========

//SNIPPET_START: cross_prod
// Cross product (p2-p1) × (p3-p1)
// > 0: p3 is left of p1→p2 (CCW)
// < 0: p3 is right of p1→p2 (CW)
// = 0: collinear
let cross_prod (x1 y1 x2 y2 x3 y3: int) : int =
  (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1)
//SNIPPET_END: cross_prod

//SNIPPET_START: find_leftmost_spec
// Find index of leftmost point (min x, break ties by min y).
// Scans from index i onward, maintaining the best candidate.
// Returns best unchanged for invalid inputs (guards on bounds).
let rec find_leftmost_aux (xs ys: Seq.seq int) (i best: nat)
  : Tot nat (decreases (Seq.length xs - i)) =
  if best >= Seq.length xs || Seq.length ys <> Seq.length xs then best
  else if i >= Seq.length xs then best
  else
    let new_best =
      if Seq.index xs i < Seq.index xs best ||
         (Seq.index xs i = Seq.index xs best && Seq.index ys i < Seq.index ys best)
      then i
      else best
    in
    find_leftmost_aux xs ys (i + 1) new_best

let find_leftmost_spec (xs ys: Seq.seq int) : nat =
  if Seq.length xs = 0 then 0
  else find_leftmost_aux xs ys 1 0
//SNIPPET_END: find_leftmost_spec

// Bounds lemma for find_leftmost_aux
let rec find_leftmost_aux_bounded (xs ys: Seq.seq int) (i best: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0 /\ best < Seq.length xs)
          (ensures find_leftmost_aux xs ys i best < Seq.length xs)
          (decreases (Seq.length xs - i)) =
  if i >= Seq.length xs then ()
  else
    let new_best =
      if Seq.index xs i < Seq.index xs best ||
         (Seq.index xs i = Seq.index xs best && Seq.index ys i < Seq.index ys best)
      then i
      else best
    in
    find_leftmost_aux_bounded xs ys (i + 1) new_best

let find_leftmost_spec_bounded (xs ys: Seq.seq int)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0)
          (ensures find_leftmost_spec xs ys < Seq.length xs) =
  find_leftmost_aux_bounded xs ys 1 0

//SNIPPET_START: find_next_spec
// Find next hull vertex: the point that all others lie to the left of
// the line from current to that point (most clockwise turn from current).
// Scans from index j onward, maintaining the best candidate.
// Returns next unchanged for invalid inputs (guards on bounds).
let rec find_next_aux (xs ys: Seq.seq int) (current next: nat) (j: nat)
  : Tot nat (decreases (Seq.length xs - j)) =
  if current >= Seq.length xs || next >= Seq.length xs || Seq.length ys <> Seq.length xs
  then next
  else if j >= Seq.length xs then next
  else if j = current then find_next_aux xs ys current next (j + 1)
  else if next = current then find_next_aux xs ys current j (j + 1)
  else
    let cp = cross_prod
      (Seq.index xs current) (Seq.index ys current)
      (Seq.index xs next) (Seq.index ys next)
      (Seq.index xs j) (Seq.index ys j) in
    let new_next = if cp < 0 then j else next in
    find_next_aux xs ys current new_next (j + 1)

let find_next_spec (xs ys: Seq.seq int) (current: nat) : nat =
  find_next_aux xs ys current current 0
//SNIPPET_END: find_next_spec

// Bounds lemma for find_next_aux
let rec find_next_aux_bounded (xs ys: Seq.seq int) (current next: nat) (j: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ current < Seq.length xs /\ next < Seq.length xs)
          (ensures find_next_aux xs ys current next j < Seq.length xs)
          (decreases (Seq.length xs - j)) =
  if j >= Seq.length xs then ()
  else if j = current then find_next_aux_bounded xs ys current next (j + 1)
  else if next = current then find_next_aux_bounded xs ys current j (j + 1)
  else
    let cp = cross_prod
      (Seq.index xs current) (Seq.index ys current)
      (Seq.index xs next) (Seq.index ys next)
      (Seq.index xs j) (Seq.index ys j) in
    let new_next = if cp < 0 then j else next in
    find_next_aux_bounded xs ys current new_next (j + 1)

let find_next_spec_bounded (xs ys: Seq.seq int) (current: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 1 /\ current < Seq.length xs)
          (ensures find_next_spec xs ys current < Seq.length xs) =
  find_next_aux_bounded xs ys current current 0

// ========== Pulse Implementations ==========

open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

//SNIPPET_START: find_leftmost_sig
fn find_leftmost (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len > 0 /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys
    )
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v result == find_leftmost_spec sxs sys /\
      SZ.v result < SZ.v len
    )
//SNIPPET_END: find_leftmost_sig
{
  find_leftmost_spec_bounded sxs sys;
  let mut best: SZ.t = 0sz;
  let mut i: SZ.t = 1sz;

  while (!i <^ len)
  invariant exists* vi vbest.
    R.pts_to i vi **
    R.pts_to best vbest **
    A.pts_to xs #p sxs **
    A.pts_to ys #p sys **
    pure (
      SZ.v vi >= 1 /\
      SZ.v vi <= SZ.v len /\
      SZ.v vbest < SZ.v len /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len == Seq.length sxs /\
      find_leftmost_aux sxs sys (SZ.v vi) (SZ.v vbest) == find_leftmost_spec sxs sys
    )
  {
    let vi = !i;
    let vbest = !best;
    let xi = xs.(vi);
    let xb = xs.(vbest);
    let yi = ys.(vi);
    let yb = ys.(vbest);

    if (xi < xb || (xi = xb && yi < yb)) {
      best := vi
    };

    i := SZ.add vi 1sz
  };

  !best
}

//SNIPPET_START: find_next_sig
fn find_next (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t) (current: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len > 1 /\
      SZ.v current < SZ.v len /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys
    )
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v result == find_next_spec sxs sys (SZ.v current) /\
      SZ.v result < SZ.v len
    )
//SNIPPET_END: find_next_sig
{
  find_next_spec_bounded sxs sys (SZ.v current);
  let mut next: SZ.t = current;
  let mut j: SZ.t = 0sz;

  while (!j <^ len)
  invariant exists* vj vnext.
    R.pts_to j vj **
    R.pts_to next vnext **
    A.pts_to xs #p sxs **
    A.pts_to ys #p sys **
    pure (
      SZ.v vj <= SZ.v len /\
      SZ.v vnext < SZ.v len /\
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v current < SZ.v len /\
      find_next_aux sxs sys (SZ.v current) (SZ.v vnext) (SZ.v vj) ==
        find_next_spec sxs sys (SZ.v current)
    )
  {
    let vj = !j;
    let vnext = !next;

    // Read all coordinates unconditionally
    let cx = xs.(current);
    let cy = ys.(current);
    let nx = xs.(vnext);
    let ny = ys.(vnext);
    let jx = xs.(vj);
    let jy = ys.(vj);
    // Cross product: when vnext = current this evaluates to 0
    let cp = (nx - cx) * (jy - cy) - (jx - cx) * (ny - cy);

    // Update next if: j is not current AND (next is current OR j is more clockwise)
    let do_update = not (vj = current) && ((vnext = current) || (cp < 0));
    if do_update {
      next := vj
    };

    j := SZ.add vj 1sz
  };

  !next
}

// ========== Complexity Analysis ==========

//SNIPPET_START: op_counts
// find_leftmost: n-1 comparisons for n points
let find_leftmost_ops (n: nat) : nat = if n > 0 then n - 1 else 0

// find_next: at most n-1 cross-product evaluations (skip current)
let find_next_ops (n: nat) : nat = if n > 1 then n - 1 else 0

// Full Jarvis march: 1 find_leftmost + h find_next calls
let jarvis_march_ops (n h: nat) : nat = find_leftmost_ops n + h * find_next_ops n
//SNIPPET_END: op_counts

//SNIPPET_START: complexity_lemmas
// Jarvis march is O(nh): bounded by n^2 in the worst case
let jarvis_march_quadratic_bound (n h: nat) : Lemma
  (requires n > 1 /\ h <= n)
  (ensures jarvis_march_ops n h <= n * n)
  = ()

// Each helper is O(n)
let helpers_linear (n: nat) : Lemma
  (requires n > 1)
  (ensures find_leftmost_ops n <= n /\ find_next_ops n <= n)
  = ()
//SNIPPET_END: complexity_lemmas
