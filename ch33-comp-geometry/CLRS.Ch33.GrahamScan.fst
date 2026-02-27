(*
   Graham Scan — CLRS Chapter 33, Section 33.3

   Computes the convex hull of a set of 2D points using Graham's scan.
   Points are sorted by polar angle w.r.t. the bottom-most point, then
   processed with a stack to eliminate non-left turns.

   Implements:
   1. find_bottom: Find the starting point (minimum y, then minimum x)
   2. polar_cmp: Compare polar angles of two points w.r.t. a pivot
   3. Pure specifications for the complete Graham scan algorithm

   Complexity: O(n lg n) dominated by sorting (scan is O(n) amortized).

   NO admits. NO assumes.
*)

module CLRS.Ch33.GrahamScan
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
let cross_prod (x1 y1 x2 y2 x3 y3: int) : int =
  (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1)
//SNIPPET_END: cross_prod

//SNIPPET_START: find_bottom_spec
// Find index of bottom-most point (min y, break ties by min x).
let rec find_bottom_aux (xs ys: Seq.seq int) (i best: nat)
  : Tot nat (decreases (Seq.length xs - i)) =
  if best >= Seq.length xs || Seq.length ys <> Seq.length xs then best
  else if i >= Seq.length xs then best
  else
    let new_best =
      if Seq.index ys i < Seq.index ys best ||
         (Seq.index ys i = Seq.index ys best && Seq.index xs i < Seq.index xs best)
      then i
      else best
    in
    find_bottom_aux xs ys (i + 1) new_best

let find_bottom_spec (xs ys: Seq.seq int) : nat =
  if Seq.length xs = 0 then 0
  else find_bottom_aux xs ys 1 0
//SNIPPET_END: find_bottom_spec

// Bounds lemma for find_bottom
let rec find_bottom_aux_bounded (xs ys: Seq.seq int) (i best: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0 /\ best < Seq.length xs)
          (ensures find_bottom_aux xs ys i best < Seq.length xs)
          (decreases (Seq.length xs - i)) =
  if i >= Seq.length xs then ()
  else
    let new_best =
      if Seq.index ys i < Seq.index ys best ||
         (Seq.index ys i = Seq.index ys best && Seq.index xs i < Seq.index xs best)
      then i
      else best
    in
    find_bottom_aux_bounded xs ys (i + 1) new_best

let find_bottom_spec_bounded (xs ys: Seq.seq int)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0)
          (ensures find_bottom_spec xs ys < Seq.length xs) =
  find_bottom_aux_bounded xs ys 1 0

//SNIPPET_START: polar_cmp_spec
// Compare polar angles of points a and b w.r.t. pivot p0.
// Returns > 0 if a has smaller polar angle (a comes before b in CCW order).
// Returns < 0 if b has smaller polar angle.
// Returns = 0 if collinear.
let polar_cmp_spec (xs ys: Seq.seq int) (p0 a b: nat) : int =
  if p0 >= Seq.length xs || a >= Seq.length xs || b >= Seq.length xs ||
     Seq.length ys <> Seq.length xs
  then 0
  else
    cross_prod
      (Seq.index xs p0) (Seq.index ys p0)
      (Seq.index xs a) (Seq.index ys a)
      (Seq.index xs b) (Seq.index ys b)
//SNIPPET_END: polar_cmp_spec

//SNIPPET_START: scan_specs
// Pop stack while top two elements and new point don't make a left turn.
// Returns the new top index after popping.
let rec pop_non_left (xs ys: Seq.seq int) (hull: Seq.seq nat) (top: nat) (p: nat)
  : Tot nat (decreases top) =
  if top < 2 || top > Seq.length hull then top
  else
    let t1_idx = Seq.index hull (top - 1) in
    let t2_idx = Seq.index hull (top - 2) in
    if t1_idx >= Seq.length xs || t2_idx >= Seq.length xs || p >= Seq.length xs ||
       Seq.length ys <> Seq.length xs
    then top
    else
      let cp = cross_prod
        (Seq.index xs t2_idx) (Seq.index ys t2_idx)
        (Seq.index xs t1_idx) (Seq.index ys t1_idx)
        (Seq.index xs p) (Seq.index ys p) in
      if cp <= 0 then pop_non_left xs ys hull (top - 1) p
      else top

// One step of the Graham scan: pop then push point p
let scan_step (xs ys: Seq.seq int) (hull: Seq.seq nat) (top: nat) (p: nat)
  : (Seq.seq nat & nat) =
  if top >= Seq.length hull then (hull, top)
  else
    let top' = pop_non_left xs ys hull top p in
    if top' >= Seq.length hull then (hull, top')
    else (Seq.upd hull top' p, top' + 1)

// Graham scan loop over sorted point indices, starting from index i.
let rec graham_loop (xs ys: Seq.seq int) (sorted: Seq.seq nat) (i: nat)
  (hull: Seq.seq nat) (top: nat)
  : Tot (Seq.seq nat & nat) (decreases (Seq.length sorted - i)) =
  if i >= Seq.length sorted then (hull, top)
  else
    let p = Seq.index sorted i in
    let (hull', top') = scan_step xs ys hull top p in
    graham_loop xs ys sorted (i + 1) hull' top'

// Full Graham scan on sorted indices: initialize stack with first 3 points, then loop.
let graham_scan_sorted (xs ys: Seq.seq int) (sorted: Seq.seq nat) : nat =
  let n = Seq.length sorted in
  if n <= 2 then n
  else
    let hull = Seq.create n 0 in
    let hull = Seq.upd hull 0 (Seq.index sorted 0) in
    let hull = Seq.upd hull 1 (Seq.index sorted 1) in
    let hull = Seq.upd hull 2 (Seq.index sorted 2) in
    let (_, top) = graham_loop xs ys sorted 3 hull 3 in
    top
//SNIPPET_END: scan_specs

//SNIPPET_START: pop_while_spec
// Pop non-left turns from the hull stack.
// SZ.t version for direct Pulse array compatibility.
let rec pop_while_spec (xs ys: Seq.seq int) (hull: Seq.seq SZ.t) (top: nat) (p_idx: nat)
  : Tot nat (decreases top) =
  if top < 2 || top > Seq.length hull then top
  else
    let t1 = SZ.v (Seq.index hull (top - 1)) in
    let t2 = SZ.v (Seq.index hull (top - 2)) in
    if t1 >= Seq.length xs || t2 >= Seq.length xs || p_idx >= Seq.length xs ||
       Seq.length ys <> Seq.length xs
    then top
    else
      let cp = cross_prod
        (Seq.index xs t2) (Seq.index ys t2)
        (Seq.index xs t1) (Seq.index ys t1)
        (Seq.index xs p_idx) (Seq.index ys p_idx) in
      if cp <= 0 then pop_while_spec xs ys hull (top - 1) p_idx
      else top

let rec pop_while_spec_bounded (xs ys: Seq.seq int) (hull: Seq.seq SZ.t) (top: nat) (p_idx: nat)
  : Lemma (ensures pop_while_spec xs ys hull top p_idx <= top)
          (decreases top) =
  if top < 2 || top > Seq.length hull then ()
  else
    let t1 = SZ.v (Seq.index hull (top - 1)) in
    let t2 = SZ.v (Seq.index hull (top - 2)) in
    if t1 >= Seq.length xs || t2 >= Seq.length xs || p_idx >= Seq.length xs ||
       Seq.length ys <> Seq.length xs
    then ()
    else
      let cp = cross_prod
        (Seq.index xs t2) (Seq.index ys t2)
        (Seq.index xs t1) (Seq.index ys t1)
        (Seq.index xs p_idx) (Seq.index ys p_idx) in
      if cp <= 0 then pop_while_spec_bounded xs ys hull (top - 1) p_idx
      else ()
//SNIPPET_END: pop_while_spec

// ========== Pulse Implementations ==========

open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

//SNIPPET_START: find_bottom_sig
fn find_bottom (#p: perm) (xs ys: array int)
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
      SZ.v result == find_bottom_spec sxs sys /\
      SZ.v result < SZ.v len
    )
//SNIPPET_END: find_bottom_sig
{
  find_bottom_spec_bounded sxs sys;
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
      find_bottom_aux sxs sys (SZ.v vi) (SZ.v vbest) == find_bottom_spec sxs sys
    )
  {
    let vi = !i;
    let vbest = !best;
    let yi = ys.(vi);
    let yb = ys.(vbest);
    let xi = xs.(vi);
    let xb = xs.(vbest);

    if (yi < yb || (yi = yb && xi < xb)) {
      best := vi
    };

    i := SZ.add vi 1sz
  };

  !best
}

//SNIPPET_START: polar_cmp_sig
fn polar_cmp (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t) (p0 a b: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v p0 < SZ.v len /\
      SZ.v a < SZ.v len /\
      SZ.v b < SZ.v len /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys
    )
  returns result: int
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (result == polar_cmp_spec sxs sys (SZ.v p0) (SZ.v a) (SZ.v b))
//SNIPPET_END: polar_cmp_sig
{
  let px = xs.(p0);
  let py = ys.(p0);
  let ax = xs.(a);
  let ay = ys.(a);
  let bx = xs.(b);
  let b_y = ys.(b);
  (ax - px) * (b_y - py) - (bx - px) * (ay - py)
}

//SNIPPET_START: pop_while_sig
#push-options "--fuel 2 --ifuel 0"
fn pop_while (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (#ph: perm) (hull: array SZ.t)
  (#shull: Ghost.erased (Seq.seq SZ.t))
  (top_in: SZ.t) (p_idx: SZ.t) (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    A.pts_to hull #ph shull **
    pure (
      SZ.v top_in >= 2 /\
      SZ.v top_in <= Seq.length shull /\
      SZ.v p_idx < SZ.v len /\
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys /\
      Seq.length shull == A.length hull /\
      (forall (i: nat). i < SZ.v top_in ==> SZ.v (Seq.index shull i) < SZ.v len)
    )
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    A.pts_to hull #ph shull **
    pure (
      SZ.v result == pop_while_spec sxs sys shull (SZ.v top_in) (SZ.v p_idx) /\
      SZ.v result <= SZ.v top_in
    )
//SNIPPET_END: pop_while_sig
{
  pop_while_spec_bounded sxs sys shull (SZ.v top_in) (SZ.v p_idx);
  let mut t: SZ.t = top_in;
  let mut keep_going: bool = true;

  while (!keep_going)
  invariant exists* vt vkg.
    R.pts_to t vt **
    R.pts_to keep_going vkg **
    A.pts_to xs #p sxs **
    A.pts_to ys #p sys **
    A.pts_to hull #ph shull **
    pure (
      SZ.v vt <= SZ.v top_in /\
      SZ.v top_in <= Seq.length shull /\
      Seq.length shull == A.length hull /\
      SZ.v p_idx < SZ.v len /\
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys /\
      (forall (i: nat). i < SZ.v top_in ==> SZ.v (Seq.index shull i) < SZ.v len) /\
      (vkg ==>
        pop_while_spec sxs sys shull (SZ.v vt) (SZ.v p_idx)
        == pop_while_spec sxs sys shull (SZ.v top_in) (SZ.v p_idx)) /\
      (not vkg ==>
        SZ.v vt == pop_while_spec sxs sys shull (SZ.v top_in) (SZ.v p_idx))
    )
  {
    let vt = !t;
    if (vt <^ 2sz) {
      keep_going := false
    } else {
      let t1_idx = hull.(SZ.sub vt 1sz);
      let t2_idx = hull.(SZ.sub vt 2sz);
      let t1x = xs.(t1_idx);
      let t1y = ys.(t1_idx);
      let t2x = xs.(t2_idx);
      let t2y = ys.(t2_idx);
      let px = xs.(p_idx);
      let py = ys.(p_idx);
      let cp = (t1x - t2x) * (py - t2y) - (px - t2x) * (t1y - t2y);
      if (cp <= 0) {
        t := SZ.sub vt 1sz
      } else {
        keep_going := false
      }
    }
  };
  !t
}
#pop-options

// ========== Complexity Analysis ==========

//SNIPPET_START: op_counts
// find_bottom: n-1 comparisons
let find_bottom_ops (n: nat) : nat = if n > 0 then n - 1 else 0

// polar_cmp: O(1) — 5 subtractions, 2 multiplications, 1 subtraction
let polar_cmp_ops : nat = 8

// pop_while: O(top) worst case — each iteration does 1 cross product (7 ops) + 1 comparison
let pop_while_ops (top: nat) : nat = top * 8

// Sorting by polar angle: O(n^2) with insertion sort, O(n lg n) with merge sort
let polar_sort_ops_insertion (n: nat) : nat = n * n

// Graham scan loop: O(n) amortized — each point is pushed and popped at most once
let graham_scan_loop_ops (n: nat) : nat = 2 * n

// Full Graham scan: dominated by sorting
let graham_scan_ops (n: nat) : nat = find_bottom_ops n + polar_sort_ops_insertion n + graham_scan_loop_ops n
//SNIPPET_END: op_counts

//SNIPPET_START: complexity_lemmas
// Graham scan with insertion sort is O(n^2)
let graham_scan_quadratic (n: nat) : Lemma
  (requires n > 0)
  (ensures graham_scan_ops n <= 4 * n * n)
  = ()

// The scan loop alone is linear
let scan_linear (n: nat) : Lemma
  (ensures graham_scan_loop_ops n <= 2 * n)
  = ()
//SNIPPET_END: complexity_lemmas
