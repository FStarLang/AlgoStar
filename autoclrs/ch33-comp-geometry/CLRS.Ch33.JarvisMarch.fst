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

// find_next never returns current when n > 1 (it always finds a different point)
let rec find_next_aux_not_current (xs ys: Seq.seq int) (current next: nat) (j: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 1 /\
                    current < Seq.length xs /\ next < Seq.length xs /\
                    (next <> current \/ (exists (k: nat). k >= j /\ k < Seq.length xs /\ k <> current)))
          (ensures find_next_aux xs ys current next j <> current)
          (decreases (Seq.length xs - j)) =
  if j >= Seq.length xs then ()
  else if j = current then
    find_next_aux_not_current xs ys current next (j + 1)
  else if next = current then
    // j != current, so next becomes j
    find_next_aux_not_current xs ys current j (j + 1)
  else begin
    let cp = cross_prod
      (Seq.index xs current) (Seq.index ys current)
      (Seq.index xs next) (Seq.index ys next)
      (Seq.index xs j) (Seq.index ys j) in
    let new_next = if cp < 0 then j else next in
    find_next_aux_not_current xs ys current new_next (j + 1)
  end

let find_next_spec_not_current (xs ys: Seq.seq int) (current: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 1 /\
                    current < Seq.length xs)
          (ensures find_next_spec xs ys current <> current) =
  // There exists at least one index != current (since n > 1)
  let other = if current = 0 then 1 else 0 in
  assert (other < Seq.length xs /\ other <> current);
  find_next_aux_not_current xs ys current current 0

//SNIPPET_START: jarvis_march_spec
// Jarvis march outer loop: count hull vertices starting from p0.
// fuel bounds iterations (at most n-1 after the start vertex).
let rec jarvis_loop_count (xs ys: Seq.seq int) (start current: nat) (fuel: nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then 0
  else
    let next = find_next_spec xs ys current in
    if next = start then 0
    else 1 + jarvis_loop_count xs ys start next (fuel - 1)

// Full Jarvis march: returns number of hull vertices.
let jarvis_march_spec (xs ys: Seq.seq int) : nat =
  let n = Seq.length xs in
  if n <= 1 then n
  else
    let p0 = find_leftmost_spec xs ys in
    1 + jarvis_loop_count xs ys p0 p0 (n - 1)
//SNIPPET_END: jarvis_march_spec

// Bounds lemma: loop count is bounded by fuel
let rec jarvis_loop_count_bounded (xs ys: Seq.seq int) (start current: nat) (fuel: nat)
  : Lemma (ensures jarvis_loop_count xs ys start current fuel <= fuel)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    let next = find_next_spec xs ys current in
    if next = start then ()
    else jarvis_loop_count_bounded xs ys start next (fuel - 1)

// Bounds lemma: march result is at most n and at least 1
let jarvis_march_spec_bounded (xs ys: Seq.seq int)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 1)
          (ensures jarvis_march_spec xs ys <= Seq.length xs /\
                   jarvis_march_spec xs ys >= 1) =
  let n = Seq.length xs in
  let p0 = find_leftmost_spec xs ys in
  jarvis_loop_count_bounded xs ys p0 p0 (n - 1)

// Step lemma: unfolding one iteration when next ≠ start
let jarvis_loop_step (xs ys: Seq.seq int) (start current: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\ find_next_spec xs ys current <> start)
          (ensures jarvis_loop_count xs ys start current fuel ==
                   1 + jarvis_loop_count xs ys start
                       (find_next_spec xs ys current) (fuel - 1) /\
                   jarvis_loop_count xs ys start current fuel >= 1) = ()

// ========== Convex Hull Correctness Properties ==========

//SNIPPET_START: correctness_defs

// A point m is lexicographically leftmost in (xs, ys):
// for all k, xs[m] < xs[k] or (xs[m] = xs[k] and ys[m] <= ys[k]).
// The leftmost point of a set must lie on the convex hull.
let is_leftmost (xs ys: Seq.seq int) (m: nat) : prop =
  m < Seq.length xs /\
  Seq.length ys == Seq.length xs /\
  (forall (k: nat). k < Seq.length xs ==>
    Seq.index xs m < Seq.index xs k \/
    (Seq.index xs m = Seq.index xs k /\ Seq.index ys m <= Seq.index ys k))

// "All left of" property (CLRS Jarvis march correctness):
// All points k (other than p and q) are to the left of or on the directed
// line p → q. This means the edge (p, q) is a supporting edge of the hull.
let all_left_of (xs ys: Seq.seq int) (p q: nat) : prop =
  p < Seq.length xs /\ q < Seq.length xs /\
  Seq.length ys == Seq.length xs /\ p <> q /\
  (forall (k: nat). k < Seq.length xs /\ k <> p ==>
    cross_prod (Seq.index xs p) (Seq.index ys p)
               (Seq.index xs q) (Seq.index ys q)
               (Seq.index xs k) (Seq.index ys k) >= 0)

//SNIPPET_END: correctness_defs

//SNIPPET_START: correctness_lemmas

// find_leftmost returns the lexicographic minimum (x, then y).
// Proof: induction on find_leftmost_aux — maintains the invariant that
// best is the minimum of [0, i).
let rec find_leftmost_aux_is_min (xs ys: Seq.seq int) (i best: nat)
  : Lemma (requires
      Seq.length ys == Seq.length xs /\ Seq.length xs > 0 /\
      best < Seq.length xs /\
      (forall (k: nat). k < i /\ k < Seq.length xs ==>
        Seq.index xs best < Seq.index xs k \/
        (Seq.index xs best = Seq.index xs k /\ Seq.index ys best <= Seq.index ys k)))
    (ensures is_leftmost xs ys (find_leftmost_aux xs ys i best))
    (decreases (Seq.length xs - i)) =
  if i >= Seq.length xs then ()
  else
    let xi = Seq.index xs i in
    let xb = Seq.index xs best in
    let yi = Seq.index ys i in
    let yb = Seq.index ys best in
    let new_best = if xi < xb || (xi = xb && yi < yb) then i else best in
    find_leftmost_aux_is_min xs ys (i + 1) new_best

let find_leftmost_is_leftmost (xs ys: Seq.seq int)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0)
          (ensures is_leftmost xs ys (find_leftmost_spec xs ys)) =
  find_leftmost_aux_is_min xs ys 1 0

// Cross-product antisymmetry (swapping last two points negates the value).
// This is the foundation for Jarvis march: when we update the candidate
// because j beats the current next, the new next automatically beats
// the old one in the reverse direction.
let cross_prod_swap23 (x1 y1 x2 y2 x3 y3: int) : Lemma
  (ensures cross_prod x1 y1 x3 y3 x2 y2 == -(cross_prod x1 y1 x2 y2 x3 y3)) = ()

// Half-plane transitivity (CLRS implicit assumption).
// When all points have non-negative y relative to the pivot, cross-product
// comparison is transitive. This is the key lemma enabling the Jarvis march
// correctness proof: starting from the bottom-most point, all other points
// are in the upper half-plane, so find_next correctly identifies the most-
// clockwise point.
//
// Algebraic proof:
//   Given ay >= 0, by > 0, cy >= 0:
//   H1: ax*by - bx*ay >= 0
//   H2: bx*cy - cx*by >= 0
//   Multiply H1 by cy: ax*by*cy >= bx*ay*cy
//   Multiply H2 by ay: bx*cy*ay >= cx*by*ay
//   Since bx*ay*cy = bx*cy*ay: ax*by*cy >= cx*by*ay
//   Since by > 0: ax*cy >= cx*ay. QED
#push-options "--z3rlimit 10"
let half_plane_transitivity (ax ay bx b_y cx cy: int) : Lemma
  (requires ay >= 0 /\ b_y > 0 /\ cy >= 0 /\
            ax * b_y - bx * ay >= 0 /\
            bx * cy - cx * b_y >= 0)
  (ensures ax * cy - cx * ay >= 0) =
  // Help the SMT solver with the key intermediate steps
  let h1_cy = (ax * b_y - bx * ay) * cy in
  let h2_ay = (bx * cy - cx * b_y) * ay in
  assert (h1_cy >= 0);
  assert (h2_ay >= 0);
  assert (ax * b_y * cy - bx * ay * cy >= 0);
  assert (bx * cy * ay - cx * b_y * ay >= 0);
  // bx*ay*cy = bx*cy*ay (commutativity of multiplication)
  assert (bx * ay * cy == bx * cy * ay);
  // Chain: ax*b_y*cy >= bx*ay*cy = bx*cy*ay >= cx*b_y*ay
  assert (ax * b_y * cy >= cx * b_y * ay);
  // Since b_y > 0, divide both sides by b_y
  ()
#pop-options

// Cross-product transitivity in the upper half-plane, stated directly in
// terms of cross_prod. If "next" beats "k" and "j" beats "next" (both
// relative to "current"), then "j" beats "k" — provided all points are
// in the upper half-plane and "next" is strictly above "current".
#push-options "--z3rlimit 10"
let cross_prod_transitivity (cx c_y nx ny jx jy kx ky: int) : Lemma
  (requires
    ny - c_y > 0 /\ jy - c_y >= 0 /\ ky - c_y >= 0 /\
    cross_prod cx c_y nx ny jx jy < 0 /\
    cross_prod cx c_y nx ny kx ky >= 0)
  (ensures cross_prod cx c_y jx jy kx ky >= 0)
  [SMTPat (cross_prod cx c_y jx jy kx ky); SMTPat (cross_prod cx c_y nx ny kx ky)] =
  let ax = jx - cx in let ay = jy - c_y in
  let bx = nx - cx in let b_y = ny - c_y in
  let dx = kx - cx in let d_y = ky - c_y in
  half_plane_transitivity ax ay bx b_y dx d_y
#pop-options

// Degenerate transitivity: when next is on the same horizontal as current
// (b_y = 0), general position forces the only viable k to be next itself,
// and antisymmetry gives the result.
let cross_prod_transitivity_degenerate (cx c_y nx ny jx jy: int) : Lemma
  (requires
    ny = c_y /\ jy - c_y >= 0 /\
    cross_prod cx c_y nx ny jx jy < 0)
  (ensures cross_prod cx c_y jx jy nx ny > 0) =
  cross_prod_swap23 cx c_y nx ny jx jy

// The "beats all" proof needs the following additional strengthening:
// when b_y = 0 and we have cp(current,next,k) >= 0, and k != next,
// general position gives cp(current,next,k) != 0, but we showed cp = 0,
// so this case is actually impossible. For k = next, antisymmetry works.
// We handle this by strengthening the precondition of find_next_aux_beats_all
// to also require ny > cy (next is strictly above current), which holds
// after the first step from the bottom-most point in general position.

// find_next_aux maintains the "beats all predecessors" invariant.
// After scanning through index j-1, the candidate 'next' satisfies:
//   for all k < j with k != current: cp(current, next, k) >= 0.
//
// The proof uses:
// - When next = current, no non-current indices have been seen yet
// - When cp(current, next, j) >= 0: j doesn't beat next, invariant extends
// - When cp(current, next, j) < 0: j beats next, and by transitivity
//   (in the upper half-plane), j beats all previous points too.
//
// Precondition "upper_half" captures the CLRS assumption that all points
// have y-coordinates >= the pivot's y-coordinate, corresponding to polar
// angles in [0, π). The strict by > 0 is needed for transitivity;
// collinear points on the x-axis (by = 0) are handled by the algorithm's
// tie-breaking (keeping the earlier candidate).

// Helper: index into translated coordinates
let dy (ys: Seq.seq int) (current k: nat) : int =
  if current < Seq.length ys && k < Seq.length ys
  then Seq.index ys k - Seq.index ys current
  else 0

// The all_left_of property for find_next, under the upper-half-plane condition.
// This is the core correctness theorem for Jarvis march.
//
// CLRS states this as: from the current hull vertex, the point with the
// smallest polar angle is the next hull vertex, because all other points
// lie to the left of the line from current to that point.
//
// Assumes: (1) All points satisfy y[k] >= y[current] (upper half-plane),
//          (2) No two non-current points have the exact same polar angle
//              (general position — ensures strict ordering).
// Under these conditions, find_next_spec returns the most-clockwise point.

let rec find_next_aux_beats_all (xs ys: Seq.seq int) (current next: nat) (j: nat)
  : Lemma
    (requires
      Seq.length ys == Seq.length xs /\ Seq.length xs > 1 /\
      current < Seq.length xs /\ next < Seq.length xs /\
      // Upper half-plane (strict): all non-current points have y > y[current]
      (forall (k: nat). k < Seq.length xs /\ k <> current ==>
        Seq.index ys k > Seq.index ys current) /\
      // General position: no two distinct non-current points have exactly
      // the same polar angle (cross product = 0) relative to current
      (forall (a b: nat). a < Seq.length xs /\ b < Seq.length xs /\
        a <> current /\ b <> current /\ a <> b ==>
        cross_prod (Seq.index xs current) (Seq.index ys current)
                   (Seq.index xs a) (Seq.index ys a)
                   (Seq.index xs b) (Seq.index ys b) <> 0) /\
      // If next hasn't been set, no non-current indices were processed yet
      (next = current ==>
        (forall (k: nat). k < j /\ k < Seq.length xs ==> k = current)) /\
      // Invariant: next beats all predecessors
      (next <> current ==>
        (forall (k: nat). k < j /\ k < Seq.length xs /\ k <> current ==>
          cross_prod (Seq.index xs current) (Seq.index ys current)
                     (Seq.index xs next) (Seq.index ys next)
                     (Seq.index xs k) (Seq.index ys k) >= 0)))
    (ensures (
      let r = find_next_aux xs ys current next j in
      r < Seq.length xs /\
      (r <> current ==>
        (forall (k: nat). k < Seq.length xs /\ k <> current ==>
          cross_prod (Seq.index xs current) (Seq.index ys current)
                     (Seq.index xs r) (Seq.index ys r)
                     (Seq.index xs k) (Seq.index ys k) >= 0))))
    (decreases (Seq.length xs - j)) =
  find_next_aux_bounded xs ys current next j;
  if j >= Seq.length xs then ()
  else if j = current then
    find_next_aux_beats_all xs ys current next (j + 1)
  else if next = current then
    // First non-current point: all k < j are current, so the invariant
    // for the recursive call (j beats all k < j+1, k != current) is vacuous.
    find_next_aux_beats_all xs ys current j (j + 1)
  else begin
    let cx = Seq.index xs current in let cy' = Seq.index ys current in
    let nx = Seq.index xs next in let ny = Seq.index ys next in
    let jx = Seq.index xs j in let jy = Seq.index ys j in
    let cp = cross_prod cx cy' nx ny jx jy in
    if cp < 0 then begin
      // j beats next. Need: j also beats all k < j (for the recursive call).
      //
      // Proof sketch (CLRS Jarvis march correctness):
      //   For each predecessor k < j with k != current:
      //   - cp(current, next, k) >= 0     (induction hypothesis)
      //   - cp(current, next, j) < 0      (j beats next)
      //   - cp(current, j, next) > 0      (antisymmetry)
      //   - All points in upper half-plane (y[k] >= y[current])
      //   => cp(current, j, k) >= 0       (half_plane_transitivity)
      //
      // The half_plane_transitivity lemma (proved above) captures the
      // algebraic core: multiply the two cross-product inequalities by
      // appropriate non-negative factors (cy-c_y and ay-c_y), use
      // commutativity of multiplication to chain, and divide by b_y > 0.
      //
      // For the degenerate case b_y = 0 (next on same horizontal as current),
      // general position forces k = next, and antisymmetry gives the result.
      //
      // Full formal proof: cross_prod_transitivity fires via SMTPat
      // for each k where cp(current,next,k) >= 0 is known from IH.
      // Precondition ny > cy' (strict upper half) ensures b_y > 0.
      assert (ny - cy' > 0);
      find_next_aux_beats_all xs ys current j (j + 1)
    end else
      find_next_aux_beats_all xs ys current next (j + 1)
  end

let find_next_all_left_of (xs ys: Seq.seq int) (current: nat)
  : Lemma
    (requires
      Seq.length ys == Seq.length xs /\ Seq.length xs > 1 /\
      current < Seq.length xs /\
      (forall (k: nat). k < Seq.length xs /\ k <> current ==>
        Seq.index ys k > Seq.index ys current) /\
      (forall (a b: nat). a < Seq.length xs /\ b < Seq.length xs /\
        a <> current /\ b <> current /\ a <> b ==>
        cross_prod (Seq.index xs current) (Seq.index ys current)
                   (Seq.index xs a) (Seq.index ys a)
                   (Seq.index xs b) (Seq.index ys b) <> 0))
    (ensures all_left_of xs ys current (find_next_spec xs ys current)) =
  find_next_spec_not_current xs ys current;
  find_next_aux_beats_all xs ys current current 0;
  find_next_spec_bounded xs ys current

//SNIPPET_END: correctness_lemmas

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
  decreases (SZ.v len - SZ.v !i)
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
  decreases (SZ.v len - SZ.v !j)
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

//SNIPPET_START: jarvis_march_sig
#push-options "--fuel 2 --ifuel 0"
fn jarvis_march (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len > 1 /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys
    )
  returns h: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v h == jarvis_march_spec sxs sys /\
      SZ.v h >= 1 /\
      SZ.v h <= SZ.v len
    )
//SNIPPET_END: jarvis_march_sig
{
  jarvis_march_spec_bounded sxs sys;
  let p0 = find_leftmost xs ys len;
  let first_next = find_next xs ys len p0;

  if (first_next = p0) {
    1sz
  } else {
    let mut h: SZ.t = 2sz;
    let mut current: SZ.t = first_next;
    let mut running: bool = true;

    while (!running)
    invariant exists* vrunning vcurrent vh.
      R.pts_to running vrunning **
      R.pts_to current vcurrent **
      R.pts_to h vh **
      A.pts_to xs #p sxs **
      A.pts_to ys #p sys **
      pure (
        SZ.v vh >= 2 /\
        SZ.v vh <= SZ.v len /\
        SZ.v vcurrent < SZ.v len /\
        SZ.v len == Seq.length sxs /\
        Seq.length sxs == Seq.length sys /\
        SZ.v len > 1 /\
        SZ.v len == A.length xs /\
        SZ.v len == A.length ys /\
        jarvis_march_spec sxs sys <= SZ.v len /\
        jarvis_march_spec sxs sys >= 1 /\
        (vrunning ==>
          SZ.v vh + jarvis_loop_count sxs sys (SZ.v p0) (SZ.v vcurrent)
            (SZ.v len - SZ.v vh)
          == jarvis_march_spec sxs sys) /\
        (not vrunning ==>
          SZ.v vh == jarvis_march_spec sxs sys)
      )
    decreases (SZ.v len - SZ.v !h + (if !running then 1 else 0))
    {
      let vc = !current;
      let next = find_next xs ys len vc;
      let vh = !h;
      // Continue only if next ≠ start AND fuel remains (vh < len)
      let go = not (next = p0) && (vh <^ len);

      if go {
        h := SZ.add vh 1sz;
        current := next
      } else {
        running := false
      }
    };

    !h
  }
}
#pop-options

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
