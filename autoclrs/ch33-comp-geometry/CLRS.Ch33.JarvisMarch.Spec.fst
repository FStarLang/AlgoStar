(*
   Jarvis's March (Gift Wrapping) — CLRS Chapter 33, Section 33.3

   Pure specifications for the Jarvis march convex hull algorithm.

   Implements:
   1. find_leftmost: Find the starting point (minimum x, then minimum y)
   2. find_next: Find the next hull vertex by cross-product comparison
   3. jarvis_march: Full convex hull computation

   Complexity: O(nh) where n = number of input points, h = number of hull vertices.
*)

module CLRS.Ch33.JarvisMarch.Spec
open FStar.Mul
open CLRS.Ch33.Segments.Spec

module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Convenience alias ==========

let cross_prod (x1 y1 x2 y2 x3 y3: int) : int =
  cross_product_spec x1 y1 x2 y2 x3 y3

// ========== Pure Specifications ==========

//SNIPPET_START: find_leftmost_spec
// Find index of leftmost point (min x, break ties by min y).
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

//SNIPPET_START: find_next_spec
// Find next hull vertex: the point that all others lie to the left of
// the line from current to that point (most clockwise turn from current).
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

//SNIPPET_START: jarvis_march_spec
// Jarvis march outer loop: count hull vertices starting from p0.
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

// ========== Convex Hull Correctness Definitions ==========

//SNIPPET_START: correctness_defs
// A point m is lexicographically leftmost in (xs, ys).
let is_leftmost (xs ys: Seq.seq int) (m: nat) : prop =
  m < Seq.length xs /\
  Seq.length ys == Seq.length xs /\
  (forall (k: nat). k < Seq.length xs ==>
    Seq.index xs m < Seq.index xs k \/
    (Seq.index xs m = Seq.index xs k /\ Seq.index ys m <= Seq.index ys k))

// "All left of" property: all points k (other than p and q) are to the
// left of or on the directed line p → q.
let all_left_of (xs ys: Seq.seq int) (p q: nat) : prop =
  p < Seq.length xs /\ q < Seq.length xs /\
  Seq.length ys == Seq.length xs /\ p <> q /\
  (forall (k: nat). k < Seq.length xs /\ k <> p ==>
    cross_prod (Seq.index xs p) (Seq.index ys p)
               (Seq.index xs q) (Seq.index ys q)
               (Seq.index xs k) (Seq.index ys k) >= 0)

// Helper: index into translated coordinates
let dy (ys: Seq.seq int) (current k: nat) : int =
  if current < Seq.length ys && k < Seq.length ys
  then Seq.index ys k - Seq.index ys current
  else 0

// Characterization of a valid Jarvis march hull output.
// hull[0] is the leftmost point, and each subsequent vertex is
// the result of find_next applied to its predecessor.
let valid_jarvis_hull (xs ys: Seq.seq int) (hull: Seq.seq SZ.t) (h: nat) : prop =
  h >= 1 /\
  h <= Seq.length hull /\
  Seq.length ys == Seq.length xs /\
  SZ.v (Seq.index hull 0) == find_leftmost_spec xs ys /\
  (forall (i: nat). i < h ==> SZ.v (Seq.index hull i) < Seq.length xs) /\
  (forall (i: nat). i >= 1 /\ i < h ==>
    SZ.v (Seq.index hull i) == find_next_spec xs ys (SZ.v (Seq.index hull (i - 1))))
//SNIPPET_END: correctness_defs
