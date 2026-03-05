(*
   Graham Scan — CLRS Chapter 33, Section 33.3
   
   Pure specifications for the Graham scan convex hull algorithm.
   
   Implements:
   1. find_bottom: Find the starting point (minimum y, then minimum x)
   2. polar_cmp: Compare polar angles of two points w.r.t. a pivot
   3. Pure specifications for the complete Graham scan algorithm
   
   Complexity: O(n lg n) dominated by sorting (scan is O(n) amortized).
*)

module CLRS.Ch33.GrahamScan.Spec
open FStar.Mul
open CLRS.Ch33.Segments.Spec

module SZ = FStar.SizeT
module Seq = FStar.Seq

// ========== Convenience alias ==========

// Re-export cross_product_spec as cross_prod for local readability
let cross_prod (x1 y1 x2 y2 x3 y3: int) : int =
  cross_product_spec x1 y1 x2 y2 x3 y3

// ========== Pure Specifications ==========

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
//SNIPPET_END: pop_while_spec

// ========== Convex Hull Correctness Definitions ==========

//SNIPPET_START: correctness_defs
// A sequence of hull indices makes all left turns (convex position).
let all_left_turns (xs ys: Seq.seq int) (hull: Seq.seq nat) (top: nat) : prop =
  top <= Seq.length hull /\
  Seq.length ys == Seq.length xs /\
  (forall (i: nat). i + 2 < top ==>
    Seq.index hull i < Seq.length xs /\
    Seq.index hull (i + 1) < Seq.length xs /\
    Seq.index hull (i + 2) < Seq.length xs /\
    cross_prod (Seq.index xs (Seq.index hull i))
               (Seq.index ys (Seq.index hull i))
               (Seq.index xs (Seq.index hull (i + 1)))
               (Seq.index ys (Seq.index hull (i + 1)))
               (Seq.index xs (Seq.index hull (i + 2)))
               (Seq.index ys (Seq.index hull (i + 2))) > 0)

// find_bottom returns the bottom-most point (minimum y, tiebreak min x).
let is_bottommost (xs ys: Seq.seq int) (m: nat) : prop =
  m < Seq.length xs /\
  Seq.length ys == Seq.length xs /\
  (forall (k: nat). k < Seq.length xs ==>
    Seq.index ys m < Seq.index ys k \/
    (Seq.index ys m = Seq.index ys k /\ Seq.index xs m <= Seq.index xs k))
//SNIPPET_END: correctness_defs
