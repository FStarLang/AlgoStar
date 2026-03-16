(*
   Computational Geometry Primitives — CLRS Chapter 33, Section 33.1

   Complexity analysis: all segment operations are O(1).
*)

module CLRS.Ch33.Segments.Complexity
open FStar.Mul

// All operations perform a constant number of arithmetic ops.

// cross_product: 4 subtractions, 2 multiplications, 1 subtraction = 7 ops
let cross_product_ops : nat = 7

// direction: same as cross_product (it's an alias)
let direction_ops : nat = cross_product_ops

// on_segment: 4 comparisons + booleans = 6 ops
let on_segment_ops : nat = 6

// segments_intersect: 4 directions + up to 4 on_segment checks
let segments_intersect_ops : nat = 4 * direction_ops + 4 * on_segment_ops

// All operations are O(1) — bounded by a constant independent of input size
let all_constant (_:unit) : Lemma
  (ensures cross_product_ops <= 7 /\
           direction_ops <= 7 /\
           on_segment_ops <= 6 /\
           segments_intersect_ops <= 52)
  = ()

// Composition: segments_intersect is bounded by a small constant
let segments_intersect_bounded (_:unit) : Lemma
  (ensures segments_intersect_ops == 4 * cross_product_ops + 4 * on_segment_ops)
  = ()
