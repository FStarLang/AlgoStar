(*
   Computational Geometry Primitives — CLRS Chapter 33, Section 33.1

   Complexity interface: all segment operations are O(1).
*)

module CLRS.Ch33.Segments.Complexity

val cross_product_ops : nat
val direction_ops : nat
val on_segment_ops : nat
val segments_intersect_ops : nat

val all_constant (_:unit) : Lemma
  (ensures cross_product_ops <= 7 /\
           direction_ops <= 7 /\
           on_segment_ops <= 6 /\
           segments_intersect_ops <= 52)

val segments_intersect_bounded (_:unit) : Lemma
  (ensures segments_intersect_ops == 4 * cross_product_ops + 4 * on_segment_ops)
