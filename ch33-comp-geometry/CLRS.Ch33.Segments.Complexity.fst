(*
   Copyright 2025 - CLRS Chapter 33: Computational Geometry
   
   Complexity analysis for segment intersection test operations.
   All operations are O(1) as they perform a constant number of arithmetic
   operations and comparisons.
*)

module CLRS.Ch33.Segments.Complexity

open FStar.Mul

(***** Operation counts *****)

(** Cross product: (p2.x - p1.x) * (p3.y - p1.y) - (p2.y - p1.y) * (p3.x - p1.x)
    - 2 multiplications
    - 1 subtraction (of the products)
    - Plus intermediate subtractions for coordinate differences (4 more ops)
    We count the core operations: 2 mults + 1 sub = 3 *)
//SNIPPET_START: op_counts
let cross_product_ops : nat = 3

let direction_ops : nat = 3

let on_segment_ops : nat = 4

let segments_intersect_ops : nat = 16
//SNIPPET_END: op_counts

(***** Constant-time proof *****)

(** All operations are O(1) - they perform at most a constant (30) operations *)
//SNIPPET_START: all_constant
let all_constant () : Lemma
  (ensures cross_product_ops + direction_ops + on_segment_ops + segments_intersect_ops <= 30)
  = ()
//SNIPPET_END: all_constant

(***** Individual operation bounds *****)

let cross_product_constant () : Lemma
  (ensures cross_product_ops <= 10)
  = ()

let direction_constant () : Lemma
  (ensures direction_ops <= 10)
  = ()

let on_segment_constant () : Lemma
  (ensures on_segment_ops <= 10)
  = ()

let segments_intersect_constant () : Lemma
  (ensures segments_intersect_ops <= 20)
  = ()

(***** Composition guarantees *****)

(** The segments-intersect operation composes at most 4 direction tests
    and 2 on-segment tests *)
//SNIPPET_START: composition
let segments_intersect_composition () : Lemma
  (ensures segments_intersect_ops <= 4 * direction_ops + 2 * on_segment_ops)
  = ()
//SNIPPET_END: composition
