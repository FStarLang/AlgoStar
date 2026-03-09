(*
   Computational Geometry Primitives — CLRS Chapter 33, Section 33.1
   
   Lemma signatures for cross product and orientation properties.
*)

module CLRS.Ch33.Segments.Lemmas
open CLRS.Ch33.Segments.Spec
open FStar.Mul

//SNIPPET_START: cross_product_properties
// Antisymmetry: swapping p2 ↔ p3 negates the cross product
val cross_product_antisymmetric (x1 y1 x2 y2 x3 y3: int) : Lemma
  (ensures cross_product_spec x1 y1 x3 y3 x2 y2 ==
           -(cross_product_spec x1 y1 x2 y2 x3 y3))

// Swapping p2 ↔ p3 reverses the turn direction
val orient_antisymmetric (x1 y1 x2 y2 x3 y3: int) : Lemma
  (ensures orient x1 y1 x3 y3 x2 y2 ==
    (match orient x1 y1 x2 y2 x3 y3 with
     | CCW -> CW | CW -> CCW | Collinear -> Collinear))

// Translation invariance: shifting all points preserves orientation
val cross_product_translation (x1 y1 x2 y2 x3 y3 dx dy: int) : Lemma
  (ensures cross_product_spec (x1+dx) (y1+dy) (x2+dx) (y2+dy) (x3+dx) (y3+dy)
        == cross_product_spec x1 y1 x2 y2 x3 y3)

// Degenerate: p2 = p1 implies collinear
val cross_product_degenerate_p2 (x1 y1 x3 y3: int) : Lemma
  (ensures cross_product_spec x1 y1 x1 y1 x3 y3 == 0)

// Degenerate: p3 = p1 implies collinear
val cross_product_degenerate_p3 (x1 y1 x2 y2: int) : Lemma
  (ensures cross_product_spec x1 y1 x2 y2 x1 y1 == 0)
//SNIPPET_END: cross_product_properties
