(*
   Computational Geometry Primitives — CLRS Chapter 33, Section 33.1
   
   Pure specifications for:
   1. Cross product direction test for three points
   2. Segment intersection test using orientation tests
   
   Based on CLRS Section 33.1: Line-segment properties
*)

module CLRS.Ch33.Segments.Spec
open FStar.Mul

// ========== Helper Functions ==========

let max_int (x y: int) : int = if x >= y then x else y
let min_int (x y: int) : int = if x <= y then x else y

// ========== Pure Specifications ==========

//SNIPPET_START: pure_specs
// Cross product (p2-p1) × (p3-p1) = (x2-x1)*(y3-y1) - (x3-x1)*(y2-y1)
// Returns:
//   > 0 if p3 is to the left of line p1->p2 (counter-clockwise)
//   < 0 if p3 is to the right of line p1->p2 (clockwise)
//   = 0 if p1, p2, p3 are collinear
let cross_product_spec (x1 y1 x2 y2 x3 y3: int) : int =
  (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1)

// Direction from p1 through p2 to p3
// Returns the cross product value
let direction_spec (x1 y1 x2 y2 x3 y3: int) : int =
  cross_product_spec x1 y1 x2 y2 x3 y3

// Check if point (x, y) is on the segment from (x1, y1) to (x2, y2)
// Assumes the three points are collinear
let on_segment_spec (x1 y1 x2 y2 x y: int) : bool =
  (x <= max_int x1 x2) && (x >= min_int x1 x2) &&
  (y <= max_int y1 y2) && (y >= min_int y1 y2)
//SNIPPET_END: pure_specs

//SNIPPET_START: segments_intersect_spec
// Check if segments (p1, p2) and (p3, p4) intersect
// Using the standard orientation-based algorithm from CLRS
let segments_intersect_spec (x1 y1 x2 y2 x3 y3 x4 y4: int) : bool =
  let d1 = direction_spec x3 y3 x4 y4 x1 y1 in
  let d2 = direction_spec x3 y3 x4 y4 x2 y2 in
  let d3 = direction_spec x1 y1 x2 y2 x3 y3 in
  let d4 = direction_spec x1 y1 x2 y2 x4 y4 in
  
  // General case: segments straddle each other
  if (((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) &&
      ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0)))
  then true
  // Special cases: collinear points
  else if (d1 = 0 && on_segment_spec x3 y3 x4 y4 x1 y1) then true
  else if (d2 = 0 && on_segment_spec x3 y3 x4 y4 x2 y2) then true
  else if (d3 = 0 && on_segment_spec x1 y1 x2 y2 x3 y3) then true
  else if (d4 = 0 && on_segment_spec x1 y1 x2 y2 x4 y4) then true
  else false
//SNIPPET_END: segments_intersect_spec

// ========== Geometric Properties ==========

//SNIPPET_START: orientation
type orientation = | CCW | CW | Collinear

let orient (x1 y1 x2 y2 x3 y3: int) : orientation =
  let cp = cross_product_spec x1 y1 x2 y2 x3 y3 in
  if cp > 0 then CCW
  else if cp < 0 then CW
  else Collinear
//SNIPPET_END: orientation
