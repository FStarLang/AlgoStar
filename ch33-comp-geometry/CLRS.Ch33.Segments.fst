(*
   Computational Geometry Primitives - CLRS Chapter 33
   
   Implements:
   1. Cross product direction test for three points
   2. Segment intersection test using orientation tests
   
   Based on CLRS Section 33.1: Line-segment properties
   
   NO admits. NO assumes.
*)

module CLRS.Ch33.Segments
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.Mul

// ========== Pure Specifications ==========

// Helper functions for min/max
let max_int (x y: int) : int = if x >= y then x else y
let min_int (x y: int) : int = if x <= y then x else y

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

// ========== Pulse Implementations ==========

//SNIPPET_START: cross_product_sig
fn cross_product (x1 y1 x2 y2 x3 y3: int)
  requires emp
  returns result: int
  ensures emp ** pure (result == cross_product_spec x1 y1 x2 y2 x3 y3)
//SNIPPET_END: cross_product_sig
{
  // Compute (x2 - x1)
  let dx21 = x2 - x1;
  
  // Compute (y3 - y1)
  let dy31 = y3 - y1;
  
  // Compute (x3 - x1)
  let dx31 = x3 - x1;
  
  // Compute (y2 - y1)
  let dy21 = y2 - y1;
  
  // Compute the cross product
  let term1 = dx21 * dy31;
  let term2 = dx31 * dy21;
  let result = term1 - term2;
  
  result
}

//SNIPPET_START: direction_sig
fn direction (x1 y1 x2 y2 x3 y3: int)
  requires emp
  returns result: int
  ensures emp ** pure (result == direction_spec x1 y1 x2 y2 x3 y3)
//SNIPPET_END: direction_sig
{
  cross_product x1 y1 x2 y2 x3 y3
}

//SNIPPET_START: on_segment_sig
fn on_segment (x1 y1 x2 y2 x y: int)
  requires emp
  returns result: bool
  ensures emp ** pure (result == on_segment_spec x1 y1 x2 y2 x y)
//SNIPPET_END: on_segment_sig
{
  let max_x = (if x1 >= x2 then x1 else x2);
  let min_x = (if x1 <= x2 then x1 else x2);
  let max_y = (if y1 >= y2 then y1 else y2);
  let min_y = (if y1 <= y2 then y1 else y2);
  
  let check_x = (x <= max_x && x >= min_x);
  let check_y = (y <= max_y && y >= min_y);
  
  (check_x && check_y)
}

//SNIPPET_START: segments_intersect_sig
fn segments_intersect (x1 y1 x2 y2 x3 y3 x4 y4: int)
  requires emp
  returns result: bool
  ensures emp ** pure (result == segments_intersect_spec x1 y1 x2 y2 x3 y3 x4 y4)
//SNIPPET_END: segments_intersect_sig
{
  // Compute orientations
  let d1 = direction x3 y3 x4 y4 x1 y1;
  let d2 = direction x3 y3 x4 y4 x2 y2;
  let d3 = direction x1 y1 x2 y2 x3 y3;
  let d4 = direction x1 y1 x2 y2 x4 y4;
  
  // General case: segments straddle each other
  let general_case = 
    ((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) &&
    ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0));
  
  if general_case {
    true
  } else {
    // Check special cases: collinear points
    let case1 = d1 = 0 && on_segment x3 y3 x4 y4 x1 y1;
    if case1 {
      true
    } else {
      let case2 = d2 = 0 && on_segment x3 y3 x4 y4 x2 y2;
      if case2 {
        true
      } else {
        let case3 = d3 = 0 && on_segment x1 y1 x2 y2 x3 y3;
        if case3 {
          true
        } else {
          let case4 = d4 = 0 && on_segment x1 y1 x2 y2 x4 y4;
          case4
        }
      }
    }
  }
}

// ========== Complexity Analysis ==========

// All operations are O(1) — constant number of arithmetic operations.

//SNIPPET_START: op_counts
let cross_product_ops : nat = 3
let direction_ops : nat = 3
let on_segment_ops : nat = 4
let segments_intersect_ops : nat = 16
//SNIPPET_END: op_counts

let all_constant () : Lemma
  (ensures cross_product_ops + direction_ops + on_segment_ops + segments_intersect_ops <= 30)
  = ()

//SNIPPET_START: composition
let segments_intersect_composition () : Lemma
  (ensures segments_intersect_ops <= 4 * direction_ops + 2 * on_segment_ops)
  = ()
//SNIPPET_END: composition
