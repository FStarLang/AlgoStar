(*
   Computational Geometry Primitives — CLRS Chapter 33, Section 33.1
   
   Pulse implementations of cross product, direction, on-segment,
   and segment intersection, each proven functionally equivalent
   to the pure specification.
   
   NO admits. NO assumes.
*)

module CLRS.Ch33.Segments.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch33.Segments.Spec

fn cross_product (x1 y1 x2 y2 x3 y3: int)
  requires emp
  returns result: int
  ensures emp ** pure (result == cross_product_spec x1 y1 x2 y2 x3 y3)
{
  let dx21 = x2 - x1;
  let dy31 = y3 - y1;
  let dx31 = x3 - x1;
  let dy21 = y2 - y1;
  let term1 = dx21 * dy31;
  let term2 = dx31 * dy21;
  let result = term1 - term2;
  result
}

fn direction (x1 y1 x2 y2 x3 y3: int)
  requires emp
  returns result: int
  ensures emp ** pure (result == direction_spec x1 y1 x2 y2 x3 y3)
{
  cross_product x1 y1 x2 y2 x3 y3
}

fn on_segment (x1 y1 x2 y2 x y: int)
  requires emp
  returns result: bool
  ensures emp ** pure (result == on_segment_spec x1 y1 x2 y2 x y)
{
  let max_x = (if x1 >= x2 then x1 else x2);
  let min_x = (if x1 <= x2 then x1 else x2);
  let max_y = (if y1 >= y2 then y1 else y2);
  let min_y = (if y1 <= y2 then y1 else y2);
  
  let check_x = (x <= max_x && x >= min_x);
  let check_y = (y <= max_y && y >= min_y);
  
  (check_x && check_y)
}

fn segments_intersect (x1 y1 x2 y2 x3 y3 x4 y4: int)
  requires emp
  returns result: bool
  ensures emp ** pure (result == segments_intersect_spec x1 y1 x2 y2 x3 y3 x4 y4)
{
  let d1 = direction x3 y3 x4 y4 x1 y1;
  let d2 = direction x3 y3 x4 y4 x2 y2;
  let d3 = direction x1 y1 x2 y2 x3 y3;
  let d4 = direction x1 y1 x2 y2 x4 y4;
  
  let general_case = 
    ((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) &&
    ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0));
  
  if general_case {
    true
  } else {
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
