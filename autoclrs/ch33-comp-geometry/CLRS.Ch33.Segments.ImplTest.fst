(*
   Spec Validation Tests — CLRS Chapter 33, Section 33.1: Segment Primitives

   Tests that the Impl.fsti postconditions are:
   1. Satisfiable — each function can be called with concrete inputs.
   2. Precise — the postcondition uniquely determines the output for each input.

   Each postcondition has the form `result == spec(args)`, so precision follows
   from the fact that spec(concrete_args) evaluates to a unique value.

   Zero admits. Zero assumes. All assertions proven by SMT.
*)

module CLRS.Ch33.Segments.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch33.Segments.Impl
open CLRS.Ch33.Segments.Spec
open FStar.Mul

(* ========== Test: cross_product ==========

   Postcondition: result == cross_product_spec x1 y1 x2 y2 x3 y3

   Test inputs cover all three orientation cases:
   - CCW (positive cross product)
   - CW  (negative cross product)
   - Collinear (zero cross product)
*)

fn test_cross_product ()
  requires emp
  returns _: unit
  ensures emp
{
  // CCW: p1=(0,0), p2=(1,0), p3=(0,1)
  //   (1-0)*(1-0) - (0-0)*(0-0) = 1
  let r_ccw = cross_product 0 0 1 0 0 1;
  assert (pure (r_ccw == 1));

  // CW: p1=(0,0), p2=(0,1), p3=(1,0)
  //   (0-0)*(0-0) - (1-0)*(1-0) = -1
  let r_cw = cross_product 0 0 0 1 1 0;
  assert (pure (r_cw == (-1)));

  // Collinear: p1=(0,0), p2=(1,1), p3=(2,2)
  //   (1-0)*(2-0) - (2-0)*(1-0) = 0
  let r_col = cross_product 0 0 1 1 2 2;
  assert (pure (r_col == 0));

  // Precision: postcondition uniquely determines each result
  assert (pure (r_ccw <> 0 /\ r_ccw <> (-1)));
  assert (pure (r_cw <> 0 /\ r_cw <> 1));
  ()
}

(* ========== Test: direction ==========

   direction_spec is an alias for cross_product_spec.
   The postcondition is equally precise.
*)

fn test_direction ()
  requires emp
  returns _: unit
  ensures emp
{
  let r = direction 0 0 1 0 0 1;
  assert (pure (r == 1));
  ()
}

(* ========== Test: on_segment ==========

   Postcondition: result == on_segment_spec x1 y1 x2 y2 x y

   Tests cover: interior, exterior, endpoints.
*)

fn test_on_segment ()
  requires emp
  returns _: unit
  ensures emp
{
  // Interior of bounding box
  let r1 = on_segment 0 0 2 2 1 1;
  assert (pure (r1 == true));

  // Exterior of bounding box
  let r2 = on_segment 0 0 2 2 3 3;
  assert (pure (r2 == false));

  // First endpoint
  let r3 = on_segment 0 0 2 2 0 0;
  assert (pure (r3 == true));

  // Second endpoint
  let r4 = on_segment 0 0 2 2 2 2;
  assert (pure (r4 == true));

  // Precision: true/false uniquely determined
  assert (pure (r1 <> false));
  assert (pure (r2 <> true));
  ()
}

(* ========== Test: segments_intersect ==========

   Postcondition: result == segments_intersect_spec x1 y1 x2 y2 x3 y3 x4 y4

   Tests cover: general crossing (straddle), non-crossing (collinear separated).
*)

fn test_segments_intersect ()
  requires emp
  returns _: unit
  ensures emp
{
  // Crossing: (0,0)-(2,2) and (0,2)-(2,0) form an X
  let r1 = segments_intersect 0 0 2 2 0 2 2 0;
  assert (pure (r1 == true));

  // Non-crossing: (0,0)-(1,1) and (2,2)-(3,3) are collinear but separated
  let r2 = segments_intersect 0 0 1 1 2 2 3 3;
  assert (pure (r2 == false));

  // Precision: postcondition rules out the other boolean
  assert (pure (r1 <> false));
  assert (pure (r2 <> true));
  ()
}
