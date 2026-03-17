(*
   Spec Validation Tests — CLRS Chapter 33, Section 33.3: Graham Scan

   Tests that the Impl.fsti postconditions are:
   1. Satisfiable — each function's precondition can be met with concrete arrays.
   2. Precise — the postcondition uniquely determines the output.
   3. Semantically strong — postconditions expose key properties:
      - find_bottom: is_bottommost (the result truly is the bottom-most point)
      - pop_while: result >= 1 (stack is never emptied) and
        ensures_left_turn (when result >= 2, a left turn is guaranteed)

   Test instances:
   - find_bottom, polar_cmp: triangle (0,0), (2,0), (1,2)
   - pop_while: 4-point set (0,0), (2,0), (1,1), (0,2) with hull [0,1,2]

   Zero admits. Zero assumes. All assertions proven by SMT.
*)

module CLRS.Ch33.GrahamScan.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.GrahamScan.Spec
open CLRS.Ch33.GrahamScan.Impl
open FStar.Mul

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

(* ========== Helper lemmas for concrete spec evaluation ========== *)

(* find_bottom_spec on triangle (0,0), (2,0), (1,2) returns 0.
   Point 0 has minimum y=0 (tied with point 1), minimum x=0 (tiebreak). *)
#push-options "--fuel 4 --ifuel 1"
let find_bottom_triangle_lemma (sxs sys: Seq.seq int)
  : Lemma
    (requires Seq.length sxs == 3 /\ Seq.length sys == 3 /\
              Seq.index sxs 0 == 0 /\ Seq.index sxs 1 == 2 /\ Seq.index sxs 2 == 1 /\
              Seq.index sys 0 == 0 /\ Seq.index sys 1 == 0 /\ Seq.index sys 2 == 2)
    (ensures find_bottom_spec sxs sys == 0)
= ()
#pop-options

(* polar_cmp_spec with pivot=0, a=1, b=2 returns 4.
   cross_prod(0,0, 2,0, 1,2) = (2-0)*(2-0) - (1-0)*(0-0) = 4.
   Positive means point 1 comes before point 2 in CCW polar order. *)
let polar_cmp_triangle_lemma (sxs sys: Seq.seq int)
  : Lemma
    (requires Seq.length sxs == 3 /\ Seq.length sys == 3 /\
              Seq.index sxs 0 == 0 /\ Seq.index sxs 1 == 2 /\ Seq.index sxs 2 == 1 /\
              Seq.index sys 0 == 0 /\ Seq.index sys 1 == 0 /\ Seq.index sys 2 == 2)
    (ensures polar_cmp_spec sxs sys 0 1 2 == 4)
= ()

(* pop_while_spec on 4-point set with hull [0,1,2], top=3, new point=3.
   Point 2 (1,1) causes a non-left-turn with new point 3 (0,2), so it's popped.
   cross_prod(2,0, 1,1, 0,2) = 0 ≤ 0 → pop. Then cross_prod(0,0, 2,0, 0,2) = 4 > 0 → stop.
   Result: top=2. *)
#push-options "--fuel 4 --ifuel 1"
let pop_while_concrete_lemma (sxs sys: Seq.seq int) (shull: Seq.seq SZ.t)
  : Lemma
    (requires Seq.length sxs == 4 /\ Seq.length sys == 4 /\ Seq.length shull == 4 /\
              Seq.index sxs 0 == 0 /\ Seq.index sxs 1 == 2 /\
              Seq.index sxs 2 == 1 /\ Seq.index sxs 3 == 0 /\
              Seq.index sys 0 == 0 /\ Seq.index sys 1 == 0 /\
              Seq.index sys 2 == 1 /\ Seq.index sys 3 == 2 /\
              Seq.index shull 0 == 0sz /\ Seq.index shull 1 == 1sz /\
              Seq.index shull 2 == 2sz /\ Seq.index shull 3 == 0sz)
    (ensures pop_while_spec sxs sys shull 3 3 == 2)
= ()
#pop-options

(* ========== Test: find_bottom ========== *)

```pulse
fn test_find_bottom ()
  requires emp
  returns _: unit
  ensures emp
{
  // Points: (0,0), (2,0), (1,2)
  let vx = V.alloc 0 3sz;
  V.to_array_pts_to vx;
  let xs = V.vec_to_array vx;
  rewrite (A.pts_to (V.vec_to_array vx) (Seq.create 3 0))
       as (A.pts_to xs (Seq.create 3 0));
  xs.(0sz) <- 0;
  xs.(1sz) <- 2;
  xs.(2sz) <- 1;

  let vy = V.alloc 0 3sz;
  V.to_array_pts_to vy;
  let ys = V.vec_to_array vy;
  rewrite (A.pts_to (V.vec_to_array vy) (Seq.create 3 0))
       as (A.pts_to ys (Seq.create 3 0));
  ys.(0sz) <- 0;
  ys.(1sz) <- 0;
  ys.(2sz) <- 2;

  with sxs. assert (A.pts_to xs sxs);
  with sys. assert (A.pts_to ys sys);

  let result = find_bottom xs ys 3sz;

  // Postcondition: SZ.v result == find_bottom_spec sxs sys
  // Helper lemma evaluates the spec to 0
  find_bottom_triangle_lemma sxs sys;
  assert (pure (SZ.v result == 0));

  // Strengthened postcondition: result is truly the bottom-most point
  assert (pure (is_bottommost sxs sys (SZ.v result)));

  // Cleanup
  with sx. assert (A.pts_to xs sx);
  rewrite (A.pts_to xs sx) as (A.pts_to (V.vec_to_array vx) sx);
  V.to_vec_pts_to vx;
  V.free vx;

  with sy. assert (A.pts_to ys sy);
  rewrite (A.pts_to ys sy) as (A.pts_to (V.vec_to_array vy) sy);
  V.to_vec_pts_to vy;
  V.free vy;
  ()
}
```

(* ========== Test: polar_cmp ========== *)

```pulse
fn test_polar_cmp ()
  requires emp
  returns _: unit
  ensures emp
{
  // Points: (0,0), (2,0), (1,2)
  let vx = V.alloc 0 3sz;
  V.to_array_pts_to vx;
  let xs = V.vec_to_array vx;
  rewrite (A.pts_to (V.vec_to_array vx) (Seq.create 3 0))
       as (A.pts_to xs (Seq.create 3 0));
  xs.(0sz) <- 0;
  xs.(1sz) <- 2;
  xs.(2sz) <- 1;

  let vy = V.alloc 0 3sz;
  V.to_array_pts_to vy;
  let ys = V.vec_to_array vy;
  rewrite (A.pts_to (V.vec_to_array vy) (Seq.create 3 0))
       as (A.pts_to ys (Seq.create 3 0));
  ys.(0sz) <- 0;
  ys.(1sz) <- 0;
  ys.(2sz) <- 2;

  with sxs. assert (A.pts_to xs sxs);
  with sys. assert (A.pts_to ys sys);

  // Compare polar angles: pivot=0, a=1, b=2
  let result = polar_cmp xs ys 3sz 0sz 1sz 2sz;

  // Postcondition: result == polar_cmp_spec sxs sys 0 1 2
  polar_cmp_triangle_lemma sxs sys;
  assert (pure (result == 4));

  // Precision: positive result means point 1 comes before point 2 in CCW order
  assert (pure (result > 0));

  // Cleanup
  with sx. assert (A.pts_to xs sx);
  rewrite (A.pts_to xs sx) as (A.pts_to (V.vec_to_array vx) sx);
  V.to_vec_pts_to vx;
  V.free vx;

  with sy. assert (A.pts_to ys sy);
  rewrite (A.pts_to ys sy) as (A.pts_to (V.vec_to_array vy) sy);
  V.to_vec_pts_to vy;
  V.free vy;
  ()
}
```

(* ========== Test: pop_while ========== *)

```pulse
fn test_pop_while ()
  requires emp
  returns _: unit
  ensures emp
{
  // Points: (0,0), (2,0), (1,1), (0,2)
  let vx = V.alloc 0 4sz;
  V.to_array_pts_to vx;
  let xs = V.vec_to_array vx;
  rewrite (A.pts_to (V.vec_to_array vx) (Seq.create 4 0))
       as (A.pts_to xs (Seq.create 4 0));
  xs.(0sz) <- 0;
  xs.(1sz) <- 2;
  xs.(2sz) <- 1;
  xs.(3sz) <- 0;

  let vy = V.alloc 0 4sz;
  V.to_array_pts_to vy;
  let ys = V.vec_to_array vy;
  rewrite (A.pts_to (V.vec_to_array vy) (Seq.create 4 0))
       as (A.pts_to ys (Seq.create 4 0));
  ys.(0sz) <- 0;
  ys.(1sz) <- 0;
  ys.(2sz) <- 1;
  ys.(3sz) <- 2;

  // Hull stack: [0, 1, 2, _] with top=3
  let vh = V.alloc 0sz 4sz;
  V.to_array_pts_to vh;
  let hull = V.vec_to_array vh;
  rewrite (A.pts_to (V.vec_to_array vh) (Seq.create 4 0sz))
       as (A.pts_to hull (Seq.create 4 0sz));
  hull.(0sz) <- 0sz;
  hull.(1sz) <- 1sz;
  hull.(2sz) <- 2sz;

  with sxs. assert (A.pts_to xs sxs);
  with sys. assert (A.pts_to ys sys);
  with shull. assert (A.pts_to hull shull);

  // Call pop_while: top=3, new point=3
  let result = pop_while xs ys hull 3sz 3sz 4sz;

  // Postcondition: SZ.v result == pop_while_spec sxs sys shull 3 3
  pop_while_concrete_lemma sxs sys shull;
  assert (pure (SZ.v result == 2));

  // Strengthened postcondition: stack is never emptied
  assert (pure (SZ.v result >= 1));

  // Strengthened postcondition: left-turn guarantee at the new top
  assert (pure (ensures_left_turn sxs sys shull (SZ.v result) 3));

  // Cleanup
  with sx. assert (A.pts_to xs sx);
  rewrite (A.pts_to xs sx) as (A.pts_to (V.vec_to_array vx) sx);
  V.to_vec_pts_to vx;
  V.free vx;

  with sy. assert (A.pts_to ys sy);
  rewrite (A.pts_to ys sy) as (A.pts_to (V.vec_to_array vy) sy);
  V.to_vec_pts_to vy;
  V.free vy;

  with sh. assert (A.pts_to hull sh);
  rewrite (A.pts_to hull sh) as (A.pts_to (V.vec_to_array vh) sh);
  V.to_vec_pts_to vh;
  V.free vh;
  ()
}
```
