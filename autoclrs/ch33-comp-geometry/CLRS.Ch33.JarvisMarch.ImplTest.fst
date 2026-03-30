(*
   Spec Validation Tests — CLRS Chapter 33, Section 33.3: Jarvis March

   Tests that the Impl.fsti postconditions are:
   1. Satisfiable — each function's precondition can be met with concrete arrays.
   2. Precise — the postcondition uniquely determines the output.
   3. Semantically strong — postconditions expose key properties:
      - find_leftmost: is_leftmost (the result truly is the leftmost point)
      - find_next: result <> current (always advances to a different point)
      - jarvis_march_with_hull: valid_jarvis_hull (hull indices match spec)

   Test instance: triangle (0,0), (2,0), (1,2) — all 3 points on the convex hull.
   - find_leftmost returns 0 (minimum x-coordinate)
   - find_next from 0 returns 1 (most clockwise from (0,0) is (2,0))
   - find_next from 1 returns 2, from 2 returns 0 (full cycle)
   - jarvis_march returns 3 (all 3 points are hull vertices)
   - jarvis_march_with_hull returns 3 and populates hull with [0, 1, 2]

   Each test returns a bool (true = pass) that is checked at the C level.

   Zero admits. Zero assumes. All assertions proven by SMT.
*)

module CLRS.Ch33.JarvisMarch.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.JarvisMarch.Spec
open CLRS.Ch33.JarvisMarch.Impl
open FStar.Mul

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

(* ========== Helper lemmas for concrete spec evaluation ========== *)

(* Shared precondition for the triangle test case *)
[@@"noextract"]
unfold
let triangle_pre (sxs sys: Seq.seq int) : prop =
  Seq.length sxs == 3 /\ Seq.length sys == 3 /\
  Seq.index sxs 0 == 0 /\ Seq.index sxs 1 == 2 /\ Seq.index sxs 2 == 1 /\
  Seq.index sys 0 == 0 /\ Seq.index sys 1 == 0 /\ Seq.index sys 2 == 2

(* find_leftmost_spec returns 0: point (0,0) has minimum x. *)
#push-options "--fuel 4 --ifuel 1"
let find_leftmost_triangle_lemma (sxs sys: Seq.seq int)
  : Lemma (requires triangle_pre sxs sys)
          (ensures find_leftmost_spec sxs sys == 0)
= ()
#pop-options

(* find_next_spec from vertex 0 returns 1.
   From (0,0), the most clockwise point is (2,0).
   cross_prod(0,0, 1,0, 2,1) for candidate comparison. *)
#push-options "--fuel 8 --ifuel 1"
let find_next_from_0_lemma (sxs sys: Seq.seq int)
  : Lemma (requires triangle_pre sxs sys)
          (ensures find_next_spec sxs sys 0 == 1)
= ()

(* find_next_spec from vertex 1 returns 2. *)
let find_next_from_1_lemma (sxs sys: Seq.seq int)
  : Lemma (requires triangle_pre sxs sys)
          (ensures find_next_spec sxs sys 1 == 2)
= ()

(* find_next_spec from vertex 2 returns 0. *)
let find_next_from_2_lemma (sxs sys: Seq.seq int)
  : Lemma (requires triangle_pre sxs sys)
          (ensures find_next_spec sxs sys 2 == 0)
= ()
#pop-options

(* jarvis_march_spec returns 3: all three triangle vertices are on the hull.
   p0=0 (leftmost), then 0→1→2→0 (back to start), so hull has 3 vertices. *)
#push-options "--fuel 8 --ifuel 1 --z3rlimit 10"
let jarvis_march_triangle_lemma (sxs sys: Seq.seq int)
  : Lemma (requires triangle_pre sxs sys)
          (ensures jarvis_march_spec sxs sys == 3)
= find_leftmost_triangle_lemma sxs sys;
  find_next_from_0_lemma sxs sys;
  find_next_from_1_lemma sxs sys;
  find_next_from_2_lemma sxs sys
#pop-options

(* ========== Test: find_leftmost ========== *)

```pulse
fn test_find_leftmost ()
  requires emp
  returns result: bool
  ensures emp ** pure (result == true)
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

  let r = find_leftmost xs ys 3sz;

  // Postcondition: SZ.v result == find_leftmost_spec sxs sys
  find_leftmost_triangle_lemma sxs sys;
  assert (pure (SZ.v r == 0));

  // Strengthened postcondition: result is truly the leftmost point
  assert (pure (is_leftmost sxs sys (SZ.v r)));

  let ok = (r = 0sz);

  // Cleanup
  with sx. assert (A.pts_to xs sx);
  rewrite (A.pts_to xs sx) as (A.pts_to (V.vec_to_array vx) sx);
  V.to_vec_pts_to vx;
  V.free vx;

  with sy. assert (A.pts_to ys sy);
  rewrite (A.pts_to ys sy) as (A.pts_to (V.vec_to_array vy) sy);
  V.to_vec_pts_to vy;
  V.free vy;
  ok
}
```

(* ========== Test: find_next ========== *)

```pulse
fn test_find_next ()
  requires emp
  returns result: bool
  ensures emp ** pure (result == true)
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

  // find_next from vertex 0: the most clockwise point from (0,0) is (2,0) = index 1
  let r0 = find_next xs ys 3sz 0sz;
  find_next_from_0_lemma sxs sys;
  assert (pure (SZ.v r0 == 1));
  // Strengthened postcondition: result always advances
  assert (pure (SZ.v r0 <> 0));

  // find_next from vertex 1: the most clockwise from (2,0) is (1,2) = index 2
  let r1 = find_next xs ys 3sz 1sz;
  find_next_from_1_lemma sxs sys;
  assert (pure (SZ.v r1 == 2));
  assert (pure (SZ.v r1 <> 1));

  // find_next from vertex 2: the most clockwise from (1,2) is (0,0) = index 0
  let r2 = find_next xs ys 3sz 2sz;
  find_next_from_2_lemma sxs sys;
  assert (pure (SZ.v r2 == 0));
  assert (pure (SZ.v r2 <> 2));

  // Full cycle: 0 → 1 → 2 → 0 (all three hull edges tested)

  let ok = (r0 = 1sz && r1 = 2sz && r2 = 0sz);

  // Cleanup
  with sx. assert (A.pts_to xs sx);
  rewrite (A.pts_to xs sx) as (A.pts_to (V.vec_to_array vx) sx);
  V.to_vec_pts_to vx;
  V.free vx;

  with sy. assert (A.pts_to ys sy);
  rewrite (A.pts_to ys sy) as (A.pts_to (V.vec_to_array vy) sy);
  V.to_vec_pts_to vy;
  V.free vy;
  ok
}
```

(* ========== Test: jarvis_march ========== *)

```pulse
fn test_jarvis_march ()
  requires emp
  returns result: bool
  ensures emp ** pure (result == true)
{
  // Points: (0,0), (2,0), (1,2) — all on the convex hull
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

  let h = jarvis_march xs ys 3sz;

  // Postcondition: SZ.v h == jarvis_march_spec sxs sys /\ SZ.v h >= 1 /\ SZ.v h <= 3
  jarvis_march_triangle_lemma sxs sys;
  assert (pure (SZ.v h == 3));

  // Precision: all 3 points are on the hull (h == n for a convex polygon)
  assert (pure (SZ.v h >= 1));
  assert (pure (SZ.v h <= 3));

  let ok = (h = 3sz);

  // Cleanup
  with sx. assert (A.pts_to xs sx);
  rewrite (A.pts_to xs sx) as (A.pts_to (V.vec_to_array vx) sx);
  V.to_vec_pts_to vx;
  V.free vx;

  with sy. assert (A.pts_to ys sy);
  rewrite (A.pts_to ys sy) as (A.pts_to (V.vec_to_array vy) sy);
  V.to_vec_pts_to vy;
  V.free vy;
  ok
}
```

(* ========== Test: jarvis_march_with_hull ========== *)

```pulse
fn test_jarvis_march_with_hull ()
  requires emp
  returns result: bool
  ensures emp ** pure (result == true)
{
  // Points: (0,0), (2,0), (1,2) — all on the convex hull
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

  // Allocate hull output array
  let vhull = V.alloc 0sz 3sz;
  V.to_array_pts_to vhull;
  let hull = V.vec_to_array vhull;
  rewrite (A.pts_to (V.vec_to_array vhull) (Seq.create 3 0sz))
       as (A.pts_to hull (Seq.create 3 0sz));

  with sxs. assert (A.pts_to xs sxs);
  with sys. assert (A.pts_to ys sys);

  let h = jarvis_march_with_hull xs ys 3sz hull;

  // Postcondition: h == 3, valid hull
  jarvis_march_triangle_lemma sxs sys;
  assert (pure (SZ.v h == 3));

  // Verify hull validity
  with shull'. assert (A.pts_to hull shull');
  assert (pure (valid_jarvis_hull sxs sys shull' (SZ.v h)));

  // Read hull to check at C level: hull should be [0, 1, 2]
  let h0 = hull.(0sz);
  let h1 = hull.(1sz);
  let h2 = hull.(2sz);

  find_leftmost_triangle_lemma sxs sys;
  find_next_from_0_lemma sxs sys;
  find_next_from_1_lemma sxs sys;
  assert (pure (SZ.v h0 == 0));
  assert (pure (SZ.v h1 == 1));
  assert (pure (SZ.v h2 == 2));

  let ok = (h = 3sz && h0 = 0sz && h1 = 1sz && h2 = 2sz);

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
  rewrite (A.pts_to hull sh) as (A.pts_to (V.vec_to_array vhull) sh);
  V.to_vec_pts_to vhull;
  V.free vhull;
  ok
}
```
