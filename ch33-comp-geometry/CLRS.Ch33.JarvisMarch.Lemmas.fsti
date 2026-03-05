(*
   Jarvis's March (Gift Wrapping) — CLRS Chapter 33, Section 33.3
   
   Lemma signatures for Jarvis march correctness properties.
*)

module CLRS.Ch33.JarvisMarch.Lemmas
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.JarvisMarch.Spec
open FStar.Mul

module Seq = FStar.Seq

// ========== Bounds Lemmas ==========

val find_leftmost_aux_bounded (xs ys: Seq.seq int) (i best: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0 /\ best < Seq.length xs)
          (ensures find_leftmost_aux xs ys i best < Seq.length xs)

val find_leftmost_spec_bounded (xs ys: Seq.seq int)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0)
          (ensures find_leftmost_spec xs ys < Seq.length xs)

val find_next_aux_bounded (xs ys: Seq.seq int) (current next: nat) (j: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ current < Seq.length xs /\ next < Seq.length xs)
          (ensures find_next_aux xs ys current next j < Seq.length xs)

val find_next_spec_bounded (xs ys: Seq.seq int) (current: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 1 /\ current < Seq.length xs)
          (ensures find_next_spec xs ys current < Seq.length xs)

// find_next never returns current when n > 1
val find_next_aux_not_current (xs ys: Seq.seq int) (current next: nat) (j: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 1 /\
                    current < Seq.length xs /\ next < Seq.length xs /\
                    (next <> current \/ (exists (k: nat). k >= j /\ k < Seq.length xs /\ k <> current)))
          (ensures find_next_aux xs ys current next j <> current)

val find_next_spec_not_current (xs ys: Seq.seq int) (current: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 1 /\
                    current < Seq.length xs)
          (ensures find_next_spec xs ys current <> current)

// ========== Loop and March Bounds ==========

val jarvis_loop_count_bounded (xs ys: Seq.seq int) (start current: nat) (fuel: nat)
  : Lemma (ensures jarvis_loop_count xs ys start current fuel <= fuel)

val jarvis_march_spec_bounded (xs ys: Seq.seq int)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 1)
          (ensures jarvis_march_spec xs ys <= Seq.length xs /\
                   jarvis_march_spec xs ys >= 1)

// Step lemma: unfolding one iteration when next ≠ start
val jarvis_loop_step (xs ys: Seq.seq int) (start current: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\ find_next_spec xs ys current <> start)
          (ensures jarvis_loop_count xs ys start current fuel ==
                   1 + jarvis_loop_count xs ys start
                       (find_next_spec xs ys current) (fuel - 1) /\
                   jarvis_loop_count xs ys start current fuel >= 1)

// ========== Correctness Lemmas ==========

// find_leftmost returns the lexicographic minimum (x, then y).
val find_leftmost_aux_is_min (xs ys: Seq.seq int) (i best: nat)
  : Lemma (requires
      Seq.length ys == Seq.length xs /\ Seq.length xs > 0 /\
      best < Seq.length xs /\
      (forall (k: nat). k < i /\ k < Seq.length xs ==>
        Seq.index xs best < Seq.index xs k \/
        (Seq.index xs best = Seq.index xs k /\ Seq.index ys best <= Seq.index ys k)))
    (ensures is_leftmost xs ys (find_leftmost_aux xs ys i best))

val find_leftmost_is_leftmost (xs ys: Seq.seq int)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0)
          (ensures is_leftmost xs ys (find_leftmost_spec xs ys))

// Cross-product antisymmetry (swapping last two points negates the value).
val cross_prod_swap23 (x1 y1 x2 y2 x3 y3: int) : Lemma
  (ensures cross_prod x1 y1 x3 y3 x2 y2 == -(cross_prod x1 y1 x2 y2 x3 y3))

// Half-plane transitivity
val half_plane_transitivity (ax ay bx b_y cx cy: int) : Lemma
  (requires ay >= 0 /\ b_y > 0 /\ cy >= 0 /\
            ax * b_y - bx * ay >= 0 /\
            bx * cy - cx * b_y >= 0)
  (ensures ax * cy - cx * ay >= 0)

// Cross-product transitivity in the upper half-plane
val cross_prod_transitivity (cx c_y nx ny jx jy kx ky: int) : Lemma
  (requires
    ny - c_y > 0 /\ jy - c_y >= 0 /\ ky - c_y >= 0 /\
    cross_prod cx c_y nx ny jx jy < 0 /\
    cross_prod cx c_y nx ny kx ky >= 0)
  (ensures cross_prod cx c_y jx jy kx ky >= 0)
  [SMTPat (cross_prod cx c_y jx jy kx ky); SMTPat (cross_prod cx c_y nx ny kx ky)]

// Degenerate transitivity
val cross_prod_transitivity_degenerate (cx c_y nx ny jx jy: int) : Lemma
  (requires
    ny = c_y /\ jy - c_y >= 0 /\
    cross_prod cx c_y nx ny jx jy < 0)
  (ensures cross_prod cx c_y jx jy nx ny > 0)

// find_next_aux maintains the "beats all predecessors" invariant.
val find_next_aux_beats_all (xs ys: Seq.seq int) (current next: nat) (j: nat)
  : Lemma
    (requires
      Seq.length ys == Seq.length xs /\ Seq.length xs > 1 /\
      current < Seq.length xs /\ next < Seq.length xs /\
      (forall (k: nat). k < Seq.length xs /\ k <> current ==>
        Seq.index ys k > Seq.index ys current) /\
      (forall (a b: nat). a < Seq.length xs /\ b < Seq.length xs /\
        a <> current /\ b <> current /\ a <> b ==>
        cross_prod (Seq.index xs current) (Seq.index ys current)
                   (Seq.index xs a) (Seq.index ys a)
                   (Seq.index xs b) (Seq.index ys b) <> 0) /\
      (next = current ==>
        (forall (k: nat). k < j /\ k < Seq.length xs ==> k = current)) /\
      (next <> current ==>
        (forall (k: nat). k < j /\ k < Seq.length xs /\ k <> current ==>
          cross_prod (Seq.index xs current) (Seq.index ys current)
                     (Seq.index xs next) (Seq.index ys next)
                     (Seq.index xs k) (Seq.index ys k) >= 0)))
    (ensures (
      let r = find_next_aux xs ys current next j in
      r < Seq.length xs /\
      (r <> current ==>
        (forall (k: nat). k < Seq.length xs /\ k <> current ==>
          cross_prod (Seq.index xs current) (Seq.index ys current)
                     (Seq.index xs r) (Seq.index ys r)
                     (Seq.index xs k) (Seq.index ys k) >= 0))))

// The "all left of" property for find_next — core correctness theorem.
val find_next_all_left_of (xs ys: Seq.seq int) (current: nat)
  : Lemma
    (requires
      Seq.length ys == Seq.length xs /\ Seq.length xs > 1 /\
      current < Seq.length xs /\
      (forall (k: nat). k < Seq.length xs /\ k <> current ==>
        Seq.index ys k > Seq.index ys current) /\
      (forall (a b: nat). a < Seq.length xs /\ b < Seq.length xs /\
        a <> current /\ b <> current /\ a <> b ==>
        cross_prod (Seq.index xs current) (Seq.index ys current)
                   (Seq.index xs a) (Seq.index ys a)
                   (Seq.index xs b) (Seq.index ys b) <> 0))
    (ensures all_left_of xs ys current (find_next_spec xs ys current))
