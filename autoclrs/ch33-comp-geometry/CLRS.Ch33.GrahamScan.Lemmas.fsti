(*
   Graham Scan — CLRS Chapter 33, Section 33.3
   
   Lemma signatures for Graham scan correctness properties.
*)

module CLRS.Ch33.GrahamScan.Lemmas
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.GrahamScan.Spec
open FStar.Mul

module SZ = FStar.SizeT
module Seq = FStar.Seq

// Bounds lemma for find_bottom_aux
val find_bottom_aux_bounded (xs ys: Seq.seq int) (i best: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0 /\ best < Seq.length xs)
          (ensures find_bottom_aux xs ys i best < Seq.length xs)

val find_bottom_spec_bounded (xs ys: Seq.seq int)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0)
          (ensures find_bottom_spec xs ys < Seq.length xs)

// Bounds lemma for pop_while_spec
val pop_while_spec_bounded (xs ys: Seq.seq int) (hull: Seq.seq SZ.t) (top: nat) (p_idx: nat)
  : Lemma (ensures pop_while_spec xs ys hull top p_idx <= top)

// find_bottom returns the bottom-most point
val find_bottom_aux_is_min (xs ys: Seq.seq int) (i best: nat)
  : Lemma (requires
      Seq.length ys == Seq.length xs /\ Seq.length xs > 0 /\
      best < Seq.length xs /\
      (forall (k: nat). k < i /\ k < Seq.length xs ==>
        Seq.index ys best < Seq.index ys k \/
        (Seq.index ys best = Seq.index ys k /\ Seq.index xs best <= Seq.index xs k)))
    (ensures is_bottommost xs ys (find_bottom_aux xs ys i best))

val find_bottom_is_bottommost (xs ys: Seq.seq int)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0)
          (ensures is_bottommost xs ys (find_bottom_spec xs ys))

//SNIPPET_START: pop_while_left_turn
// When pop_while_spec stops, the top of the remaining stack with the new
// point p makes a left turn (cross product > 0), or the stack is too small.
val pop_while_ensures_left_turn
  (xs ys: Seq.seq int) (hull: Seq.seq SZ.t) (top: nat) (p_idx: nat)
  : Lemma
    (requires
      Seq.length ys == Seq.length xs /\
      top >= 2 /\ top <= Seq.length hull /\
      p_idx < Seq.length xs /\
      (forall (i: nat). i < top ==> SZ.v (Seq.index hull i) < Seq.length xs))
    (ensures (
      let top' = pop_while_spec xs ys hull top p_idx in
      top' <= top /\
      (top' >= 2 ==>
        (let t1 = SZ.v (Seq.index hull (top' - 1)) in
         let t2 = SZ.v (Seq.index hull (top' - 2)) in
         cross_prod (Seq.index xs t2) (Seq.index ys t2)
                    (Seq.index xs t1) (Seq.index ys t1)
                    (Seq.index xs p_idx) (Seq.index ys p_idx) > 0))))
//SNIPPET_END: pop_while_left_turn
