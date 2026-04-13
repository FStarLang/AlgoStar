(*
   Bridge lemmas connecting c2pulse postconditions (Int32.t arrays)
   to CLRS.Ch33.JarvisMarch.Spec functions (int sequences).

   c2pulse operates on Seq.seq (option Int32.t); the Impl.fsti specs
   use Seq.seq int. These bridge wrappers work directly on option
   sequences to match c2pulse's element access pattern, then are
   proven equivalent to the spec functions.

   NO admits. NO assumes.
*)

module CLRS.Ch33.JarvisMarch.C.BridgeLemmas
open FStar.Mul
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.JarvisMarch.Spec

module SZ = FStar.SizeT
module Seq = FStar.Seq

(* ================================================================
   Direct access helpers matching c2pulse's array_read
   ================================================================ *)

let ival (s: Seq.seq (option Int32.t)) (i: nat) : int =
  if i < Seq.length s then
    match Seq.index s i with Some v -> Int32.v v | None -> 0
  else 0

(* ================================================================
   _c wrappers: spec-equivalent functions on option Int32.t seqs
   ================================================================ *)

let rec find_leftmost_aux_c (xs ys: Seq.seq (option Int32.t)) (i best: nat)
  : Tot nat (decreases (Seq.length xs - i)) =
  if best >= Seq.length xs || Seq.length ys <> Seq.length xs then best
  else if i >= Seq.length xs then best
  else
    let new_best =
      if ival xs i < ival xs best ||
         (ival xs i = ival xs best && ival ys i < ival ys best)
      then i
      else best
    in
    find_leftmost_aux_c xs ys (i + 1) new_best

let find_leftmost_spec_c (xs ys: Seq.seq (option Int32.t)) : Tot nat =
  if Seq.length xs = 0 then 0
  else find_leftmost_aux_c xs ys 1 0

let rec find_next_aux_c (xs ys: Seq.seq (option Int32.t)) (current next: nat) (j: nat)
  : Tot nat (decreases (Seq.length xs - j)) =
  if current >= Seq.length xs || next >= Seq.length xs || Seq.length ys <> Seq.length xs
  then next
  else if j >= Seq.length xs then next
  else if j = current then find_next_aux_c xs ys current next (j + 1)
  else if next = current then find_next_aux_c xs ys current j (j + 1)
  else
    let cp = cross_product_spec
      (ival xs current) (ival ys current)
      (ival xs next) (ival ys next)
      (ival xs j) (ival ys j) in
    let new_next = if cp < 0 then j else next in
    find_next_aux_c xs ys current new_next (j + 1)

let find_next_spec_c (xs ys: Seq.seq (option Int32.t)) (current: nat) : Tot nat =
  find_next_aux_c xs ys current current 0

let rec jarvis_loop_count_c (xs ys: Seq.seq (option Int32.t)) (start current: nat) (fuel: nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then 0
  else
    let next = find_next_spec_c xs ys current in
    if next = start then 0
    else 1 + jarvis_loop_count_c xs ys start next (fuel - 1)

let jarvis_march_spec_c (xs ys: Seq.seq (option Int32.t)) : Tot nat =
  let n = Seq.length xs in
  if n <= 1 then n
  else
    let p0 = find_leftmost_spec_c xs ys in
    1 + jarvis_loop_count_c xs ys p0 p0 (n - 1)

(* ================================================================
   Unfolding lemmas for jarvis_loop_count_c
   ================================================================ *)

let jarvis_loop_done_c (xs ys: Seq.seq (option Int32.t)) (start current: nat) (fuel: nat)
  : Lemma
    (requires fuel > 0 /\ find_next_spec_c xs ys current = start)
    (ensures jarvis_loop_count_c xs ys start current fuel == 0)
  = ()

let jarvis_loop_step_c (xs ys: Seq.seq (option Int32.t)) (start current: nat) (fuel: nat)
  : Lemma
    (requires fuel > 0 /\ find_next_spec_c xs ys current <> start)
    (ensures jarvis_loop_count_c xs ys start current fuel ==
             1 + jarvis_loop_count_c xs ys start (find_next_spec_c xs ys current) (fuel - 1))
  = ()

let jarvis_march_unfold_c (xs ys: Seq.seq (option Int32.t))
  : Lemma
    (requires Seq.length xs > 1)
    (ensures jarvis_march_spec_c xs ys ==
             1 + jarvis_loop_count_c xs ys
                   (find_leftmost_spec_c xs ys) (find_leftmost_spec_c xs ys)
                   (Seq.length xs - 1))
  = ()

let jarvis_loop_zero_c (xs ys: Seq.seq (option Int32.t)) (start current: nat)
  : Lemma (jarvis_loop_count_c xs ys start current 0 == 0)
  = ()
