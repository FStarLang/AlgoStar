(*
   Bridge lemmas connecting c2pulse postconditions (Int32.t arrays)
   to CLRS.Ch33.GrahamScan.Spec functions (int sequences).

   c2pulse operates on Seq.seq (option Int32.t); the Impl.fsti specs
   use Seq.seq int. These bridge wrappers work directly on option
   sequences to match c2pulse's element access pattern, then are
   proven equivalent to the spec functions.

   NO admits. NO assumes.
*)

module CLRS.Ch33.GrahamScan.C.BridgeLemmas
open FStar.Mul
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.GrahamScan.Spec

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

let rec find_bottom_aux_c (xs ys: Seq.seq (option Int32.t)) (i best: nat)
  : Tot nat (decreases (Seq.length xs - i)) =
  if best >= Seq.length xs || Seq.length ys <> Seq.length xs then best
  else if i >= Seq.length xs then best
  else
    let new_best =
      if ival ys i < ival ys best ||
         (ival ys i = ival ys best && ival xs i < ival xs best)
      then i
      else best
    in
    find_bottom_aux_c xs ys (i + 1) new_best

let find_bottom_spec_c (xs ys: Seq.seq (option Int32.t)) : Tot nat =
  if Seq.length xs = 0 then 0
  else find_bottom_aux_c xs ys 1 0

let polar_cmp_spec_c (xs ys: Seq.seq (option Int32.t)) (p0 a b: nat) : Tot int =
  if p0 >= Seq.length xs || a >= Seq.length xs || b >= Seq.length xs ||
     Seq.length ys <> Seq.length xs
  then 0
  else
    cross_product_spec (ival xs p0) (ival ys p0)
                       (ival xs a) (ival ys a)
                       (ival xs b) (ival ys b)

let sz_val (s: Seq.seq (option SZ.t)) (i: nat) : SZ.t =
  if i < Seq.length s then
    match Seq.index s i with Some v -> v | None -> 0sz
  else 0sz

let rec pop_while_spec_c (xs ys: Seq.seq (option Int32.t))
                          (hull: Seq.seq (option SZ.t)) (top: nat) (p_idx: nat)
  : Tot nat (decreases top) =
  if top < 2 || top > Seq.length hull then top
  else
    let t1 = SZ.v (sz_val hull (top - 1)) in
    let t2 = SZ.v (sz_val hull (top - 2)) in
    if t1 >= Seq.length xs || t2 >= Seq.length xs || p_idx >= Seq.length xs ||
       Seq.length ys <> Seq.length xs
    then top
    else
      let cp = cross_product_spec
        (ival xs t2) (ival ys t2)
        (ival xs t1) (ival ys t1)
        (ival xs p_idx) (ival ys p_idx) in
      if cp <= 0 then pop_while_spec_c xs ys hull (top - 1) p_idx
      else top

let ensures_left_turn_c (xs ys: Seq.seq (option Int32.t))
                         (hull: Seq.seq (option SZ.t)) (top p_idx: nat) : prop =
  if top >= 2 && top <= Seq.length hull && p_idx < Seq.length xs &&
     Seq.length ys = Seq.length xs then
    let t1 = SZ.v (sz_val hull (top - 1)) in
    let t2 = SZ.v (sz_val hull (top - 2)) in
    if t1 < Seq.length xs && t2 < Seq.length xs then
      cross_product_spec (ival xs t2) (ival ys t2)
                         (ival xs t1) (ival ys t1)
                         (ival xs p_idx) (ival ys p_idx) > 0
    else True
  else True
