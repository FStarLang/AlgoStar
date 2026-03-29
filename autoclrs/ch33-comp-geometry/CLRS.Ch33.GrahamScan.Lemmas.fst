(*
   Graham Scan — CLRS Chapter 33, Section 33.3
   
   Proofs of Graham scan correctness properties.
   
   NO admits. NO assumes.
*)

module CLRS.Ch33.GrahamScan.Lemmas
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.GrahamScan.Spec
open FStar.Mul

module SZ = FStar.SizeT
module Seq = FStar.Seq

let rec find_bottom_aux_bounded (xs ys: Seq.seq int) (i best: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0 /\ best < Seq.length xs)
          (ensures find_bottom_aux xs ys i best < Seq.length xs)
          (decreases (Seq.length xs - i)) =
  if i >= Seq.length xs then ()
  else
    let new_best =
      if Seq.index ys i < Seq.index ys best ||
         (Seq.index ys i = Seq.index ys best && Seq.index xs i < Seq.index xs best)
      then i
      else best
    in
    find_bottom_aux_bounded xs ys (i + 1) new_best

let find_bottom_spec_bounded (xs ys: Seq.seq int)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0)
          (ensures find_bottom_spec xs ys < Seq.length xs) =
  find_bottom_aux_bounded xs ys 1 0

let rec pop_while_spec_bounded (xs ys: Seq.seq int) (hull: Seq.seq SZ.t) (top: nat) (p_idx: nat)
  : Lemma (ensures pop_while_spec xs ys hull top p_idx <= top)
          (decreases top) =
  if top < 2 || top > Seq.length hull then ()
  else
    let t1 = SZ.v (Seq.index hull (top - 1)) in
    let t2 = SZ.v (Seq.index hull (top - 2)) in
    if t1 >= Seq.length xs || t2 >= Seq.length xs || p_idx >= Seq.length xs ||
       Seq.length ys <> Seq.length xs
    then ()
    else
      let cp = cross_prod
        (Seq.index xs t2) (Seq.index ys t2)
        (Seq.index xs t1) (Seq.index ys t1)
        (Seq.index xs p_idx) (Seq.index ys p_idx) in
      if cp <= 0 then pop_while_spec_bounded xs ys hull (top - 1) p_idx
      else ()

let rec find_bottom_aux_is_min (xs ys: Seq.seq int) (i best: nat)
  : Lemma (requires
      Seq.length ys == Seq.length xs /\ Seq.length xs > 0 /\
      best < Seq.length xs /\
      (forall (k: nat). k < i /\ k < Seq.length xs ==>
        Seq.index ys best < Seq.index ys k \/
        (Seq.index ys best = Seq.index ys k /\ Seq.index xs best <= Seq.index xs k)))
    (ensures is_bottommost xs ys (find_bottom_aux xs ys i best))
    (decreases (Seq.length xs - i)) =
  if i >= Seq.length xs then ()
  else
    let yi = Seq.index ys i in
    let yb = Seq.index ys best in
    let xi = Seq.index xs i in
    let xb = Seq.index xs best in
    let new_best = if yi < yb || (yi = yb && xi < xb) then i else best in
    find_bottom_aux_is_min xs ys (i + 1) new_best

let find_bottom_is_bottommost (xs ys: Seq.seq int)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0)
          (ensures is_bottommost xs ys (find_bottom_spec xs ys)) =
  find_bottom_aux_is_min xs ys 1 0

let rec pop_while_ensures_left_turn
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
    (decreases top) =
  pop_while_spec_bounded xs ys hull top p_idx;
  let t1 = SZ.v (Seq.index hull (top - 1)) in
  let t2 = SZ.v (Seq.index hull (top - 2)) in
  let cp = cross_prod
    (Seq.index xs t2) (Seq.index ys t2)
    (Seq.index xs t1) (Seq.index ys t1)
    (Seq.index xs p_idx) (Seq.index ys p_idx) in
  if cp <= 0 then begin
    if top - 1 >= 2 then
      pop_while_ensures_left_turn xs ys hull (top - 1) p_idx
    else
      pop_while_spec_bounded xs ys hull (top - 1) p_idx
  end else ()

let all_left_turns_sz_prefix (xs ys: Seq.seq int) (hull: Seq.seq SZ.t) (top top': nat)
  : Lemma (requires all_left_turns_sz xs ys hull top /\ top' <= top)
          (ensures all_left_turns_sz xs ys hull top') = ()

let rec pop_while_spec_ge_1 (xs ys: Seq.seq int) (hull: Seq.seq SZ.t) (top: nat) (p_idx: nat)
  : Lemma (requires top >= 2)
          (ensures pop_while_spec xs ys hull top p_idx >= 1)
          (decreases top) =
  if top < 2 || top > Seq.length hull then ()
  else
    let t1 = SZ.v (Seq.index hull (top - 1)) in
    let t2 = SZ.v (Seq.index hull (top - 2)) in
    if t1 >= Seq.length xs || t2 >= Seq.length xs || p_idx >= Seq.length xs ||
       Seq.length ys <> Seq.length xs
    then ()
    else
      let cp = cross_prod
        (Seq.index xs t2) (Seq.index ys t2)
        (Seq.index xs t1) (Seq.index ys t1)
        (Seq.index xs p_idx) (Seq.index ys p_idx) in
      if cp <= 0 then begin
        if top - 1 >= 2 then pop_while_spec_ge_1 xs ys hull (top - 1) p_idx
        else ()
      end else ()

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"
let scan_step_preserves_left_turns
  (xs ys: Seq.seq int) (hull: Seq.seq SZ.t) (top: nat) (p_idx: SZ.t)
  : Lemma
    (requires
      all_left_turns_sz xs ys hull top /\
      top >= 2 /\ top <= Seq.length hull /\
      SZ.v p_idx < Seq.length xs /\ Seq.length ys == Seq.length xs /\
      (forall (i: nat). i < top ==> SZ.v (Seq.index hull i) < Seq.length xs) /\
      pop_while_spec xs ys hull top (SZ.v p_idx) < Seq.length hull)
    (ensures (
      let top' = pop_while_spec xs ys hull top (SZ.v p_idx) in
      all_left_turns_sz xs ys (Seq.upd hull top' p_idx) (top' + 1))) =
  pop_while_spec_bounded xs ys hull top (SZ.v p_idx);
  pop_while_ensures_left_turn xs ys hull top (SZ.v p_idx);
  let top' = pop_while_spec xs ys hull top (SZ.v p_idx) in
  let hull' = Seq.upd hull top' p_idx in
  // For i + 2 < top': hull'[i] == hull[i] for all positions < top',
  // so all_left_turns_sz for the prefix follows from the original.
  // For i + 2 == top' (when top' >= 2): pop_while_ensures_left_turn gives cp > 0.
  assert (forall (i: nat). i < top' ==> Seq.index hull' i == Seq.index hull i);
  assert (top' <= top);
  ()
#pop-options
