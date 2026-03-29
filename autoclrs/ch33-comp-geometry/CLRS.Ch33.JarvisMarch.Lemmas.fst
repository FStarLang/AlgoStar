(*
   Jarvis's March (Gift Wrapping) — CLRS Chapter 33, Section 33.3
   
   Proofs of Jarvis march correctness properties.
   
   NO admits. NO assumes.
*)

module CLRS.Ch33.JarvisMarch.Lemmas
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.JarvisMarch.Spec
open FStar.Mul

module Seq = FStar.Seq
module SZ = FStar.SizeT

// ========== Bounds Lemmas ==========

let rec find_leftmost_aux_bounded (xs ys: Seq.seq int) (i best: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0 /\ best < Seq.length xs)
          (ensures find_leftmost_aux xs ys i best < Seq.length xs)
          (decreases (Seq.length xs - i)) =
  if i >= Seq.length xs then ()
  else
    let new_best =
      if Seq.index xs i < Seq.index xs best ||
         (Seq.index xs i = Seq.index xs best && Seq.index ys i < Seq.index ys best)
      then i
      else best
    in
    find_leftmost_aux_bounded xs ys (i + 1) new_best

let find_leftmost_spec_bounded (xs ys: Seq.seq int)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0)
          (ensures find_leftmost_spec xs ys < Seq.length xs) =
  find_leftmost_aux_bounded xs ys 1 0

let rec find_next_aux_bounded (xs ys: Seq.seq int) (current next: nat) (j: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ current < Seq.length xs /\ next < Seq.length xs)
          (ensures find_next_aux xs ys current next j < Seq.length xs)
          (decreases (Seq.length xs - j)) =
  if j >= Seq.length xs then ()
  else if j = current then find_next_aux_bounded xs ys current next (j + 1)
  else if next = current then find_next_aux_bounded xs ys current j (j + 1)
  else
    let cp = cross_prod
      (Seq.index xs current) (Seq.index ys current)
      (Seq.index xs next) (Seq.index ys next)
      (Seq.index xs j) (Seq.index ys j) in
    let new_next = if cp < 0 then j else next in
    find_next_aux_bounded xs ys current new_next (j + 1)

let find_next_spec_bounded (xs ys: Seq.seq int) (current: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 1 /\ current < Seq.length xs)
          (ensures find_next_spec xs ys current < Seq.length xs) =
  find_next_aux_bounded xs ys current current 0

let rec find_next_aux_not_current (xs ys: Seq.seq int) (current next: nat) (j: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 1 /\
                    current < Seq.length xs /\ next < Seq.length xs /\
                    (next <> current \/ (exists (k: nat). k >= j /\ k < Seq.length xs /\ k <> current)))
          (ensures find_next_aux xs ys current next j <> current)
          (decreases (Seq.length xs - j)) =
  if j >= Seq.length xs then ()
  else if j = current then
    find_next_aux_not_current xs ys current next (j + 1)
  else if next = current then
    find_next_aux_not_current xs ys current j (j + 1)
  else begin
    let cp = cross_prod
      (Seq.index xs current) (Seq.index ys current)
      (Seq.index xs next) (Seq.index ys next)
      (Seq.index xs j) (Seq.index ys j) in
    let new_next = if cp < 0 then j else next in
    find_next_aux_not_current xs ys current new_next (j + 1)
  end

let find_next_spec_not_current (xs ys: Seq.seq int) (current: nat)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 1 /\
                    current < Seq.length xs)
          (ensures find_next_spec xs ys current <> current) =
  let other = if current = 0 then 1 else 0 in
  assert (other < Seq.length xs /\ other <> current);
  find_next_aux_not_current xs ys current current 0

// ========== Loop and March Bounds ==========

let rec jarvis_loop_count_bounded (xs ys: Seq.seq int) (start current: nat) (fuel: nat)
  : Lemma (ensures jarvis_loop_count xs ys start current fuel <= fuel)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    let next = find_next_spec xs ys current in
    if next = start then ()
    else jarvis_loop_count_bounded xs ys start next (fuel - 1)

let jarvis_march_spec_bounded (xs ys: Seq.seq int)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 1)
          (ensures jarvis_march_spec xs ys <= Seq.length xs /\
                   jarvis_march_spec xs ys >= 1) =
  let n = Seq.length xs in
  let p0 = find_leftmost_spec xs ys in
  jarvis_loop_count_bounded xs ys p0 p0 (n - 1)

let jarvis_loop_step (xs ys: Seq.seq int) (start current: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\ find_next_spec xs ys current <> start)
          (ensures jarvis_loop_count xs ys start current fuel ==
                   1 + jarvis_loop_count xs ys start
                       (find_next_spec xs ys current) (fuel - 1) /\
                   jarvis_loop_count xs ys start current fuel >= 1) = ()

// ========== Correctness Lemmas ==========

let rec find_leftmost_aux_is_min (xs ys: Seq.seq int) (i best: nat)
  : Lemma (requires
      Seq.length ys == Seq.length xs /\ Seq.length xs > 0 /\
      best < Seq.length xs /\
      (forall (k: nat). k < i /\ k < Seq.length xs ==>
        Seq.index xs best < Seq.index xs k \/
        (Seq.index xs best = Seq.index xs k /\ Seq.index ys best <= Seq.index ys k)))
    (ensures is_leftmost xs ys (find_leftmost_aux xs ys i best))
    (decreases (Seq.length xs - i)) =
  if i >= Seq.length xs then ()
  else
    let xi = Seq.index xs i in
    let xb = Seq.index xs best in
    let yi = Seq.index ys i in
    let yb = Seq.index ys best in
    let new_best = if xi < xb || (xi = xb && yi < yb) then i else best in
    find_leftmost_aux_is_min xs ys (i + 1) new_best

let find_leftmost_is_leftmost (xs ys: Seq.seq int)
  : Lemma (requires Seq.length ys == Seq.length xs /\ Seq.length xs > 0)
          (ensures is_leftmost xs ys (find_leftmost_spec xs ys)) =
  find_leftmost_aux_is_min xs ys 1 0

let cross_prod_swap23 (x1 y1 x2 y2 x3 y3: int) : Lemma
  (ensures cross_prod x1 y1 x3 y3 x2 y2 == -(cross_prod x1 y1 x2 y2 x3 y3)) = ()

#push-options "--z3rlimit 10"
let half_plane_transitivity (ax ay bx b_y cx cy: int) : Lemma
  (requires ay >= 0 /\ b_y > 0 /\ cy >= 0 /\
            ax * b_y - bx * ay >= 0 /\
            bx * cy - cx * b_y >= 0)
  (ensures ax * cy - cx * ay >= 0) =
  let h1_cy = (ax * b_y - bx * ay) * cy in
  let h2_ay = (bx * cy - cx * b_y) * ay in
  assert (h1_cy >= 0);
  assert (h2_ay >= 0);
  assert (ax * b_y * cy - bx * ay * cy >= 0);
  assert (bx * cy * ay - cx * b_y * ay >= 0);
  assert (bx * ay * cy == bx * cy * ay);
  assert (ax * b_y * cy >= cx * b_y * ay);
  ()
#pop-options

#push-options "--z3rlimit 10"
let cross_prod_transitivity (cx c_y nx ny jx jy kx ky: int) : Lemma
  (requires
    ny - c_y > 0 /\ jy - c_y >= 0 /\ ky - c_y >= 0 /\
    cross_prod cx c_y nx ny jx jy < 0 /\
    cross_prod cx c_y nx ny kx ky >= 0)
  (ensures cross_prod cx c_y jx jy kx ky >= 0)
  [SMTPat (cross_prod cx c_y jx jy kx ky); SMTPat (cross_prod cx c_y nx ny kx ky)] =
  let ax = jx - cx in let ay = jy - c_y in
  let bx = nx - cx in let b_y = ny - c_y in
  let dx = kx - cx in let d_y = ky - c_y in
  half_plane_transitivity ax ay bx b_y dx d_y
#pop-options

let cross_prod_transitivity_degenerate (cx c_y nx ny jx jy: int) : Lemma
  (requires
    ny = c_y /\ jy - c_y >= 0 /\
    cross_prod cx c_y nx ny jx jy < 0)
  (ensures cross_prod cx c_y jx jy nx ny > 0) =
  cross_prod_swap23 cx c_y nx ny jx jy

let rec find_next_aux_beats_all (xs ys: Seq.seq int) (current next: nat) (j: nat)
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
    (decreases (Seq.length xs - j)) =
  find_next_aux_bounded xs ys current next j;
  if j >= Seq.length xs then ()
  else if j = current then
    find_next_aux_beats_all xs ys current next (j + 1)
  else if next = current then
    find_next_aux_beats_all xs ys current j (j + 1)
  else begin
    let cx = Seq.index xs current in let cy' = Seq.index ys current in
    let nx = Seq.index xs next in let ny = Seq.index ys next in
    let jx = Seq.index xs j in let jy = Seq.index ys j in
    let cp = cross_prod cx cy' nx ny jx jy in
    if cp < 0 then begin
      assert (ny - cy' > 0);
      find_next_aux_beats_all xs ys current j (j + 1)
    end else
      find_next_aux_beats_all xs ys current next (j + 1)
  end

let find_next_all_left_of (xs ys: Seq.seq int) (current: nat)
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
    (ensures all_left_of xs ys current (find_next_spec xs ys current)) =
  find_next_spec_not_current xs ys current;
  find_next_aux_beats_all xs ys current current 0;
  find_next_spec_bounded xs ys current

#push-options "--z3rlimit 40 --split_queries always"
let extend_valid_jarvis_hull (xs ys: Seq.seq int) (hull: Seq.seq SZ.t) (h: nat) (next: SZ.t)
  : Lemma
    (requires
      valid_jarvis_hull xs ys hull h /\
      h < Seq.length hull /\
      SZ.v next < Seq.length xs /\
      h >= 1 /\
      SZ.v next == find_next_spec xs ys (SZ.v (Seq.index hull (h - 1))))
    (ensures
      valid_jarvis_hull xs ys (Seq.upd hull h next) (h + 1)) =
  let hull' = Seq.upd hull h next in
  // Seq.upd preserves other indices and sets position h to next
  assert (forall (i: nat). i < h ==> Seq.index hull' i == Seq.index hull i);
  assert (Seq.index hull' h == next);
  assert (Seq.length hull' == Seq.length hull)
#pop-options
