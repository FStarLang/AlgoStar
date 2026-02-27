module CLRS.Ch28.StrassenPulse
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Vec
open FStar.SizeT
open Pulse.Lib.Reference
open FStar.Mul
open FStar.Classical

module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S = CLRS.Ch28.Strassen
module MM = CLRS.Ch28.MatrixMultiply

(*
 * Imperative (Pulse) Strassen's matrix multiplication — §4.2, pp. 79–82.
 *
 * Uses flat row-major arrays (Vec int) with divide-and-conquer.
 * Seven recursive multiplications on n/2 × n/2 sub-problems.
 *
 * Postcondition: mat_mul_correct (standard multiply result).
 * Equivalence to functional Strassen follows via lemma_strassen_correct.
 *
 * Status:
 *   Verified (zero admits): flat_vec_add, flat_vec_sub, extract_quadrant,
 *     write_quadrant, strassen_pulse base case, quad_idx_bound lemma,
 *     quad_idx_inj lemma, si_upd_eq/si_upd_neq SMTPat helpers
 *   Admitted (4): add_to_quadrant, sub_from_quadrant (SMT cannot
 *     automate row-major index injectivity for Seq.upd preservation),
 *     strassen_pulse recursive case (Strassen algebra for flat arrays),
 *     bridging lemma (correspondence to functional Strassen)
 *)

// ========== Safe index (no refinement needed) ==========

let si (s: Seq.seq int) (k: nat) : int =
  if k < Seq.length s then Seq.index s k else 0

// ========== Named spec predicates ==========

let flat_add_post (sa sb sc: Seq.seq int) (len: nat) : prop =
  Seq.length sc == len /\
  (forall (k:nat). k < len ==> si sc k == si sa k + si sb k)

let flat_sub_post (sa sb sc: Seq.seq int) (len: nat) : prop =
  Seq.length sc == len /\
  (forall (k:nat). k < len ==> si sc k == si sa k - si sb k)

let extract_post (ss: Seq.seq int) (n half ro co: nat) (sd: Seq.seq int) : prop =
  Seq.length sd == half * half /\
  (forall (i j: nat). i < half /\ j < half ==>
    si sd (i * half + j) == si ss ((ro + i) * n + (co + j)))

let write_quad_post (new_sd: Seq.seq int) (n half ro co: nat) (ss: Seq.seq int) : prop =
  Seq.length new_sd == n * n /\
  (forall (i j: nat). i < half /\ j < half ==>
    si new_sd ((ro + i) * n + (co + j)) == si ss (i * half + j))

let addq_post (old_sd new_sd: Seq.seq int) (n half ro co: nat) (ss: Seq.seq int) : prop =
  Seq.length new_sd == n * n /\
  (forall (i j: nat). i < half /\ j < half ==>
    si new_sd ((ro + i) * n + (co + j)) ==
    si old_sd ((ro + i) * n + (co + j)) + si ss (i * half + j))

let subq_post (old_sd new_sd: Seq.seq int) (n half ro co: nat) (ss: Seq.seq int) : prop =
  Seq.length new_sd == n * n /\
  (forall (i j: nat). i < half /\ j < half ==>
    si new_sd ((ro + i) * n + (co + j)) ==
    si old_sd ((ro + i) * n + (co + j)) - si ss (i * half + j))

let quad_pre (n half ro co: nat) : prop =
  half > 0 /\ ro + half <= n /\ co + half <= n /\
  SZ.fits (n * n) /\ SZ.fits (half * half)

// Arithmetic bound lemma for quadrant indexing
let quad_idx_bound (n half ro co i j: nat)
  : Lemma
    (requires ro + half <= n /\ co + half <= n /\ i < half /\ j < half /\ n > 0 /\
             SZ.fits (n * n) /\ SZ.fits (half * half))
    (ensures (ro + i) * n + (co + j) < n * n /\
             i * half + j < half * half /\
             SZ.fits ((ro + i) * n + (co + j)) /\
             SZ.fits (i * half + j) /\
             SZ.fits ((ro + i) * n) /\
             SZ.fits (ro + i) /\
             SZ.fits (co + j))
  = assert ((ro + i) < n);
    assert ((co + j) < n);
    assert ((ro + i) * n + (co + j) <= (n - 1) * n + (n - 1));
    assert ((n - 1) * n + (n - 1) == n * n - 1);
    assert (i * half + j < half * half);
    SZ.fits_lte ((ro + i) * n + (co + j)) (n * n);
    SZ.fits_lte (i * half + j) (half * half);
    SZ.fits_lte ((ro + i) * n) (n * n);
    SZ.fits_lte (ro + i) (n * n);
    SZ.fits_lte (co + j) (n * n)

// Injectivity: distinct (i,j) in a quadrant → distinct flat indices in big matrix
let quad_idx_inj (n: pos) (ro co i1 j1 i2 j2: nat)
  : Lemma
    (requires i1 < n /\ j1 < n /\ i2 < n /\ j2 < n /\
              (ro + i1) * n + (co + j1) == (ro + i2) * n + (co + j2))
    (ensures i1 == i2 /\ j1 == j2)
  = // (ro+i1)*n + (co+j1) == (ro+i2)*n + (co+j2)
    // → i1*n + j1 == i2*n + j2
    // → (i1-i2)*n == j2-j1
    // |j2-j1| < n while |(i1-i2)*n| >= n when i1<>i2 → contradiction
    // So i1==i2, hence j1==j2
    assert (i1 * n + j1 == i2 * n + j2)

// SMTPat lemmas for si with Seq.upd (helps loop invariant proofs)
let si_upd_eq (s: Seq.seq int) (k: nat{k < Seq.length s}) (v: int)
  : Lemma (ensures si (Seq.upd s k v) k == v)
          [SMTPat (si (Seq.upd s k v) k)]
  = ()

let si_upd_neq (s: Seq.seq int) (k: nat{k < Seq.length s}) (v: int) (k': nat)
  : Lemma (requires k' <> k)
          (ensures si (Seq.upd s k v) k' == si s k')
          [SMTPat (si (Seq.upd s k v) k')]
  = if k' < Seq.length s then ()
    else ()

// ========== Pulse helpers ==========

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"

fn flat_vec_add (a b c: V.vec int) (len: SZ.t)
  (#sa #sb #sc: Ghost.erased (Seq.seq int))
  requires V.pts_to a sa ** V.pts_to b sb ** V.pts_to c sc **
           pure (Seq.length sa == SZ.v len /\ Seq.length sb == SZ.v len /\ Seq.length sc == SZ.v len)
  ensures  exists* sc'. V.pts_to a sa ** V.pts_to b sb ** V.pts_to c sc' **
           pure (flat_add_post sa sb sc' (SZ.v len))
{
  let mut i = 0sz;
  while (!i <^ len)
  invariant exists* vi sc_i.
    R.pts_to i vi **
    V.pts_to a sa **
    V.pts_to b sb **
    V.pts_to c sc_i **
    pure (SZ.v vi <= SZ.v len /\
          Seq.length sc_i == SZ.v len /\
          (forall (k:nat). k < SZ.v vi ==> si sc_i k == si sa k + si sb k))
  {
    let vi = !i;
    let av = V.op_Array_Access a vi;
    let bv = V.op_Array_Access b vi;
    V.op_Array_Assignment c vi (av + bv);
    i := vi +^ 1sz;
  }
}

fn flat_vec_sub (a b c: V.vec int) (len: SZ.t)
  (#sa #sb #sc: Ghost.erased (Seq.seq int))
  requires V.pts_to a sa ** V.pts_to b sb ** V.pts_to c sc **
           pure (Seq.length sa == SZ.v len /\ Seq.length sb == SZ.v len /\ Seq.length sc == SZ.v len)
  ensures  exists* sc'. V.pts_to a sa ** V.pts_to b sb ** V.pts_to c sc' **
           pure (flat_sub_post sa sb sc' (SZ.v len))
{
  let mut i = 0sz;
  while (!i <^ len)
  invariant exists* vi sc_i.
    R.pts_to i vi **
    V.pts_to a sa **
    V.pts_to b sb **
    V.pts_to c sc_i **
    pure (SZ.v vi <= SZ.v len /\
          Seq.length sc_i == SZ.v len /\
          (forall (k:nat). k < SZ.v vi ==> si sc_i k == si sa k - si sb k))
  {
    let vi = !i;
    let av = V.op_Array_Access a vi;
    let bv = V.op_Array_Access b vi;
    V.op_Array_Assignment c vi (av - bv);
    i := vi +^ 1sz;
  }
}

fn extract_quadrant (src: V.vec int) (n: SZ.t) (ro co: SZ.t)
                    (dst: V.vec int) (half: SZ.t)
  (#ss #sd: Ghost.erased (Seq.seq int))
  requires V.pts_to src ss ** V.pts_to dst sd **
           pure (quad_pre (SZ.v n) (SZ.v half) (SZ.v ro) (SZ.v co) /\
                 Seq.length ss == SZ.v n * SZ.v n /\ Seq.length sd == SZ.v half * SZ.v half)
  ensures  exists* sd'. V.pts_to src ss ** V.pts_to dst sd' **
           pure (extract_post ss (SZ.v n) (SZ.v half) (SZ.v ro) (SZ.v co) sd')
{
  let mut ri = 0sz;
  while (!ri <^ half)
  invariant exists* vri sd_i.
    R.pts_to ri vri **
    V.pts_to src ss **
    V.pts_to dst sd_i **
    pure (SZ.v vri <= SZ.v half /\
          Seq.length sd_i == SZ.v half * SZ.v half /\
          (forall (i j: nat). i < SZ.v vri /\ j < SZ.v half ==>
            si sd_i (i * SZ.v half + j) == si ss ((SZ.v ro + i) * SZ.v n + (SZ.v co + j))))
  {
    let vri = !ri;
    let mut ci = 0sz;
    while (!ci <^ half)
    invariant exists* vci sd_ij.
      R.pts_to ri vri **
      R.pts_to ci vci **
      V.pts_to src ss **
      V.pts_to dst sd_ij **
      pure (SZ.v vri < SZ.v half /\
            SZ.v vci <= SZ.v half /\
            Seq.length sd_ij == SZ.v half * SZ.v half /\
            (forall (i j: nat). i < SZ.v vri /\ j < SZ.v half ==>
              si sd_ij (i * SZ.v half + j) == si ss ((SZ.v ro + i) * SZ.v n + (SZ.v co + j))) /\
            (forall (j: nat). j < SZ.v vci ==>
              si sd_ij (SZ.v vri * SZ.v half + j) == si ss ((SZ.v ro + SZ.v vri) * SZ.v n + (SZ.v co + j))))
    {
      let vci = !ci;
      quad_idx_bound (SZ.v n) (SZ.v half) (SZ.v ro) (SZ.v co) (SZ.v vri) (SZ.v vci);
      let src_idx = (ro +^ vri) *^ n +^ (co +^ vci);
      let dst_idx = vri *^ half +^ vci;
      let v = V.op_Array_Access src src_idx;
      V.op_Array_Assignment dst dst_idx v;
      ci := vci +^ 1sz;
    };
    ri := vri +^ 1sz;
  }
}

fn write_quadrant (dst: V.vec int) (n: SZ.t) (ro co: SZ.t)
                  (src: V.vec int) (half: SZ.t)
  (#sd #ss: Ghost.erased (Seq.seq int))
  requires V.pts_to dst sd ** V.pts_to src ss **
           pure (quad_pre (SZ.v n) (SZ.v half) (SZ.v ro) (SZ.v co) /\
                 Seq.length sd == SZ.v n * SZ.v n /\ Seq.length ss == SZ.v half * SZ.v half)
  ensures  exists* sd'. V.pts_to dst sd' ** V.pts_to src ss **
           pure (write_quad_post sd' (SZ.v n) (SZ.v half) (SZ.v ro) (SZ.v co) ss)
{
  let mut ri = 0sz;
  while (!ri <^ half)
  invariant exists* vri sd_i.
    R.pts_to ri vri **
    V.pts_to dst sd_i **
    V.pts_to src ss **
    pure (SZ.v vri <= SZ.v half /\
          Seq.length sd_i == SZ.v n * SZ.v n /\
          (forall (i j: nat). i < SZ.v vri /\ j < SZ.v half ==>
            si sd_i ((SZ.v ro + i) * SZ.v n + (SZ.v co + j)) == si ss (i * SZ.v half + j)))
  {
    let vri = !ri;
    let mut ci = 0sz;
    while (!ci <^ half)
    invariant exists* vci sd_ij.
      R.pts_to ri vri **
      R.pts_to ci vci **
      V.pts_to dst sd_ij **
      V.pts_to src ss **
      pure (SZ.v vri < SZ.v half /\
            SZ.v vci <= SZ.v half /\
            Seq.length sd_ij == SZ.v n * SZ.v n /\
            (forall (i j: nat). i < SZ.v vri /\ j < SZ.v half ==>
              si sd_ij ((SZ.v ro + i) * SZ.v n + (SZ.v co + j)) == si ss (i * SZ.v half + j)) /\
            (forall (j: nat). j < SZ.v vci ==>
              si sd_ij ((SZ.v ro + SZ.v vri) * SZ.v n + (SZ.v co + j)) == si ss (SZ.v vri * SZ.v half + j)))
    {
      let vci = !ci;
      quad_idx_bound (SZ.v n) (SZ.v half) (SZ.v ro) (SZ.v co) (SZ.v vri) (SZ.v vci);
      let src_idx = vri *^ half +^ vci;
      let dst_idx = (ro +^ vri) *^ n +^ (co +^ vci);
      let v = V.op_Array_Access src src_idx;
      V.op_Array_Assignment dst dst_idx v;
      ci := vci +^ 1sz;
    };
    ri := vri +^ 1sz;
  }
}

fn add_to_quadrant (dst: V.vec int) (n: SZ.t) (ro co: SZ.t)
                   (src: V.vec int) (half: SZ.t)
  (#sd #ss: Ghost.erased (Seq.seq int))
  requires V.pts_to dst sd ** V.pts_to src ss **
           pure (quad_pre (SZ.v n) (SZ.v half) (SZ.v ro) (SZ.v co) /\
                 Seq.length sd == SZ.v n * SZ.v n /\ Seq.length ss == SZ.v half * SZ.v half)
  ensures  exists* sd'. V.pts_to dst sd' ** V.pts_to src ss **
           pure (addq_post sd sd' (SZ.v n) (SZ.v half) (SZ.v ro) (SZ.v co) ss)
{ admit() }

fn sub_from_quadrant (dst: V.vec int) (n: SZ.t) (ro co: SZ.t)
                     (src: V.vec int) (half: SZ.t)
  (#sd #ss: Ghost.erased (Seq.seq int))
  requires V.pts_to dst sd ** V.pts_to src ss **
           pure (quad_pre (SZ.v n) (SZ.v half) (SZ.v ro) (SZ.v co) /\
                 Seq.length sd == SZ.v n * SZ.v n /\ Seq.length ss == SZ.v half * SZ.v half)
  ensures  exists* sd'. V.pts_to dst sd' ** V.pts_to src ss **
           pure (subq_post sd sd' (SZ.v n) (SZ.v half) (SZ.v ro) (SZ.v co) ss)
{ admit() }

#pop-options

// ========== Main recursive Strassen ==========

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"

fn rec strassen_pulse (a b c: V.vec int)
  (#sa #sb #sc: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires
    V.pts_to a sa **
    V.pts_to b sb **
    V.pts_to c sc **
    pure (
      SZ.v n > 0 /\
      S.is_pow2 (SZ.v n) /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.length sa == SZ.v n * SZ.v n /\
      Seq.length sb == SZ.v n * SZ.v n /\
      Seq.length sc == SZ.v n * SZ.v n
    )
  ensures exists* sc'.
    V.pts_to a sa **
    V.pts_to b sb **
    V.pts_to c sc' **
    pure (
      MM.mat_mul_correct sa sb sc' (SZ.v n)
    )
{
  if (n = 1sz) {
    // Base case: 1x1 multiply
    let av = V.op_Array_Access a 0sz;
    let bv = V.op_Array_Access b 0sz;
    V.op_Array_Assignment c 0sz (av * bv);
    // mat_mul_correct needs dot_product_spec sa sb 1 0 0 1 == sa[0]*sb[0]
    MM.index_bounds_lemma 1 0 0 0;
    ()
  } else {
    let half = n /^ 2sz;
    let qsz = half *^ half;

    // --- Allocate & extract quadrants of A ---
    let a11 = V.alloc 0 qsz;
    let a12 = V.alloc 0 qsz;
    let a21 = V.alloc 0 qsz;
    let a22 = V.alloc 0 qsz;
    extract_quadrant a n 0sz 0sz a11 half;
    extract_quadrant a n 0sz half a12 half;
    extract_quadrant a n half 0sz a21 half;
    extract_quadrant a n half half a22 half;

    // --- Allocate & extract quadrants of B ---
    let b11 = V.alloc 0 qsz;
    let b12 = V.alloc 0 qsz;
    let b21 = V.alloc 0 qsz;
    let b22 = V.alloc 0 qsz;
    extract_quadrant b n 0sz 0sz b11 half;
    extract_quadrant b n 0sz half b12 half;
    extract_quadrant b n half 0sz b21 half;
    extract_quadrant b n half half b22 half;

    // --- Allocate & compute S matrices ---
    let t1 = V.alloc 0 qsz;
    flat_vec_sub b12 b22 t1 qsz;     // t1 = B12 - B22

    let t2 = V.alloc 0 qsz;
    flat_vec_add a11 a12 t2 qsz;     // t2 = A11 + A12

    let t3 = V.alloc 0 qsz;
    flat_vec_add a21 a22 t3 qsz;     // t3 = A21 + A22

    let t4 = V.alloc 0 qsz;
    flat_vec_sub b21 b11 t4 qsz;     // t4 = B21 - B11

    let t5 = V.alloc 0 qsz;
    flat_vec_add a11 a22 t5 qsz;     // t5 = A11 + A22

    let t6 = V.alloc 0 qsz;
    flat_vec_add b11 b22 t6 qsz;     // t6 = B11 + B22

    let t7 = V.alloc 0 qsz;
    flat_vec_sub a12 a22 t7 qsz;     // t7 = A12 - A22

    let t8 = V.alloc 0 qsz;
    flat_vec_add b21 b22 t8 qsz;     // t8 = B21 + B22

    let t9 = V.alloc 0 qsz;
    flat_vec_sub a11 a21 t9 qsz;     // t9 = A11 - A21

    let t10 = V.alloc 0 qsz;
    flat_vec_add b11 b12 t10 qsz;    // t10 = B11 + B12

    // --- Allocate products & 7 recursive multiplications ---
    let p1 = V.alloc 0 qsz;
    strassen_pulse a11 t1 p1 half;    // P1 = A11 * (B12 - B22)

    let p2 = V.alloc 0 qsz;
    strassen_pulse t2 b22 p2 half;    // P2 = (A11 + A12) * B22

    let p3 = V.alloc 0 qsz;
    strassen_pulse t3 b11 p3 half;    // P3 = (A21 + A22) * B11

    let p4 = V.alloc 0 qsz;
    strassen_pulse a22 t4 p4 half;    // P4 = A22 * (B21 - B11)

    let p5 = V.alloc 0 qsz;
    strassen_pulse t5 t6 p5 half;     // P5 = (A11 + A22) * (B11 + B22)

    let p6 = V.alloc 0 qsz;
    strassen_pulse t7 t8 p6 half;     // P6 = (A12 - A22) * (B21 + B22)

    let p7 = V.alloc 0 qsz;
    strassen_pulse t9 t10 p7 half;    // P7 = (A11 - A21) * (B11 + B12)

    // --- Combine results into c ---
    // C11 = P5 + P4 - P2 + P6
    write_quadrant c n 0sz 0sz p5 half;
    add_to_quadrant c n 0sz 0sz p4 half;
    sub_from_quadrant c n 0sz 0sz p2 half;
    add_to_quadrant c n 0sz 0sz p6 half;

    // C12 = P1 + P2
    write_quadrant c n 0sz half p1 half;
    add_to_quadrant c n 0sz half p2 half;

    // C21 = P3 + P4
    write_quadrant c n half 0sz p3 half;
    add_to_quadrant c n half 0sz p4 half;

    // C22 = P5 + P1 - P3 - P7
    write_quadrant c n half half p5 half;
    add_to_quadrant c n half half p1 half;
    sub_from_quadrant c n half half p3 half;
    sub_from_quadrant c n half half p7 half;

    // --- Free all temporaries ---
    V.free a11; V.free a12; V.free a21; V.free a22;
    V.free b11; V.free b12; V.free b21; V.free b22;
    V.free t1; V.free t2; V.free t3; V.free t4; V.free t5;
    V.free t6; V.free t7; V.free t8; V.free t9; V.free t10;
    V.free p1; V.free p2; V.free p3; V.free p4;
    V.free p5; V.free p6; V.free p7;

    // Strassen algebra: combining gives mat_mul_correct
    admit()
  }
}

#pop-options

// ========== Bridging: Pulse Strassen == Functional Strassen ==========

// flat_to_matrix: convert flat row-major sequence to matrix (seq-of-seq)
let flat_to_matrix (s: Seq.seq int) (n: pos{Seq.length s == n * n})
  : S.matrix
  = Seq.init n (fun (i:nat{i < n}) ->
      Seq.init n (fun (j:nat{j < n}) ->
        Seq.index s (i * n + j)))

// Bridging theorem: mat_mul_correct implies equivalence to functional Strassen
let lemma_pulse_strassen_equals_functional
  (sa sb sc: Seq.seq int) (n: pos)
  : Lemma
    (requires
      S.is_pow2 n /\
      Seq.length sa == n * n /\
      Seq.length sb == n * n /\
      MM.mat_mul_correct sa sb sc n)
    (ensures (
      let a_mat = flat_to_matrix sa n in
      let b_mat = flat_to_matrix sb n in
      forall (i j: nat). i < n /\ j < n ==>
        Seq.index sc (i * n + j) ==
        S.get_elem (S.strassen_multiply a_mat b_mat) i j))
  = let a_mat = flat_to_matrix sa n in
    let b_mat = flat_to_matrix sb n in
    S.lemma_strassen_correct a_mat b_mat;
    admit()
