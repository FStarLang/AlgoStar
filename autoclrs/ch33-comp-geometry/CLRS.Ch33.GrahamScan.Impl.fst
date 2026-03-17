(*
   Graham Scan — CLRS Chapter 33, Section 33.3
   
   Pulse implementations of find_bottom, polar_cmp, and pop_while,
   each proven functionally equivalent to the pure specification.
   
   NO admits. NO assumes.
*)

module CLRS.Ch33.GrahamScan.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.GrahamScan.Spec
open CLRS.Ch33.GrahamScan.Lemmas
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

//SNIPPET_START: find_bottom_impl
fn find_bottom (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len > 0 /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys
    )
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v result == find_bottom_spec sxs sys /\
      SZ.v result < SZ.v len /\
      is_bottommost sxs sys (SZ.v result)
    )
{
  find_bottom_spec_bounded sxs sys;
  find_bottom_is_bottommost sxs sys;
  let mut best: SZ.t = 0sz;
  let mut i: SZ.t = 1sz;

  while (!i <^ len)
  invariant exists* vi vbest.
    R.pts_to i vi **
    R.pts_to best vbest **
    A.pts_to xs #p sxs **
    A.pts_to ys #p sys **
    pure (
      SZ.v vi >= 1 /\
      SZ.v vi <= SZ.v len /\
      SZ.v vbest < SZ.v len /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len == Seq.length sxs /\
      find_bottom_aux sxs sys (SZ.v vi) (SZ.v vbest) == find_bottom_spec sxs sys
    )
  decreases (SZ.v len - SZ.v !i)
  {
    let vi = !i;
    let vbest = !best;
    let yi = ys.(vi);
    let yb = ys.(vbest);
    let xi = xs.(vi);
    let xb = xs.(vbest);

    if (yi < yb || (yi = yb && xi < xb)) {
      best := vi
    };

    i := SZ.add vi 1sz
  };

  !best
}
//SNIPPET_END: find_bottom_impl

//SNIPPET_START: polar_cmp_impl
fn polar_cmp (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t) (p0 a b: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v p0 < SZ.v len /\
      SZ.v a < SZ.v len /\
      SZ.v b < SZ.v len /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys
    )
  returns result: int
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (result == polar_cmp_spec sxs sys (SZ.v p0) (SZ.v a) (SZ.v b))
{
  let px = xs.(p0);
  let py = ys.(p0);
  let ax = xs.(a);
  let ay = ys.(a);
  let bx = xs.(b);
  let b_y = ys.(b);
  (ax - px) * (b_y - py) - (bx - px) * (ay - py)
}
//SNIPPET_END: polar_cmp_impl

//SNIPPET_START: pop_while_impl
#push-options "--fuel 2 --ifuel 0"
fn pop_while (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (#ph: perm) (hull: array SZ.t)
  (#shull: Ghost.erased (Seq.seq SZ.t))
  (top_in: SZ.t) (p_idx: SZ.t) (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    A.pts_to hull #ph shull **
    pure (
      SZ.v top_in >= 2 /\
      SZ.v top_in <= Seq.length shull /\
      SZ.v p_idx < SZ.v len /\
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys /\
      Seq.length shull == A.length hull /\
      (forall (i: nat). i < SZ.v top_in ==> SZ.v (Seq.index shull i) < SZ.v len)
    )
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    A.pts_to hull #ph shull **
    pure (
      SZ.v result == pop_while_spec sxs sys shull (SZ.v top_in) (SZ.v p_idx) /\
      SZ.v result <= SZ.v top_in /\
      SZ.v result >= 1 /\
      ensures_left_turn sxs sys shull (SZ.v result) (SZ.v p_idx)
    )
{
  pop_while_spec_bounded sxs sys shull (SZ.v top_in) (SZ.v p_idx);
  pop_while_spec_ge_1 sxs sys shull (SZ.v top_in) (SZ.v p_idx);
  pop_while_ensures_left_turn sxs sys shull (SZ.v top_in) (SZ.v p_idx);
  let mut t: SZ.t = top_in;
  let mut keep_going: bool = true;

  while (!keep_going)
  invariant exists* vt vkg.
    R.pts_to t vt **
    R.pts_to keep_going vkg **
    A.pts_to xs #p sxs **
    A.pts_to ys #p sys **
    A.pts_to hull #ph shull **
    pure (
      SZ.v vt <= SZ.v top_in /\
      SZ.v top_in <= Seq.length shull /\
      Seq.length shull == A.length hull /\
      SZ.v p_idx < SZ.v len /\
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys /\
      (forall (i: nat). i < SZ.v top_in ==> SZ.v (Seq.index shull i) < SZ.v len) /\
      (vkg ==>
        pop_while_spec sxs sys shull (SZ.v vt) (SZ.v p_idx)
        == pop_while_spec sxs sys shull (SZ.v top_in) (SZ.v p_idx)) /\
      (not vkg ==>
        SZ.v vt == pop_while_spec sxs sys shull (SZ.v top_in) (SZ.v p_idx))
    )
  decreases (SZ.v !t + (if !keep_going then 1 else 0))
  {
    let vt = !t;
    if (vt <^ 2sz) {
      keep_going := false
    } else {
      let t1_idx = hull.(SZ.sub vt 1sz);
      let t2_idx = hull.(SZ.sub vt 2sz);
      let t1x = xs.(t1_idx);
      let t1y = ys.(t1_idx);
      let t2x = xs.(t2_idx);
      let t2y = ys.(t2_idx);
      let px = xs.(p_idx);
      let py = ys.(p_idx);
      let cp = (t1x - t2x) * (py - t2y) - (px - t2x) * (t1y - t2y);
      if (cp <= 0) {
        t := SZ.sub vt 1sz
      } else {
        keep_going := false
      }
    }
  };
  !t
}
#pop-options
//SNIPPET_END: pop_while_impl

//SNIPPET_START: graham_scan_step_impl
fn graham_scan_step (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (hull: array SZ.t)
  (#shull: Ghost.erased (Seq.seq SZ.t))
  (top_in: SZ.t) (p_idx: SZ.t) (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    A.pts_to hull shull **
    pure (
      SZ.v top_in >= 2 /\
      SZ.v top_in < Seq.length shull /\
      SZ.v p_idx < SZ.v len /\
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys /\
      Seq.length shull == A.length hull /\
      Seq.length shull <= SZ.v len /\
      (forall (i: nat). i < SZ.v top_in ==> SZ.v (Seq.index shull i) < SZ.v len)
    )
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    (exists* shull'.
      A.pts_to hull shull' **
      pure (
        shull' == fst (scan_step_sz_spec sxs sys shull (SZ.v top_in) p_idx) /\
        SZ.v result == snd (scan_step_sz_spec sxs sys shull (SZ.v top_in) p_idx) /\
        SZ.v result >= 2 /\
        SZ.v result <= Seq.length shull
      ))
{
  pop_while_spec_bounded sxs sys shull (SZ.v top_in) (SZ.v p_idx);
  pop_while_spec_ge_1 sxs sys shull (SZ.v top_in) (SZ.v p_idx);
  let top' = pop_while xs ys hull top_in p_idx len;
  hull.(top') <- p_idx;
  SZ.add top' 1sz
}
//SNIPPET_END: graham_scan_step_impl
