(*
   Jarvis's March (Gift Wrapping) — CLRS Chapter 33, Section 33.3
   
   Pulse implementations of find_leftmost, find_next, and jarvis_march,
   each proven functionally equivalent to the pure specification.
   
   NO admits. NO assumes.
*)

module CLRS.Ch33.JarvisMarch.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.JarvisMarch.Spec
open CLRS.Ch33.JarvisMarch.Lemmas
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

//SNIPPET_START: find_leftmost_impl
fn find_leftmost (#p: perm) (xs ys: array int)
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
      SZ.v result == find_leftmost_spec sxs sys /\
      SZ.v result < SZ.v len
    )
{
  find_leftmost_spec_bounded sxs sys;
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
      find_leftmost_aux sxs sys (SZ.v vi) (SZ.v vbest) == find_leftmost_spec sxs sys
    )
  decreases (SZ.v len - SZ.v !i)
  {
    let vi = !i;
    let vbest = !best;
    let xi = xs.(vi);
    let xb = xs.(vbest);
    let yi = ys.(vi);
    let yb = ys.(vbest);

    if (xi < xb || (xi = xb && yi < yb)) {
      best := vi
    };

    i := SZ.add vi 1sz
  };

  !best
}
//SNIPPET_END: find_leftmost_impl

//SNIPPET_START: find_next_impl
fn find_next (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t) (current: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len > 1 /\
      SZ.v current < SZ.v len /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys
    )
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v result == find_next_spec sxs sys (SZ.v current) /\
      SZ.v result < SZ.v len
    )
{
  find_next_spec_bounded sxs sys (SZ.v current);
  let mut next: SZ.t = current;
  let mut j: SZ.t = 0sz;

  while (!j <^ len)
  invariant exists* vj vnext.
    R.pts_to j vj **
    R.pts_to next vnext **
    A.pts_to xs #p sxs **
    A.pts_to ys #p sys **
    pure (
      SZ.v vj <= SZ.v len /\
      SZ.v vnext < SZ.v len /\
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v current < SZ.v len /\
      find_next_aux sxs sys (SZ.v current) (SZ.v vnext) (SZ.v vj) ==
        find_next_spec sxs sys (SZ.v current)
    )
  decreases (SZ.v len - SZ.v !j)
  {
    let vj = !j;
    let vnext = !next;

    let cx = xs.(current);
    let cy = ys.(current);
    let nx = xs.(vnext);
    let ny = ys.(vnext);
    let jx = xs.(vj);
    let jy = ys.(vj);
    let cp = (nx - cx) * (jy - cy) - (jx - cx) * (ny - cy);

    let do_update = not (vj = current) && ((vnext = current) || (cp < 0));
    if do_update {
      next := vj
    };

    j := SZ.add vj 1sz
  };

  !next
}
//SNIPPET_END: find_next_impl

//SNIPPET_START: jarvis_march_impl
#push-options "--fuel 2 --ifuel 0"
fn jarvis_march (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len > 1 /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys
    )
  returns h: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v h == jarvis_march_spec sxs sys /\
      SZ.v h >= 1 /\
      SZ.v h <= SZ.v len
    )
{
  jarvis_march_spec_bounded sxs sys;
  let p0 = find_leftmost xs ys len;
  let first_next = find_next xs ys len p0;

  if (first_next = p0) {
    1sz
  } else {
    let mut h: SZ.t = 2sz;
    let mut current: SZ.t = first_next;
    let mut running: bool = true;

    while (!running)
    invariant exists* vrunning vcurrent vh.
      R.pts_to running vrunning **
      R.pts_to current vcurrent **
      R.pts_to h vh **
      A.pts_to xs #p sxs **
      A.pts_to ys #p sys **
      pure (
        SZ.v vh >= 2 /\
        SZ.v vh <= SZ.v len /\
        SZ.v vcurrent < SZ.v len /\
        SZ.v len == Seq.length sxs /\
        Seq.length sxs == Seq.length sys /\
        SZ.v len > 1 /\
        SZ.v len == A.length xs /\
        SZ.v len == A.length ys /\
        jarvis_march_spec sxs sys <= SZ.v len /\
        jarvis_march_spec sxs sys >= 1 /\
        (vrunning ==>
          SZ.v vh + jarvis_loop_count sxs sys (SZ.v p0) (SZ.v vcurrent)
            (SZ.v len - SZ.v vh)
          == jarvis_march_spec sxs sys) /\
        (not vrunning ==>
          SZ.v vh == jarvis_march_spec sxs sys)
      )
    decreases (SZ.v len - SZ.v !h + (if !running then 1 else 0))
    {
      let vc = !current;
      let next = find_next xs ys len vc;
      let vh = !h;
      let go = not (next = p0) && (vh <^ len);

      if go {
        h := SZ.add vh 1sz;
        current := next
      } else {
        running := false
      }
    };

    !h
  }
}
#pop-options
//SNIPPET_END: jarvis_march_impl
