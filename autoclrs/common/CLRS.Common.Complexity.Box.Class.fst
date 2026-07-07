module CLRS.Common.Complexity.Box.Class
#lang-pulse

open Pulse

module MR = Pulse.Lib.MonotonicGhostRef
module B = Pulse.Lib.Box

let preorder_nat : FStar.Preorder.preorder nat =
  fun (x y:nat) -> b2t (x <= y)

let ticks_t = MR.mref #nat preorder_nat

let read_cost : nat = 1
let write_cost : nat = 1
let alloc_cost : nat = 1
let free_cost : nat = 1

ghost
fn pay (ctr:ticks_t) (work:nat) (#i:erased nat)
  requires MR.pts_to ctr #1.0R i
  ensures MR.pts_to ctr #1.0R (i + work)
{
  MR.update ctr (i + work)
}

class box_class
  (ctr:ticks_t)
  (box:([@@@strictly_positive] _:Type0 -> Type0))
= {
  pts_to: (#a:Type0 -> box a -> erased a -> slprop);

  read:
    (fn (#a:Type0)
        (b:box a)
        (#v:erased a)
        (#i:erased nat)
      requires pts_to b v ** MR.pts_to ctr #1.0R i
      returns u:a
      ensures pts_to b v **
              MR.pts_to ctr #1.0R (i + read_cost) **
              pure (u == reveal v));

  write:
    (fn (#a:Type0)
        (b:box a)
        (u:a)
        (#v:erased a)
        (#i:erased nat)
      requires pts_to b v ** MR.pts_to ctr #1.0R i
      ensures pts_to b (hide u) **
              MR.pts_to ctr #1.0R (i + write_cost));

  alloc:
    (fn (#a:Type0)
        (u:a)
        (#i:erased nat)
      requires MR.pts_to ctr #1.0R i
      returns b:box a
      ensures pts_to b (hide u) **
              MR.pts_to ctr #1.0R (i + alloc_cost));

  free:
    (fn (#a:Type0)
        (b:box a)
        (#v:erased a)
        (#i:erased nat)
      requires pts_to b v ** MR.pts_to ctr #1.0R i
      ensures MR.pts_to ctr #1.0R (i + free_cost))
}

fn test
    (ctr:ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| box_class ctr box |}
    (a:Type0)
    (x:a)
requires MR.pts_to ctr #1.0R 0
ensures MR.pts_to ctr #1.0R (alloc_cost + free_cost)
{
  let b = alloc #ctr #box x;
  free #ctr #box b;
}

let box_t
    (#ctr:ticks_t)
    (box:([@@@strictly_positive] _:Type0 -> Type0))
    {| boxes:box_class ctr box |}
    (a:Type0)
  : Type0
  = box a

let points_to
    (#ctr:ticks_t)
    (#box:([@@@strictly_positive] _:Type0 -> Type0))
    {| boxes:box_class ctr box |}
    (#a:Type0)
    (b:box_t #ctr box a)
    (v:erased a)
  : slprop
  = boxes.pts_to b v

let pulse_box ([@@@strictly_positive] a:Type0) : Type0 = B.box a

let pulse_points_to (#a:Type0) (b:pulse_box a) (v:erased a) : slprop =
  B.pts_to b v

fn pulse_read (ctr:ticks_t) (#a:Type0)
    (b:pulse_box a)
    (#v:erased a)
    (#i:erased nat)
  requires pulse_points_to b v ** MR.pts_to ctr #1.0R i
  returns u:a
  ensures pulse_points_to b v **
          MR.pts_to ctr #1.0R (i + read_cost) **
          pure (u == reveal v)
{
  rewrite (pulse_points_to b v) as (B.pts_to b v);
  let u = B.(!b);
  rewrite (B.pts_to b v) as (pulse_points_to b v);
  pay ctr read_cost;
  u
}

fn pulse_write (ctr:ticks_t) (#a:Type0)
    (b:pulse_box a)
    (u:a)
    (#v:erased a)
    (#i:erased nat)
  requires pulse_points_to b v ** MR.pts_to ctr #1.0R i
  ensures pulse_points_to b (hide u) **
          MR.pts_to ctr #1.0R (i + write_cost)
{
  rewrite (pulse_points_to b v) as (B.pts_to b v);
  B.(b := u);
  rewrite (B.pts_to b (hide u)) as (pulse_points_to b (hide u));
  pay ctr write_cost
}

fn pulse_alloc (ctr:ticks_t) (#a:Type0)
    (u:a)
    (#i:erased nat)
  requires MR.pts_to ctr #1.0R i
  returns b:pulse_box a
  ensures pulse_points_to b (hide u) **
          MR.pts_to ctr #1.0R (i + alloc_cost)
{
  let b = B.alloc #a u;
  rewrite (B.pts_to b (hide u)) as (pulse_points_to b (hide u));
  pay ctr alloc_cost;
  b
}

fn pulse_free (ctr:ticks_t) (#a:Type0)
    (b:pulse_box a)
    (#v:erased a)
    (#i:erased nat)
  requires pulse_points_to b v ** MR.pts_to ctr #1.0R i
  ensures MR.pts_to ctr #1.0R (i + free_cost)
{
  rewrite (pulse_points_to b v) as (B.pts_to b v);
  B.free b;
  pay ctr free_cost
}

instance pulse_box_class (ctr:ticks_t) : box_class ctr (fun a -> pulse_box a) =
  Pulse.Lib.Core.slprop_equivs ();
  {
    pts_to = pulse_points_to;
    read = pulse_read ctr;
    write = pulse_write ctr;
    alloc = pulse_alloc ctr;
    free = pulse_free ctr
  }
