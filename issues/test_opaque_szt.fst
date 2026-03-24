module Test_opaque_szt
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

[@@"opaque_to_smt"]
let my_pred (ks ws: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length ks == n /\ Seq.length ws == n * n

fn test_fn
    (#p: perm)
    (key_a weights: A.array SZ.t)
    (#ws: Ghost.erased (Seq.seq SZ.t))
    (n: SZ.t)
  requires exists* ks.
    A.pts_to key_a ks **
    A.pts_to weights #p ws **
    pure (SZ.v n > 0 /\ Seq.length ks == SZ.v n /\
          Seq.length ws == SZ.v n * SZ.v n /\
          my_pred ks ws (SZ.v n))
  returns _: unit
  ensures exists* ks'.
    A.pts_to key_a ks' **
    A.pts_to weights #p ws **
    pure (Seq.length ks' == SZ.v n /\
          my_pred ks' ws (SZ.v n))
{
  with ks0. assert (A.pts_to key_a ks0);
  let v = A.op_Array_Access key_a 0sz;
  A.op_Array_Assignment key_a 0sz v;
}
