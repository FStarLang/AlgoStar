module CLRS.Common.Complexity.LinearSorting.Class
#lang-pulse

open Pulse

module A = Pulse.Lib.Array
module MR = Pulse.Lib.MonotonicGhostRef
module Seq = FStar.Seq
module SZ = FStar.SizeT
module SeqP = FStar.Seq.Properties

let preorder_nat : FStar.Preorder.preorder nat = fun (x y:nat) -> b2t (x <= y)

let ticks_t = MR.mref #nat preorder_nat

let sorted_by (#a:Type) (key:a -> GTot nat) (s:Seq.seq a) : prop =
  forall (i j:nat). {:pattern (Seq.index s i); (Seq.index s j)}
    i <= j /\ j < Seq.length s ==> key (Seq.index s i) <= key (Seq.index s j)

let in_key_range (#a:Type) (key:a -> GTot nat) (s:Seq.seq a) (k:nat) : prop =
  forall (i:nat). i < Seq.length s ==> key (Seq.index s i) <= k

let fits_in_digits (#a:Type) (value:a -> GTot nat) (pow:nat -> nat -> GTot nat)
  (s:Seq.seq a) (base digits:nat) : prop =
  forall (i:nat). i < Seq.length s ==> value (Seq.index s i) < pow base digits

let stable_by_digit (#a:eqtype) (digit:a -> nat -> nat -> GTot nat)
  (s_in s_out:Seq.seq a) (d base:nat) : prop =
  base > 0 /\
  SeqP.permutation a s_in s_out /\
  (forall (i j:nat). {:pattern (Seq.index s_out i); (Seq.index s_out j)}
    i <= j /\ j < Seq.length s_out ==>
      digit (Seq.index s_out i) d base <= digit (Seq.index s_out j) d base) /\
  (forall (j1 j2:nat). {:pattern (Seq.index s_out j1); (Seq.index s_out j2)}
    j1 < j2 /\ j2 < Seq.length s_out /\
    digit (Seq.index s_out j1) d base == digit (Seq.index s_out j2) d base /\
    Seq.index s_out j1 <> Seq.index s_out j2 ==>
    (exists (i1 i2:nat). i1 < i2 /\ i2 < Seq.length s_in /\
      Seq.index s_in i1 == Seq.index s_out j1 /\
      Seq.index s_in i2 == Seq.index s_out j2))

let instrumented_key (a:Type) (key:a -> GTot nat) (ctr:ticks_t) =
  fn (x:a) (#i:erased nat)
  requires MR.pts_to ctr #1.0R i
  returns k:nat
  ensures MR.pts_to ctr #1.0R (i + 1)
  ensures pure (k == key x)

let instrumented_digit (a:Type) (digit:a -> nat -> nat -> GTot nat) (ctr:ticks_t) =
  fn (x:a) (d:nat) (base:nat) (#i:erased nat)
  requires MR.pts_to ctr #1.0R i
  returns k:nat
  ensures MR.pts_to ctr #1.0R (i + 1)
  ensures pure (k == digit x d base)

ghost
fn pay (ctr:ticks_t) (work:nat) (#i:erased nat)
  requires MR.pts_to ctr #1.0R i
  ensures MR.pts_to ctr #1.0R (i + work)
{
  MR.update ctr (i + work)
}

let counting_sort_bound (n k:nat) : nat = 2 * n + k + 1
let digit_counting_sort_bound (n base:nat) : nat = 2 * n + base
let radix_sort_bound (n base digits:nat) : nat =
  digits * (digit_counting_sort_bound n base + n)

class array_counting_sort (a:eqtype) (key:a -> GTot nat) (f:nat -> nat -> nat) = {
  sort:
    (fn (input:A.array a)
        (output:A.array a)
        (len:SZ.t)
        (max_key:SZ.t)
        (ctr:ticks_t)
        (ikey:instrumented_key a key ctr)
        (#s:erased (Seq.seq a))
        (#out0:erased (Seq.seq a))
        (#i:erased nat)
      requires
        A.pts_to input #0.5R s **
        A.pts_to output out0 **
        MR.pts_to ctr #1.0R i **
        pure (
          SZ.v len <= A.length input /\
          SZ.v len <= A.length output /\
          SZ.v len == Seq.length s /\
          SZ.v len == Seq.length out0 /\
          Seq.length s == A.length input /\
          Seq.length out0 == A.length output /\
          in_key_range key s (SZ.v max_key) /\
          SZ.fits (SZ.v max_key + 2) /\
          SZ.fits (SZ.v len + SZ.v max_key + 2))
      ensures exists* out' ticks.
        A.pts_to input #0.5R s **
        A.pts_to output out' **
        MR.pts_to ctr #1.0R ticks **
        pure (
          Seq.length out' == Seq.length s /\
          sorted_by key out' /\
          SeqP.permutation a s out' /\
          in_key_range key out' (SZ.v max_key) /\
          ticks <= i + f (Seq.length s) (SZ.v max_key)));
}

class array_inplace_counting_sort (a:eqtype) (key:a -> GTot nat) (f:nat -> nat -> nat) = {
  sort_inplace:
    (fn (arr:A.array a)
        (len:SZ.t)
        (max_key:SZ.t)
        (ctr:ticks_t)
        (ikey:instrumented_key a key ctr)
        (#s:erased (Seq.seq a))
        (#i:erased nat)
      requires
        A.pts_to arr s **
        MR.pts_to ctr #1.0R i **
        pure (
          SZ.v len <= A.length arr /\
          SZ.v len == Seq.length s /\
          Seq.length s == A.length arr /\
          in_key_range key s (SZ.v max_key) /\
          SZ.fits (SZ.v max_key + 2) /\
          SZ.fits (SZ.v len + SZ.v max_key + 2))
      ensures exists* s' ticks.
        A.pts_to arr s' **
        MR.pts_to ctr #1.0R ticks **
        pure (
          Seq.length s' == Seq.length s /\
          sorted_by key s' /\
          SeqP.permutation a s s' /\
          in_key_range key s' (SZ.v max_key) /\
          ticks <= i + f (Seq.length s) (SZ.v max_key)));
}

class array_digit_counting_sort (a:eqtype) (digit:a -> nat -> nat -> GTot nat)
  (f:nat -> nat -> nat) = {
  sort_by_digit:
    (fn (input:A.array a)
        (output:A.array a)
        (len:SZ.t)
        (base:SZ.t)
        (d:nat)
        (ctr:ticks_t)
        (idigit:instrumented_digit a digit ctr)
        (#s:erased (Seq.seq a))
        (#out0:erased (Seq.seq a))
        (#i:erased nat)
      requires
        A.pts_to input #0.5R s **
        A.pts_to output out0 **
        MR.pts_to ctr #1.0R i **
        pure (
          SZ.v len <= A.length input /\
          SZ.v len <= A.length output /\
          SZ.v len == Seq.length s /\
          SZ.v len == Seq.length out0 /\
          Seq.length s == A.length input /\
          Seq.length out0 == A.length output /\
          SZ.v base >= 2 /\
          SZ.fits (SZ.v base + 2) /\
          SZ.fits (SZ.v len + SZ.v base + 2))
      ensures exists* out' ticks.
        A.pts_to input #0.5R s **
        A.pts_to output out' **
        MR.pts_to ctr #1.0R ticks **
        pure (
          Seq.length out' == Seq.length s /\
          stable_by_digit digit s out' d (SZ.v base) /\
          ticks <= i + f (Seq.length s) (SZ.v base)));
}

class array_radix_sort (a:eqtype)
  (value:a -> GTot nat)
  (digit:a -> nat -> nat -> GTot nat)
  (pow:nat -> nat -> GTot nat)
  (f:nat -> nat -> nat -> nat) = {
  radix_sort:
    (fn (arr:A.array a)
        (len:SZ.t)
        (base:SZ.t)
        (digits:SZ.t)
        (ctr:ticks_t)
        (idigit:instrumented_digit a digit ctr)
        (#s:erased (Seq.seq a))
        (#i:erased nat)
      requires
        A.pts_to arr s **
        MR.pts_to ctr #1.0R i **
        pure (
          SZ.v len <= A.length arr /\
          SZ.v len == Seq.length s /\
          Seq.length s == A.length arr /\
          SZ.v base >= 2 /\
          SZ.v digits > 0 /\
          fits_in_digits value pow s (SZ.v base) (SZ.v digits) /\
          SZ.fits (SZ.v base + 2) /\
          SZ.fits (SZ.v len + SZ.v base + 2))
      ensures exists* s' ticks.
        A.pts_to arr s' **
        MR.pts_to ctr #1.0R ticks **
        pure (
          Seq.length s' == Seq.length s /\
          sorted_by value s' /\
          SeqP.permutation a s s' /\
          ticks <= i + f (Seq.length s) (SZ.v base) (SZ.v digits)));
}
