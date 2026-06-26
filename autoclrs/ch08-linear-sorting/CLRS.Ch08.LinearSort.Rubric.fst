(*
   CLRS Chapter 8: linear sorting as instances of a shared complexity rubric.

   Counting sort and radix sort are not comparison sorts, so the common
   comparison-based array_sort class is the wrong abstraction.  This module
   exposes the existing nat implementations through the linear-sort classes,
   whose costs are stated in terms of bounded key and digit domains.
*)
module CLRS.Ch08.LinearSort.Rubric
#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module B = CLRS.Ch08.RadixSort.Base
module Bridge = CLRS.Ch08.RadixSort.Bridge
module Impl = CLRS.Ch08.CountingSort.Impl
module LC = CLRS.Common.Complexity.LinearSorting.Class
module MR = Pulse.Lib.MonotonicGhostRef
module Radix = CLRS.Ch08.RadixSort
module S = CLRS.Ch08.CountingSort.Spec
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SZ = FStar.SizeT
module Stab = CLRS.Ch08.RadixSort.Stability

let nat_key (x:nat) : GTot nat = x
let nat_digit (x:nat) (d:nat) (base:nat) : GTot nat = B.digit x d base
let nat_pow (base:nat) (digits:nat) : GTot nat = B.pow base digits

let sorted_to_lc (s:Seq.seq nat)
  : Lemma (requires S.sorted s)
          (ensures LC.sorted_by nat_key s)
  = ()

let in_range_to_lc (s:Seq.seq nat) (k:nat)
  : Lemma (requires S.in_range s k)
          (ensures LC.in_key_range nat_key s k)
  = ()

let permutation_to_lc (s0 s1:Seq.seq nat)
  : Lemma (requires S.permutation s0 s1)
          (ensures SeqP.permutation nat s0 s1)
  = reveal_opaque (`%S.permutation) (S.permutation s0 s1)

let fits_digits_to_lc (s:Seq.seq nat) (base digits:nat)
  : Lemma
    (requires forall (i:nat). i < Seq.length s ==> Seq.index s i < B.pow base digits)
    (ensures LC.fits_in_digits nat_key nat_pow s base digits)
  = ()

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let sorted_on_digit_to_lc (s:Seq.seq nat) (d base:nat)
  : Lemma (requires base > 0 /\ B.sorted_on_digit s d base)
          (ensures forall (i j:nat). i <= j /\ j < Seq.length s ==>
            nat_digit (Seq.index s i) d base <= nat_digit (Seq.index s j) d base)
  = let aux (i:nat) (j:nat)
      : Lemma (ensures i <= j /\ j < Seq.length s ==>
          nat_digit (Seq.index s i) d base <= nat_digit (Seq.index s j) d base)
      = if i <= j && j < Seq.length s then
          if i = j then ()
          else Stab.sorted_on_digit_at s d base i j
    in
    FStar.Classical.forall_intro_2 aux
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let stable_on_digit_to_lc (s_in s_out:Seq.seq nat) (d base:nat)
  : Lemma (requires base > 0 /\ Stab.is_stable_sort_on_digit s_in s_out d base)
          (ensures LC.stable_by_digit nat_digit s_in s_out d base)
  = Stab.is_stable_get_perm s_in s_out d base;
    Bridge.base_perm_implies_seqp_perm s_in s_out;
    Stab.is_stable_get_sorted s_in s_out d base;
    sorted_on_digit_to_lc s_out d base;
    let order_proof (j1:nat) (j2:nat)
      : Lemma (j1 < j2 /\ j2 < Seq.length s_out /\
               nat_digit (Seq.index s_out j1) d base == nat_digit (Seq.index s_out j2) d base /\
               Seq.index s_out j1 <> Seq.index s_out j2 ==>
               (exists (i1 i2:nat). i1 < i2 /\ i2 < Seq.length s_in /\
                 Seq.index s_in i1 == Seq.index s_out j1 /\
                 Seq.index s_in i2 == Seq.index s_out j2))
      = if j1 < j2 && j2 < Seq.length s_out &&
           nat_digit (Seq.index s_out j1) d base == nat_digit (Seq.index s_out j2) d base &&
           Seq.index s_out j1 <> Seq.index s_out j2
        then Stab.is_stable_get_witnesses s_in s_out d base j1 j2
    in
    FStar.Classical.forall_intro_2 order_proof;
    assert (LC.stable_by_digit nat_digit s_in s_out d base)
#pop-options

fn counting_sort_sort
  (input:A.array nat)
  (output:A.array nat)
  (len:SZ.t)
  (max_key:SZ.t)
  (ctr:LC.ticks_t)
  (ikey:LC.instrumented_key nat nat_key ctr)
  (#s:erased (Seq.seq nat))
  (#out0:erased (Seq.seq nat))
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
    LC.in_key_range nat_key s (SZ.v max_key) /\
    SZ.fits (SZ.v max_key + 2) /\
    SZ.fits (SZ.v len + SZ.v max_key + 2))
ensures exists* out' ticks.
  A.pts_to input #0.5R s **
  A.pts_to output out' **
  MR.pts_to ctr #1.0R ticks **
  pure (
    Seq.length out' == Seq.length s /\
    LC.sorted_by nat_key out' /\
    SeqP.permutation nat s out' /\
    LC.in_key_range nat_key out' (SZ.v max_key) /\
    ticks <= reveal i + LC.counting_sort_bound (Seq.length s) (SZ.v max_key))
{
  Impl.counting_sort_impl_tracked input output len max_key ctr;
  with out' ticks. assert (A.pts_to output out' ** MR.pts_to ctr #1.0R ticks);
  sorted_to_lc out';
  permutation_to_lc s out';
  in_range_to_lc out' (SZ.v max_key);
  ()
}

fn counting_sort_inplace_sort
  (arr:A.array nat)
  (len:SZ.t)
  (max_key:SZ.t)
  (ctr:LC.ticks_t)
  (ikey:LC.instrumented_key nat nat_key ctr)
  (#s:erased (Seq.seq nat))
  (#i:erased nat)
requires
  A.pts_to arr s **
  MR.pts_to ctr #1.0R i **
  pure (
    SZ.v len <= A.length arr /\
    SZ.v len == Seq.length s /\
    Seq.length s == A.length arr /\
    LC.in_key_range nat_key s (SZ.v max_key) /\
    SZ.fits (SZ.v max_key + 2) /\
    SZ.fits (SZ.v len + SZ.v max_key + 2))
ensures exists* s' ticks.
  A.pts_to arr s' **
  MR.pts_to ctr #1.0R ticks **
  pure (
    Seq.length s' == Seq.length s /\
    LC.sorted_by nat_key s' /\
    SeqP.permutation nat s s' /\
    LC.in_key_range nat_key s' (SZ.v max_key) /\
    ticks <= reveal i + LC.counting_sort_bound (Seq.length s) (SZ.v max_key))
{
  Impl.counting_sort_inplace_tracked arr len max_key ctr;
  with s' ticks. assert (A.pts_to arr s' ** MR.pts_to ctr #1.0R ticks);
  sorted_to_lc s';
  permutation_to_lc s s';
  in_range_to_lc s' (SZ.v max_key);
  ()
}

fn counting_sort_by_digit_sort
  (input:A.array nat)
  (output:A.array nat)
  (len:SZ.t)
  (base:SZ.t)
  (d:nat)
  (ctr:LC.ticks_t)
  (idigit:LC.instrumented_digit nat nat_digit ctr)
  (#s:erased (Seq.seq nat))
  (#out0:erased (Seq.seq nat))
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
    LC.stable_by_digit nat_digit s out' d (SZ.v base) /\
    ticks <= reveal i + LC.digit_counting_sort_bound (Seq.length s) (SZ.v base))
{
  Impl.counting_sort_by_digit_tracked input output len base d ctr;
  with out' ticks. assert (A.pts_to output out' ** MR.pts_to ctr #1.0R ticks);
  stable_on_digit_to_lc s out' d (SZ.v base);
  ()
}

fn radix_sort_sort
  (arr:A.array nat)
  (len:SZ.t)
  (base:SZ.t)
  (digits:SZ.t)
  (ctr:LC.ticks_t)
  (idigit:LC.instrumented_digit nat nat_digit ctr)
  (#s:erased (Seq.seq nat))
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
    LC.fits_in_digits nat_key nat_pow s (SZ.v base) (SZ.v digits) /\
    SZ.fits (SZ.v base + 2) /\
    SZ.fits (SZ.v len + SZ.v base + 2))
ensures exists* s' ticks.
  A.pts_to arr s' **
  MR.pts_to ctr #1.0R ticks **
  pure (
    Seq.length s' == Seq.length s /\
    LC.sorted_by nat_key s' /\
    SeqP.permutation nat s s' /\
    ticks <= reveal i + LC.radix_sort_bound (Seq.length s) (SZ.v base) (SZ.v digits))
{
  Radix.radix_sort_multidigit_tracked arr len base digits ctr;
  with s' ticks. assert (A.pts_to arr s' ** MR.pts_to ctr #1.0R ticks);
  sorted_to_lc s';
  permutation_to_lc s s';
  ()
}

instance counting_sort_array_sort :
  LC.array_counting_sort nat nat_key LC.counting_sort_bound =
{
  sort = counting_sort_sort;
}

instance counting_sort_inplace_array_sort :
  LC.array_inplace_counting_sort nat nat_key LC.counting_sort_bound =
{
  sort_inplace = counting_sort_inplace_sort;
}

instance digit_counting_sort_array_sort :
  LC.array_digit_counting_sort nat nat_digit LC.digit_counting_sort_bound =
{
  sort_by_digit = counting_sort_by_digit_sort;
}

instance radix_sort_array_sort :
  LC.array_radix_sort nat nat_key nat_digit nat_pow LC.radix_sort_bound =
{
  radix_sort = radix_sort_sort;
}
