/// Repro for post-loop lemma call failure in Prim's update_keys.
/// Matches the actual pattern: fn with #ghost_param, loop modifies arr,
/// loop invariant tracks that ghost_param entries are unchanged,
/// post-loop calls transfer lemma.
module ISSUE_06_post_loop_lemma_call
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open Pulse.Lib.Reference
open FStar.Mul
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

[@@"opaque_to_smt"]
let my_safe (ps ks ims: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length ps == n /\ Seq.length ks == n /\ Seq.length ims == n /\
  (forall (v:nat). v < n /\ SZ.v (Seq.index ims v) = 1 ==>
    SZ.v (Seq.index ks v) <= 50)

let my_safe_transfer (ps1 ks1 ps2 ks2 ims: Seq.seq SZ.t) (n: nat)
  : Lemma
    (requires Seq.length ps1 == n /\ Seq.length ks1 == n /\
              my_safe ps1 ks1 ims n /\
              Seq.length ps2 == n /\ Seq.length ks2 == n /\
              Seq.length ims == n /\ n > 0 /\
              (forall (v:nat). v < n /\ SZ.v (Seq.index ims v) = 1 ==>
                Seq.index ps1 v == Seq.index ps2 v /\
                Seq.index ks1 v == Seq.index ks2 v))
    (ensures my_safe ps2 ks2 ims n)
  = reveal_opaque (`%my_safe) (my_safe ps1 ks1 ims n);
    reveal_opaque (`%my_safe) (my_safe ps2 ks2 ims n)

let my_kpc (ks ps ws: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length ks == n /\ Seq.length ps == n /\ Seq.length ws == n * n

let my_kpc_step (ks ps ws: Seq.seq SZ.t) (n i: nat) (nk np: SZ.t)
  : Lemma
    (requires my_kpc ks ps ws n /\ i < n)
    (ensures my_kpc (Seq.upd ks i nk) (Seq.upd ps i np) ws n)
  = ()

/// This is the pattern from Prim's update_keys:
/// - Two arrays (key_a, parent_a) modified in a loop
/// - One array (in_mst) read-only (ghost param)
/// - Ghost params #ks0 #ps0 = original contents
/// - Loop invariant tracks: unchanged for in-MST vertices
/// - Post-loop: call my_safe_transfer with ks0, ps0, ks_final, ps_final
#push-options "--z3rlimit 400"
fn update_loop
  (#p: perm)
  (key_a: array SZ.t) (#ks0: Ghost.erased (Seq.seq SZ.t))
  (in_mst: array SZ.t) (#ims: Ghost.erased (Seq.seq SZ.t))
  (parent_a: array SZ.t) (#ps0: Ghost.erased (Seq.seq SZ.t))
  (weights: array SZ.t) (#ws: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t) (u: SZ.t)
  requires
    A.pts_to key_a ks0 ** A.pts_to in_mst #p ims **
    A.pts_to parent_a ps0 ** A.pts_to weights #p ws **
    pure (
      SZ.v n > 0 /\ SZ.v u < SZ.v n /\
      Seq.length ks0 == SZ.v n /\ Seq.length ps0 == SZ.v n /\
      Seq.length ims == SZ.v n /\ Seq.length ws == SZ.v n * SZ.v n /\
      SZ.v n * SZ.v n < pow2 64 /\ SZ.fits_u64 /\
      my_safe ps0 ks0 ims (SZ.v n) /\
      my_kpc ks0 ps0 ws (SZ.v n))
  returns _r: unit
  ensures exists* (ks1 ps1: Ghost.erased (Seq.seq SZ.t)).
    A.pts_to key_a ks1 ** A.pts_to in_mst #p ims **
    A.pts_to parent_a ps1 ** A.pts_to weights #p ws **
    pure (
      SZ.v n > 0 /\
      Seq.length ks1 == SZ.v n /\ Seq.length ps1 == SZ.v n /\
      my_kpc ks1 ps1 ws (SZ.v n) /\
      my_safe ps1 ks1 ims (SZ.v n))
{
  let mut i: SZ.t = 0sz;
  while (let vi = !i; vi <^ n)
  invariant exists* vi ks ps.
    R.pts_to i vi **
    A.pts_to key_a ks ** A.pts_to in_mst #p ims **
    A.pts_to parent_a ps ** A.pts_to weights #p ws **
    pure (
      SZ.v vi <= SZ.v n /\ SZ.v u < SZ.v n /\ SZ.v n > 0 /\
      Seq.length ks == SZ.v n /\ Seq.length ps == SZ.v n /\
      Seq.length ims == SZ.v n /\ Seq.length ws == SZ.v n * SZ.v n /\
      SZ.v n * SZ.v n < pow2 64 /\ SZ.fits_u64 /\
      my_kpc ks ps ws (SZ.v n) /\
      // Pass-through: original my_safe + lengths
      my_safe ps0 ks0 ims (SZ.v n) /\
      Seq.length ks0 == SZ.v n /\ Seq.length ps0 == SZ.v n /\
      // In-MST entries unchanged
      (forall (v:nat). v < SZ.v n /\ SZ.v (Seq.index ims v) = 1 ==>
        Seq.index ps0 v == Seq.index ps v /\ Seq.index ks0 v == Seq.index ks v))
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    let in_mst_v = A.op_Array_Access in_mst vi;
    let key_v = A.op_Array_Access key_a vi;
    let old_p = A.op_Array_Access parent_a vi;
    let should_update = (in_mst_v = 0sz);
    let new_k : SZ.t = (if should_update then 42sz else key_v);
    let new_p : SZ.t = (if should_update then u else old_p);
    with ks ps. assert (A.pts_to key_a ks ** A.pts_to parent_a ps);
    my_kpc_step ks ps ws (SZ.v n) (SZ.v vi) new_k new_p;
    A.op_Array_Assignment key_a vi new_k;
    A.op_Array_Assignment parent_a vi new_p;
    i := vi +^ 1sz;
  };
  // Post-loop: transfer my_safe from old to new sequences
  with ks_f ps_f. assert (A.pts_to key_a ks_f ** A.pts_to parent_a ps_f);
  my_safe_transfer ps0 ks0 ps_f ks_f ims (SZ.v n)
}
#pop-options
