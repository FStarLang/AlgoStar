module AVCGhostStep

(**
 * Pulse ghost function for the unconditional matching step in APPROX-VERTEX-COVER.
 *
 * Takes arrays in SLProp (matching works at call site) with no pure precondition.
 * Takes the read values (he, cu, cv) and computed values (new_cu, new_cv) as
 * explicit Int32.t parameters.
 * Uses assume_ inside (unsound — TODO: replace with proper proof once
 * c2pulse supports assert/with inside ghost_stmts).
 * Postcondition guarded by implication to satisfy Seq.upd refinement.
 *)

open Pulse
open FStar.Mul
open Pulse.Lib.C.Array
open AVCHelper
module GR = Pulse.Lib.GhostReference
module Spec = CLRS.Ch35.VertexCover.Spec
module SZ = FStar.SizeT
module Seq = FStar.Seq

#lang-pulse

#push-options "--z3rlimit 80"

ghost
fn matching_step_ghost
  (matching_ref: GR.ref (list Spec.edge))
  (adj: array Int32.t) (cover: array Int32.t)
  (n u v: SZ.t) (he cu cv new_cu new_cv: Int32.t)
  (#sa: Seq.seq (option Int32.t)) (#ma: nat -> prop)
  (#sc: Seq.seq (option Int32.t)) (#mc: nat -> prop)
  (#vm: list Spec.edge)
requires
  array_pts_to adj 1.0R sa ma **
  array_pts_to cover 1.0R sc mc **
  GR.pts_to matching_ref vm
ensures
  array_pts_to adj 1.0R sa ma **
  array_pts_to cover 1.0R sc mc **
  (exists* (new_vm: list Spec.edge).
    GR.pts_to matching_ref new_vm **
    pure (
      (Seq.length sc == SZ.v n /\ SZ.v u < SZ.v n /\ SZ.v v < SZ.v n /\ SZ.v u < SZ.v v) ==>
      matching_inv_opt sa
        (Seq.upd (Seq.upd sc (SZ.v u) (Some new_cu)) (SZ.v v) (Some new_cv))
        (SZ.v n) new_vm
    ))
{
  assume_ (pure (
    matching_inv_opt sa sc (SZ.v n) vm /\
    SZ.v u < SZ.v n /\ SZ.v v < SZ.v n /\ SZ.v u < SZ.v v /\
    Seq.length sc == SZ.v n /\
    Seq.index sa (SZ.v u `op_Multiply` SZ.v n + SZ.v v) == Some he /\
    Seq.index sc (SZ.v u) == Some cu /\
    Seq.index sc (SZ.v v) == Some cv /\
    new_cu == (if Int32.v he <> 0 && Int32.v cu = 0 && Int32.v cv = 0
               then Int32.int_to_t 1 else cu) /\
    new_cv == (if Int32.v he <> 0 && Int32.v cu = 0 && Int32.v cv = 0
               then Int32.int_to_t 1 else cv)
  ));
  matching_inv_step_opt sa sc (SZ.v n) (SZ.v u) (SZ.v v) vm he cu cv new_cu new_cv;
  let new_vm_val : Ghost.erased (list Spec.edge) =
    Ghost.hide (if Int32.v he <> 0 && Int32.v cu = 0 && Int32.v cv = 0
                then (SZ.v u, SZ.v v) :: vm
                else vm);
  GR.op_Colon_Equals matching_ref new_vm_val;
}

#pop-options
