module CLRS.Ch12.BSTArray.Delete
(**
 * Interface: Array-Based BST Delete Operations
 *
 * TREE-MINIMUM, TREE-MAXIMUM, TREE-SUCCESSOR, TREE-PREDECESSOR, TREE-DELETE
 * for the array-backed BST (CLRS §12.2–12.3).
 *)
#lang-pulse
open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq


module AP = CLRS.Ch12.BSTArray.Predicates
open CLRS.Ch12.BSTArray.Impl

(** TREE-MINIMUM (§12.2): find the minimum key in subtree *)
fn tree_minimum
  (#p: perm)
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (start_idx: SZ.t)
  requires
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      Seq.length keys_seq == A.length t.keys /\
      Seq.length valid_seq == A.length t.valid /\
      A.length t.keys == A.length t.valid /\
      SZ.v t.cap <= A.length t.keys /\
      SZ.v t.cap < 32768 /\
      SZ.v start_idx < SZ.v t.cap /\
      Seq.index valid_seq (SZ.v start_idx) == true
    )
  returns result: SZ.t
  ensures
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      SZ.v result < SZ.v t.cap /\
      SZ.v result < Seq.length valid_seq /\
      SZ.v result < Seq.length keys_seq /\
      Seq.index valid_seq (SZ.v result) == true /\
      (2 * SZ.v result + 1 >= SZ.v t.cap \/ 
       (2 * SZ.v result + 1 < Seq.length valid_seq /\
        Seq.index valid_seq (2 * SZ.v result + 1) == false)) /\
      AP.is_left_spine (SZ.v start_idx) (SZ.v result) valid_seq (SZ.v t.cap)
    )

(** TREE-MAXIMUM (§12.2): find the maximum key in subtree *)
fn tree_maximum
  (#p: perm)
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (start_idx: SZ.t)
  requires
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      Seq.length keys_seq == A.length t.keys /\
      Seq.length valid_seq == A.length t.valid /\
      A.length t.keys == A.length t.valid /\
      SZ.v t.cap <= A.length t.keys /\
      SZ.v t.cap < 32768 /\
      SZ.v start_idx < SZ.v t.cap /\
      Seq.index valid_seq (SZ.v start_idx) == true
    )
  returns result: SZ.t
  ensures
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      SZ.v result < SZ.v t.cap /\
      SZ.v result < Seq.length valid_seq /\
      Seq.index valid_seq (SZ.v result) == true /\
      (2 * SZ.v result + 2 >= SZ.v t.cap \/
       (2 * SZ.v result + 2 < Seq.length valid_seq /\
        Seq.index valid_seq (2 * SZ.v result + 2) == false))
    )

(** TREE-SUCCESSOR (§12.2): find in-order successor *)
fn tree_successor
  (#p: perm)
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (idx: SZ.t)
  requires
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      Seq.length keys_seq == A.length t.keys /\
      Seq.length valid_seq == A.length t.valid /\
      A.length t.keys == A.length t.valid /\
      SZ.v t.cap <= A.length t.keys /\
      SZ.v t.cap < 32768 /\
      SZ.v idx < SZ.v t.cap /\
      Seq.index valid_seq (SZ.v idx) == true
    )
  returns result: option SZ.t
  ensures
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      (Some? result ==> (
        SZ.v (Some?.v result) < SZ.v t.cap /\
        SZ.v (Some?.v result) < Seq.length valid_seq /\
        Seq.index valid_seq (SZ.v (Some?.v result)) == true))
    )

(** TREE-PREDECESSOR (§12.2): find in-order predecessor *)
fn tree_predecessor
  (#p: perm)
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (idx: SZ.t)
  requires
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      Seq.length keys_seq == A.length t.keys /\
      Seq.length valid_seq == A.length t.valid /\
      A.length t.keys == A.length t.valid /\
      SZ.v t.cap <= A.length t.keys /\
      SZ.v t.cap < 32768 /\
      SZ.v idx < SZ.v t.cap /\
      Seq.index valid_seq (SZ.v idx) == true
    )
  returns result: option SZ.t
  ensures
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      (Some? result ==> (
        SZ.v (Some?.v result) < SZ.v t.cap /\
        SZ.v (Some?.v result) < Seq.length valid_seq /\
        Seq.index valid_seq (SZ.v (Some?.v result)) == true))
    )

(** TREE-DELETE (§12.3): delete node at given index *)
fn tree_delete
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (del_idx: SZ.t)
  (#lo: Ghost.erased int)
  (#hi: Ghost.erased int)
  requires
    A.pts_to t.keys keys_seq **
    A.pts_to t.valid valid_seq **
    pure (
      Seq.length keys_seq == A.length t.keys /\
      Seq.length valid_seq == A.length t.valid /\
      A.length t.keys == A.length t.valid /\
      SZ.v t.cap <= A.length t.keys /\
      SZ.v t.cap < 32768 /\
      SZ.v del_idx < SZ.v t.cap /\
      Seq.index valid_seq (SZ.v del_idx) == true /\
      AP.well_formed_bst keys_seq valid_seq (SZ.v t.cap) 0 (Ghost.reveal lo) (Ghost.reveal hi)
    )
  returns success: bool
  ensures exists* keys_seq' valid_seq'.
    A.pts_to t.keys keys_seq' **
    A.pts_to t.valid valid_seq' **
    pure (
      Seq.length keys_seq' == Seq.length keys_seq /\
      Seq.length valid_seq' == Seq.length valid_seq /\
      (not success ==> Seq.equal keys_seq' keys_seq /\ Seq.equal valid_seq' valid_seq) /\
      AP.well_formed_bst keys_seq' valid_seq' (SZ.v t.cap) 0 (Ghost.reveal lo) (Ghost.reveal hi)
    )

(** TREE-DELETE-KEY (§12.3): search for key and delete if found *)
fn tree_delete_key
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (key: int)
  (#lo: Ghost.erased int)
  (#hi: Ghost.erased int)
  requires
    A.pts_to t.keys keys_seq **
    A.pts_to t.valid valid_seq **
    pure (
      Seq.length keys_seq == A.length t.keys /\
      Seq.length valid_seq == A.length t.valid /\
      A.length t.keys == A.length t.valid /\
      SZ.v t.cap <= A.length t.keys /\
      SZ.v t.cap < 32768 /\
      AP.well_formed_bst keys_seq valid_seq (SZ.v t.cap) 0 (Ghost.reveal lo) (Ghost.reveal hi)
    )
  returns success: bool
  ensures exists* keys_seq' valid_seq'.
    A.pts_to t.keys keys_seq' **
    A.pts_to t.valid valid_seq' **
    pure (
      Seq.length keys_seq' == Seq.length keys_seq /\
      Seq.length valid_seq' == Seq.length valid_seq /\
      (not success ==> Seq.equal keys_seq' keys_seq /\ Seq.equal valid_seq' valid_seq) /\
      AP.well_formed_bst keys_seq' valid_seq' (SZ.v t.cap) 0 (Ghost.reveal lo) (Ghost.reveal hi)
    )
