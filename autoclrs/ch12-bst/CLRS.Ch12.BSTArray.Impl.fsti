module CLRS.Ch12.BSTArray.Impl
(**
 * Interface: Array-Based Binary Search Tree (Pulse Implementation)
 *
 * Public types and operation signatures for the array-backed BST.
 * Node at index i has left child at 2*i+1, right child at 2*i+2.
 *
 * Each operation's postcondition links to the shared predicates
 * in CLRS.Ch12.BSTArray.Predicates and the pure spec in
 * CLRS.Ch12.BSTArray.Spec.
 *
 * CLRS Reference: §12.1–12.3
 *)
#lang-pulse
open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module C = FStar.Classical

open FStar.Mul
open FStar.List.Tot
open CLRS.Ch12.BSTArray.Complexity
module AP = CLRS.Ch12.BSTArray.Predicates

// ============================================================
// Helper lemma: child indices fit in SZ.t
// ============================================================

let child_indices_fit (cap: nat) (i: nat)
  : Lemma
    (requires cap < 32768 /\ i < cap)
    (ensures (
      let left = 2 * i + 1 in
      let right = 2 * i + 2 in
      0 <= left /\ left < pow2 16 /\
      0 <= right /\ right < pow2 16
    ))
= ()

// ============================================================
// Array-based BST type
// ============================================================

noeq
type bst = {
  keys: A.array int;
  valid: A.array bool;
  cap: SZ.t;
}

// ============================================================
// Locally-defined predicates (duplicated from Predicates for
// Pulse import compatibility)
// ============================================================

let rec subtree_in_range 
  (keys: Seq.seq int) 
  (valid: Seq.seq bool) 
  (cap: nat) 
  (i: nat) 
  (lo hi: int)
  : Tot prop (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= Seq.length keys || i >= Seq.length valid then True
    else if not (Seq.index valid i) then True
    else 
      let k = Seq.index keys i in
      let left = op_Multiply 2 i + 1 in
      let right = op_Multiply 2 i + 2 in
      lo < k /\ k < hi /\
      subtree_in_range keys valid cap left lo k /\
      subtree_in_range keys valid cap right k hi

let rec key_in_subtree 
  (keys: Seq.seq int) 
  (valid: Seq.seq bool) 
  (cap: nat) 
  (i: nat) 
  (key: int)
  : Tot prop (decreases (if i < cap then cap - i else 0))
  = i < cap /\ i < Seq.length keys /\ i < Seq.length valid /\
    Seq.index valid i /\
    (Seq.index keys i == key \/
     key_in_subtree keys valid cap (op_Multiply 2 i + 1) key \/
     key_in_subtree keys valid cap (op_Multiply 2 i + 2) key)

// ============================================================
// Public Operations
// ============================================================

(** TREE-SEARCH (§12.2): iterative BST search with O(h) ghost ticks
    Postcondition: ticks bounded by tree_height(cap) *)
fn tree_search
  (#p: perm)
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (#lo: Ghost.erased int)
  (#hi: Ghost.erased int)
  (key: int)
  (ticks: GR.ref nat)
  requires
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    GR.pts_to ticks 'n **
    pure (
      Seq.length keys_seq == A.length t.keys /\
      Seq.length valid_seq == A.length t.valid /\
      A.length t.keys == A.length t.valid /\
      SZ.v t.cap <= A.length t.keys /\
      SZ.v t.cap < 32768 /\
      subtree_in_range keys_seq valid_seq (SZ.v t.cap) 0 lo hi
    )
  returns result: option SZ.t
  ensures exists* vticks.
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    GR.pts_to ticks vticks **
    pure (
      vticks >= 'n /\
      (SZ.v t.cap > 0 ==> vticks - 'n <= tree_height (SZ.v t.cap)) /\
      (Some? result ==> (
        SZ.v (Some?.v result) < Seq.length keys_seq /\
        SZ.v (Some?.v result) < Seq.length valid_seq /\
        Seq.index valid_seq (SZ.v (Some?.v result)) == true /\
        Seq.index keys_seq (SZ.v (Some?.v result)) == key)) /\
      (None? result ==> ~(key_in_subtree keys_seq valid_seq (SZ.v t.cap) 0 key))
    )

(** TREE-INSERT (§12.3): iterative BST insert, well_formed_bst pre/post
    Postcondition: ticks bounded by tree_height(cap) *)
fn tree_insert
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (key: int)
  (#lo: Ghost.erased int)
  (#hi: Ghost.erased int)
  (ticks: GR.ref nat)
  requires
    A.pts_to t.keys keys_seq **
    A.pts_to t.valid valid_seq **
    GR.pts_to ticks 'n **
    pure (
      Seq.length keys_seq == A.length t.keys /\
      Seq.length valid_seq == A.length t.valid /\
      A.length t.keys == A.length t.valid /\
      SZ.v t.cap <= A.length t.keys /\
      SZ.v t.cap < 32768 /\
      AP.well_formed_bst keys_seq valid_seq (SZ.v t.cap) 0 (Ghost.reveal lo) (Ghost.reveal hi) /\
      Ghost.reveal lo < key /\ key < Ghost.reveal hi
    )
  returns success: bool
  ensures exists* keys_seq' valid_seq' vticks.
    A.pts_to t.keys keys_seq' **
    A.pts_to t.valid valid_seq' **
    GR.pts_to ticks vticks **
    pure (
      vticks >= 'n /\
      (SZ.v t.cap > 0 ==> vticks - 'n <= tree_height (SZ.v t.cap)) /\
      Seq.length keys_seq' == Seq.length keys_seq /\
      Seq.length valid_seq' == Seq.length valid_seq /\
      (not success ==> Seq.equal keys_seq' keys_seq /\
                       Seq.equal valid_seq' valid_seq) /\
      (success ==> (exists (idx: nat). idx < SZ.v t.cap /\
                    idx < Seq.length keys_seq' /\
                    idx < Seq.length valid_seq' /\
                    Seq.index keys_seq' idx == key /\
                    Seq.index valid_seq' idx == true)) /\
      (success ==> key_in_subtree keys_seq' valid_seq' (SZ.v t.cap) 0 key) /\
      AP.well_formed_bst keys_seq' valid_seq' (SZ.v t.cap) 0 (Ghost.reveal lo) (Ghost.reveal hi)
    )

(** INORDER-WALK (§12.1): recursive inorder traversal *)
fn inorder_walk
  (#p: perm)
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (output: A.array int)
  (#out_seq: Ghost.erased (Seq.seq int))
  (write_pos: R.ref SZ.t)
  (#wp0: Ghost.erased SZ.t)
  (out_len: SZ.t)
  requires
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    A.pts_to output out_seq **
    R.pts_to write_pos wp0 **
    pure (
      Seq.length keys_seq == A.length t.keys /\
      Seq.length valid_seq == A.length t.valid /\
      A.length t.keys == A.length t.valid /\
      SZ.v t.cap <= A.length t.keys /\
      SZ.v t.cap < 32768 /\
      SZ.v out_len == A.length output /\
      Seq.length out_seq == A.length output /\
      SZ.v wp0 <= SZ.v out_len
    )
  ensures
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    (exists* out_seq' wp'.
      A.pts_to output out_seq' **
      R.pts_to write_pos wp' **
      pure (
        Seq.length out_seq' == A.length output /\
        SZ.v wp' <= SZ.v out_len
      ))

// ============================================================
// Bridge lemmas
//
// Convert between AP.well_formed_bst (from tree_insert postcondition)
// and local subtree_in_range (for tree_search precondition).
// Eliminates the need for client-side bridge lemmas.
// ============================================================

val wfb_to_sir
  (keys: Seq.seq int) (valid: Seq.seq bool)
  (cap: nat) (i: nat) (lo hi: int)
  : Lemma
    (requires AP.well_formed_bst keys valid cap i lo hi)
    (ensures subtree_in_range keys valid cap i lo hi)
