module CLRS.Ch12.BST
#lang-pulse
open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

open FStar.Mul

// Helper lemma to prove that child indices fit in SZ.t
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
  // Since cap < 32768 and i < cap, we have i < 32768, so i <= 32767
  // Actually i < cap < 32768, so i <= cap - 1 <= 32767 - 1 = 32766
  // Wait: if cap < 32768, then cap <= 32767
  // And i < cap, so i <= cap - 1 <= 32767 - 1 = 32766  
  // Therefore: 2 * i + 2 <= 2 * 32766 + 2 = 65534 < 65536 = pow2 16

// Array-based BST (simplified representation)
// Node i has: left at 2*i+1, right at 2*i+2
noeq
type bst = {
  keys: A.array int;
  valid: A.array bool;
  cap: SZ.t;
}

// BST property predicate (spec only)
let bst_property_at (keys: Seq.seq int) (valid: Seq.seq bool) (cap: nat) (i: nat) : prop =
  let left = op_Multiply 2 i + 1 in
  let right = op_Multiply 2 i + 2 in
  i < cap /\ cap <= Seq.length keys /\ cap <= Seq.length valid ==>
    (Seq.index valid i ==>
      (left < cap ==> (Seq.index valid left ==> Seq.index keys left < Seq.index keys i)) /\
      (right < cap ==> (Seq.index valid right ==> Seq.index keys right > Seq.index keys i)))

// Tree search
fn tree_search
  (#p: perm)
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (key: int)
  requires
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      Seq.length keys_seq == A.length t.keys /\
      Seq.length valid_seq == A.length t.valid /\
      A.length t.keys == A.length t.valid /\
      SZ.v t.cap <= A.length t.keys /\
      SZ.v t.cap < 32768
    )
  returns result: option SZ.t
  ensures
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      (Some? result ==> (
        SZ.v (Some?.v result) < Seq.length keys_seq /\
        SZ.v (Some?.v result) < Seq.length valid_seq /\
        Seq.index valid_seq (SZ.v (Some?.v result)) == true /\
        Seq.index keys_seq (SZ.v (Some?.v result)) == key))
    )
{
  let mut current : SZ.t = 0sz;
  let mut found = false;
  let mut result_idx : SZ.t = 0sz;
  
  while (
    let vc = !current;
    let vf = !found;
    SZ.lt vc t.cap && not vf
  )
  invariant exists* vc vf vr.
    R.pts_to current vc **
    R.pts_to found vf **
    R.pts_to result_idx vr **
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      SZ.v vc <= SZ.v t.cap /\
      (vf ==> (SZ.v vr < SZ.v t.cap /\
               Seq.index valid_seq (SZ.v vr) == true /\
               Seq.index keys_seq (SZ.v vr) == key))
    )
  {
    let idx = !current;
    let is_valid = t.valid.(idx);
    
    if (not is_valid) {
      current := t.cap;
    } else {
      let current_key = t.keys.(idx);
      if (current_key = key) {
        result_idx := idx;
        found := true;
      } else if (key < current_key) {
        // Left child: 2*i + 1
        child_indices_fit (SZ.v t.cap) (SZ.v idx);
        assert (pure (SZ.fits (2 * SZ.v idx + 1)));
        let two_idx = SZ.mul 2sz idx;
        let left_idx = SZ.add two_idx 1sz;
        if (SZ.gte left_idx t.cap) {
          current := t.cap;
        } else {
          current := left_idx;
        };
      } else {
        // Right child: 2*i + 2
        child_indices_fit (SZ.v t.cap) (SZ.v idx);
        assert (pure (SZ.fits (2 * SZ.v idx + 2)));
        let two_idx = SZ.mul 2sz idx;
        let right_idx = SZ.add two_idx 2sz;
        if (SZ.gte right_idx t.cap) {
          current := t.cap;
        } else {
          current := right_idx;
        };
      };
    };
  };
  
  let vf = !found;
  let vr = !result_idx;
  if vf 
  { 
    Some vr
  } 
  else 
  {
    None #SZ.t
  }
}

// Tree insert
fn tree_insert
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (key: int)
  requires
    A.pts_to t.keys keys_seq **
    A.pts_to t.valid valid_seq **
    pure (
      Seq.length keys_seq == A.length t.keys /\
      Seq.length valid_seq == A.length t.valid /\
      A.length t.keys == A.length t.valid /\
      SZ.v t.cap <= A.length t.keys /\
      SZ.v t.cap < 32768
    )
  returns success: bool
  ensures exists* keys_seq' valid_seq'.
    A.pts_to t.keys keys_seq' **
    A.pts_to t.valid valid_seq' **
    pure (
      Seq.length keys_seq' == Seq.length keys_seq /\
      Seq.length valid_seq' == Seq.length valid_seq /\
      // If successful, key exists at some valid position
      (success ==> (exists (k: nat). k < SZ.v t.cap /\ k < Seq.length keys_seq' /\ k < Seq.length valid_seq' /\
                     Seq.index keys_seq' k == key /\
                     Seq.index valid_seq' k == true)) /\
      // If not successful, arrays unchanged
      (not success ==> Seq.equal keys_seq' keys_seq /\
                       Seq.equal valid_seq' valid_seq)
    )
{
  let mut current : SZ.t = 0sz;
  let mut done = false;
  let mut success_flag = false;
  
  while (
    let vc = !current;
    let vd = !done;
    SZ.lt vc t.cap && not vd
  )
  invariant exists* vc vd vs.
    R.pts_to current vc **
    R.pts_to done vd **
    R.pts_to success_flag vs **
    (exists* ks vs'. A.pts_to t.keys ks ** A.pts_to t.valid vs' ** 
      pure (Seq.length ks == A.length t.keys /\ Seq.length vs' == A.length t.valid /\
        // If success, key is stored; if not yet done, arrays unchanged
        (vs ==> (exists (k: nat). k < SZ.v t.cap /\ k < Seq.length ks /\ k < Seq.length vs' /\
                  Seq.index ks k == key /\
                  Seq.index vs' k == true)) /\
        (not vs ==> Seq.equal ks keys_seq /\ Seq.equal vs' valid_seq)
      )) **
    pure (SZ.v vc <= SZ.v t.cap)
  {
    let idx = !current;
    
    with ks vs'. assert (A.pts_to t.keys ks ** A.pts_to t.valid vs');
    
    let is_valid = t.valid.(idx);
    
    if (not is_valid) {
      t.keys.(idx) <- key;
      t.valid.(idx) <- true;
      success_flag := true;
      done := true;
    } else {
      let current_key = t.keys.(idx);
      if (current_key = key) {
        done := true;
      } else if (key < current_key) {
        child_indices_fit (SZ.v t.cap) (SZ.v idx);
        assert (pure (SZ.fits (2 * SZ.v idx + 1)));
        let two_idx = SZ.mul 2sz idx;
        let left_idx = SZ.add two_idx 1sz;
        if (SZ.gte left_idx t.cap) {
          done := true;
        } else {
          current := left_idx;
        };
      } else {
        child_indices_fit (SZ.v t.cap) (SZ.v idx);
        assert (pure (SZ.fits (2 * SZ.v idx + 2)));
        let two_idx = SZ.mul 2sz idx;
        let right_idx = SZ.add two_idx 2sz;
        if (SZ.gte right_idx t.cap) {
          done := true;
        } else {
          current := right_idx;
        };
      };
    };
  };
  
  !success_flag
}
