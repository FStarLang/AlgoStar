module CLRS.Ch12.BST
#lang-pulse
open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module C = FStar.Classical

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

// Stronger BST property: all keys in subtree are bounded by lo and hi
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

// Key membership in subtree rooted at i
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

// Lemma: If key is in a bounded subtree, it must be within the bounds
let rec lemma_key_in_bounded_subtree
  (keys: Seq.seq int)
  (valid: Seq.seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma 
    (requires subtree_in_range keys valid cap i lo hi /\ key_in_subtree keys valid cap i key)
    (ensures lo < key /\ key < hi)
    (decreases (if i < cap then cap - i else 0))
  = let left = op_Multiply 2 i + 1 in
    let right = op_Multiply 2 i + 2 in
    // key_in_subtree establishes i < cap /\ valid[i]
    // subtree_in_range establishes lo < keys[i] < hi
    // Case 1: key == keys[i], then lo < key < hi directly
    // Case 2: key in left subtree, recurse
    // Case 3: key in right subtree, recurse
    C.or_elim
      #(key_in_subtree keys valid cap left key)
      #(key_in_subtree keys valid cap right key)
      #(fun _ -> lo < key /\ key < hi)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap left lo (Seq.index keys i) key)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap right (Seq.index keys i) hi key)

// Lemma: If key < current_key and BST property holds, key can only be in left subtree
[@@"opaque_to_smt"]
let lemma_key_not_in_right_if_less
  (keys: Seq.seq int)
  (valid: Seq.seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma
    (requires 
      subtree_in_range keys valid cap i lo hi /\
      i < cap /\ i < Seq.length keys /\ i < Seq.length valid /\
      Seq.index valid i /\
      key < Seq.index keys i /\
      key_in_subtree keys valid cap i key)
    (ensures key_in_subtree keys valid cap (op_Multiply 2 i + 1) key)
  = let k = Seq.index keys i in
    let right = op_Multiply 2 i + 2 in
    // key != k since key < k
    // If key were in right subtree, then k < key < hi by lemma_key_in_bounded_subtree
    // But this contradicts key < k
    // By definition of key_in_subtree: key == k \/ in left \/ in right
    // key != k, so: in left \/ in right
    // Prove ~(in right) by contradiction, so must be in left
    C.or_elim
      #(key_in_subtree keys valid cap right key)
      #(~(key_in_subtree keys valid cap right key))
      #(fun _ -> key_in_subtree keys valid cap (op_Multiply 2 i + 1) key)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap right k hi key) // derives False from key < k /\ k < key
      (fun _ -> ())

// Lemma: If key > current_key and BST property holds, key can only be in right subtree  
[@@"opaque_to_smt"]
let lemma_key_not_in_left_if_greater
  (keys: Seq.seq int)
  (valid: Seq.seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma
    (requires 
      subtree_in_range keys valid cap i lo hi /\
      i < cap /\ i < Seq.length keys /\ i < Seq.length valid /\
      Seq.index valid i /\
      key > Seq.index keys i /\
      key_in_subtree keys valid cap i key)
    (ensures key_in_subtree keys valid cap (op_Multiply 2 i + 2) key)
  = let k = Seq.index keys i in
    let left = op_Multiply 2 i + 1 in
    // key != k since key > k
    // If key were in left subtree, then lo < key < k by lemma_key_in_bounded_subtree
    // But this contradicts key > k
    C.or_elim
      #(key_in_subtree keys valid cap left key)
      #(~(key_in_subtree keys valid cap left key))
      #(fun _ -> key_in_subtree keys valid cap (op_Multiply 2 i + 2) key)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap left lo k key) // derives False from key > k /\ key < k
      (fun _ -> ())


// NOTE: Several lemmas with admits were removed as they were unused and required
// additional reachability predicates or BST property in preconditions to prove.
// These included:
// - lemma_reachable_implies_subtree_in_range
// - lemma_search_left_simple  
// - lemma_search_right_simple
// - lemma_insert_at_invalid_adds_key
// If needed in the future when BST invariants are added, they can be restored from git history.

// Lemma: If a node is invalid, no key can be in its subtree
let lemma_invalid_node_empty
  (keys: Seq.seq int)
  (valid: Seq.seq bool)
  (cap: nat)
  (i: nat)
  (k: int)
  : Lemma
    (requires
      i < cap /\ i < Seq.length keys /\ i < Seq.length valid /\
      ~(Seq.index valid i))
    (ensures ~(key_in_subtree keys valid cap i k))
  = ()

// Lemma: If a position is out of bounds, no key can be in its subtree
let lemma_out_of_bounds_empty
  (keys: Seq.seq int)
  (valid: Seq.seq bool)
  (cap: nat)
  (i: nat)
  (k: int)
  : Lemma
    (requires i >= cap)
    (ensures ~(key_in_subtree keys valid cap i k))
  = ()

// Old versions:
let lemma_search_left_preserves_completeness
  (keys: Seq.seq int)
  (valid: Seq.seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma
    (requires
      subtree_in_range keys valid cap i lo hi /\
      i < cap /\ i < Seq.length keys /\ i < Seq.length valid /\
      Seq.index valid i /\
      key < Seq.index keys i)
    (ensures
      (key_in_subtree keys valid cap i key ==>
       key_in_subtree keys valid cap (op_Multiply 2 i + 1) key))
  = reveal_opaque (`%lemma_key_not_in_right_if_less) (lemma_key_not_in_right_if_less keys valid cap i lo hi);
    C.move_requires (lemma_key_not_in_right_if_less keys valid cap i lo hi) key

let lemma_search_right_preserves_completeness
  (keys: Seq.seq int)
  (valid: Seq.seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma
    (requires
      subtree_in_range keys valid cap i lo hi /\
      i < cap /\ i < Seq.length keys /\ i < Seq.length valid /\
      Seq.index valid i /\
      key > Seq.index keys i)
    (ensures
      (key_in_subtree keys valid cap i key ==>
       key_in_subtree keys valid cap (op_Multiply 2 i + 2) key))
  = reveal_opaque (`%lemma_key_not_in_left_if_greater) (lemma_key_not_in_left_if_greater keys valid cap i lo hi);
    C.move_requires (lemma_key_not_in_left_if_greater keys valid cap i lo hi) key

// Lemma: If key is not in subtree at root, it's not at any valid position
// (requires additional well-formedness: all valid nodes are reachable from root)
// Deferred: needs a reachability predicate for the array-based tree structure.

// Lemma: When inserting at an invalid position, old keys are preserved
let rec lemma_insert_at_invalid_preserves_old_keys
  (keys_old: Seq.seq int)
  (valid_old: Seq.seq bool)
  (keys_new: Seq.seq int)
  (valid_new: Seq.seq bool)
  (cap: nat)
  (insert_idx: nat)
  (new_key: int)
  (root: nat)
  (old_key: int)
  : Lemma
    (requires
      insert_idx < cap /\
      insert_idx < Seq.length valid_old /\
      Seq.index valid_old insert_idx == false /\
      Seq.length keys_new == Seq.length keys_old /\
      Seq.length valid_new == Seq.length valid_old /\
      cap <= Seq.length keys_old /\
      cap <= Seq.length valid_old /\
      // new arrays: only position insert_idx changed
      (forall (i: nat). i < Seq.length keys_new /\ i < Seq.length valid_new /\ i =!= insert_idx ==>
        Seq.index valid_new i == Seq.index valid_old i /\
        Seq.index keys_new i == Seq.index keys_old i) /\
      Seq.index valid_new insert_idx == true /\
      Seq.index keys_new insert_idx == new_key /\
      // old_key was in old tree
      key_in_subtree keys_old valid_old cap root old_key)
    (ensures
      key_in_subtree keys_new valid_new cap root old_key)
    (decreases (if root < cap then cap - root else 0))
  = if root >= cap || root >= Seq.length keys_old || root >= Seq.length valid_old then ()
    else if root = insert_idx then ()  // contradiction: valid_old[root] was false, but key_in_subtree requires it true
    else (
      // root != insert_idx, so valid_new[root] == valid_old[root] and keys_new[root] == keys_old[root]
      assert (Seq.length keys_new == Seq.length keys_old);
      assert (root < Seq.length keys_old);
      assert (root < Seq.length keys_new);
      // key_in_subtree requires valid_old[root] == true
      // By definition: old_key == keys_old[root] \/ in left subtree \/ in right subtree
      let left = op_Multiply 2 root + 1 in
      let right = op_Multiply 2 root + 2 in
      // Use classical reasoning to handle the disjunction
      C.or_elim
        #(key_in_subtree keys_old valid_old cap left old_key)
        #(key_in_subtree keys_old valid_old cap right old_key)
        #(fun _ -> key_in_subtree keys_new valid_new cap root old_key)
        (fun _ -> lemma_insert_at_invalid_preserves_old_keys keys_old valid_old keys_new valid_new cap insert_idx new_key left old_key)
        (fun _ -> lemma_insert_at_invalid_preserves_old_keys keys_old valid_old keys_new valid_new cap insert_idx new_key right old_key)
    )

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
      // Note: Completeness (~key_in_subtree when None) requires BST property in precondition
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
  let vc = !current;
  
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
      // If not successful, arrays unchanged
      (not success ==> Seq.equal keys_seq' keys_seq /\
                       Seq.equal valid_seq' valid_seq)
      // Note: Proving key insertion and preservation requires BST property/reachability
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
        // If not yet successful, arrays unchanged
        (not vs ==> Seq.equal ks keys_seq /\ Seq.equal vs' valid_seq)
      )) **
    pure (SZ.v vc <= SZ.v t.cap)
  {
    let idx = !current;
    
    with ks vs'. assert (A.pts_to t.keys ks ** A.pts_to t.valid vs');
    
    let is_valid = t.valid.(idx);
    
    if (not is_valid) {
      // Capture old arrays before modification
      let old_keys = Ghost.hide ks;
      let old_valid = Ghost.hide vs';
      
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
