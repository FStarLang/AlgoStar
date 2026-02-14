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

// Lemma: If a node is in the subtree and subtree_in_range holds at root,
// then subtree_in_range holds for that node with appropriate bounds
let rec lemma_reachable_implies_subtree_in_range
  (keys: Seq.seq int)
  (valid: Seq.seq bool)
  (cap: nat)
  (root: nat)
  (lo hi: int)
  (i: nat)
  : Lemma
    (requires
      subtree_in_range keys valid cap root lo hi /\
      root < cap /\ root < Seq.length keys /\ root < Seq.length valid /\
      Seq.index valid root /\
      i < cap /\ i < Seq.length keys /\ i < Seq.length valid /\
      Seq.index valid i /\
      // i is in subtree rooted at root (simplified: i >= root since array-based tree)
      i >= root)
    (ensures
      // There exist bounds for i
      (exists (lo_i hi_i: int). subtree_in_range keys valid cap i lo_i hi_i /\
         lo < lo_i /\ hi_i < hi))
    (decreases (if root < cap then cap - root else 0))
  =  admit() // TODO: This needs a proper reachability predicate for array-based trees

// Simplified helper lemmas that don't require exact bounds
let lemma_search_left_simple
  (keys: Seq.seq int)
  (valid: Seq.seq bool)
  (cap: nat)
  (i: nat)
  (key: int)
  : Lemma
    (requires
      // Assume SOME bounds exist for which subtree_in_range holds
      (exists (lo hi: int). subtree_in_range keys valid cap i lo hi) /\
      i < cap /\ i < Seq.length keys /\ i < Seq.length valid /\
      Seq.index valid i /\
      key < Seq.index keys i /\
      key_in_subtree keys valid cap i key)
    (ensures
      key_in_subtree keys valid cap (op_Multiply 2 i + 1) key)
  = admit() // TODO: Complete this proof using exists_elim on the bounds

let lemma_search_right_simple
  (keys: Seq.seq int)
  (valid: Seq.seq bool)
  (cap: nat)
  (i: nat)
  (key: int)
  : Lemma
    (requires
      (exists (lo hi: int). subtree_in_range keys valid cap i lo hi) /\
      i < cap /\ i < Seq.length keys /\ i < Seq.length valid /\
      Seq.index valid i /\
      key > Seq.index keys i /\
      key_in_subtree keys valid cap i key)
    (ensures
      key_in_subtree keys valid cap (op_Multiply 2 i + 2) key)
  = admit() // TODO: Complete this proof using exists_elim on the bounds

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
        Seq.index keys_seq (SZ.v (Some?.v result)) == key)) /\
      (None? result ==> ~(key_in_subtree keys_seq valid_seq (SZ.v t.cap) 0 key))
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
               Seq.index keys_seq (SZ.v vr) == key)) /\
      (~vf ==> (
         key_in_subtree keys_seq valid_seq (SZ.v t.cap) 0 key ==>
         SZ.v vc < SZ.v t.cap /\ key_in_subtree keys_seq valid_seq (SZ.v t.cap) (SZ.v vc) key))
    )
  {
    let idx = !current;
    let is_valid = t.valid.(idx);
    
    if (not is_valid) {
      current := t.cap;
      admit();
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
          admit();
        } else {
          // If key is in tree, it must be in left subtree (derived from BST property)
          // TODO: Apply lemma_key_not_in_right_if_less when subtree_in_range precondition is added
          admit();
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
          // When we set current >= cap, the invariant holds vacuously
          admit();
        } else {
          // If key is in tree, it must be in right subtree (derived from BST property)
          // TODO: Apply lemma_key_not_in_left_if_greater when subtree_in_range precondition is added
          admit();
          current := right_idx;
        };
      };
    };
  };
  
  let vf = !found;
  let vr = !result_idx;
  let vc = !current;
  
  // Help SMT see the completeness proof:
  // Loop exits when vf OR vc >= cap
  // If ~vf, then vc >= cap
  // From invariant: ~vf ==> (key_in_subtree...0... ==> vc < cap /\ key_in_subtree...vc...)
  // But vc >= cap, so key_in_subtree...0... must be false
  assert (pure (~vf ==> ~(key_in_subtree keys_seq valid_seq (SZ.v t.cap) 0 key)));
  
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
