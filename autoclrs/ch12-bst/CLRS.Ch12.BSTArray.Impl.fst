module CLRS.Ch12.BSTArray.Impl
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
//SNIPPET_START: tree_search
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
//SNIPPET_END: tree_search
{
  let mut current : SZ.t = 0sz;
  let mut found = false;
  let mut result_idx : SZ.t = 0sz;
  
  // Ghost references for BST bounds tracking
  let lo_ref = GR.alloc #int (reveal lo);
  let hi_ref = GR.alloc #int (reveal hi);
  
  while (
    let vc = !current;
    let vf = !found;
    SZ.lt vc t.cap && not vf
  )
  invariant exists* vc vf vr vlo vhi vticks.
    R.pts_to current vc **
    R.pts_to found vf **
    R.pts_to result_idx vr **
    GR.pts_to lo_ref vlo **
    GR.pts_to hi_ref vhi **
    GR.pts_to ticks vticks **
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      SZ.v vc <= SZ.v t.cap /\
      // Complexity: tick count tracks node depth
      vticks >= 'n /\
      (~vf /\ SZ.v vc < SZ.v t.cap ==> vticks - 'n == node_depth (SZ.v vc)) /\
      (SZ.v t.cap > 0 ==> vticks - 'n <= tree_height (SZ.v t.cap)) /\
      (vf ==> (SZ.v vr < SZ.v t.cap /\
               Seq.index valid_seq (SZ.v vr) == true /\
               Seq.index keys_seq (SZ.v vr) == key)) /\
      (~vf ==> (
        (key_in_subtree keys_seq valid_seq (SZ.v t.cap) 0 key ==>
         key_in_subtree keys_seq valid_seq (SZ.v t.cap) (SZ.v vc) key) /\
        (SZ.v vc < SZ.v t.cap ==>
          subtree_in_range keys_seq valid_seq (SZ.v t.cap) (SZ.v vc) vlo vhi)))
    )
  decreases (SZ.v t.cap - SZ.v !current + (if not !found then 1 else 0))
  {
    let idx = !current;
    let is_valid = t.valid.(idx);
    
    if (not is_valid) {
      // Node is invalid — key can't be in subtree at idx
      lemma_invalid_node_empty keys_seq valid_seq (SZ.v t.cap) (SZ.v idx) key;
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
        
        // Preserve completeness: key in subtree at idx ⟹ key in left subtree
        with vlo vhi vticks_v. assert (GR.pts_to lo_ref vlo ** GR.pts_to hi_ref vhi ** GR.pts_to ticks vticks_v);
        lemma_search_left_preserves_completeness
          keys_seq valid_seq (SZ.v t.cap) (SZ.v idx) vlo vhi key;
        
        let two_idx = SZ.mul 2sz idx;
        let left_idx = SZ.add two_idx 1sz;
        if (SZ.gte left_idx t.cap) {
          // Left child out of bounds — key not in subtree
          lemma_out_of_bounds_empty keys_seq valid_seq (SZ.v t.cap) (SZ.v left_idx) key;
          current := t.cap;
        } else {
          // Complexity: moving to left child increases depth by 1
          node_depth_left_child (SZ.v idx);
          node_depth_bounded (SZ.v t.cap) (SZ.v left_idx);
          GR.op_Colon_Equals ticks (hide (vticks_v + 1));
          // Narrow bounds: hi becomes current_key
          GR.op_Colon_Equals hi_ref (hide current_key);
          current := left_idx;
        };
      } else {
        // Right child: 2*i + 2
        child_indices_fit (SZ.v t.cap) (SZ.v idx);
        assert (pure (SZ.fits (2 * SZ.v idx + 2)));
        
        // Preserve completeness: key in subtree at idx ⟹ key in right subtree
        with vlo vhi vticks_v. assert (GR.pts_to lo_ref vlo ** GR.pts_to hi_ref vhi ** GR.pts_to ticks vticks_v);
        lemma_search_right_preserves_completeness
          keys_seq valid_seq (SZ.v t.cap) (SZ.v idx) vlo vhi key;
        
        let two_idx = SZ.mul 2sz idx;
        let right_idx = SZ.add two_idx 2sz;
        if (SZ.gte right_idx t.cap) {
          // Right child out of bounds — key not in subtree
          lemma_out_of_bounds_empty keys_seq valid_seq (SZ.v t.cap) (SZ.v right_idx) key;
          current := t.cap;
        } else {
          // Complexity: moving to right child increases depth by 1
          node_depth_right_child (SZ.v idx);
          node_depth_bounded (SZ.v t.cap) (SZ.v right_idx);
          GR.op_Colon_Equals ticks (hide (vticks_v + 1));
          // Narrow bounds: lo becomes current_key
          GR.op_Colon_Equals lo_ref (hide current_key);
          current := right_idx;
        };
      };
    };
  };
  
  let vf = !found;
  let vr = !result_idx;
  let vc = !current;
  
  // Free ghost references (not the external ticks — caller owns that)
  with vlo_f vhi_f. assert (GR.pts_to lo_ref vlo_f ** GR.pts_to hi_ref vhi_f);
  GR.free lo_ref;
  GR.free hi_ref;
  
  if vf 
  { 
    Some vr
  } 
  else 
  {
    // vc >= cap, so key not in subtree at vc (out of bounds)
    lemma_out_of_bounds_empty keys_seq valid_seq (SZ.v t.cap) (SZ.v vc) key;
    None #SZ.t
  }
}

// After inserting key_val at position idx (reached by BST search from i),
// key_val is reachable from i. Uses local key_in_subtree.
let rec lemma_insert_key_reachable
  (keys: Seq.seq int) (valid: Seq.seq bool) (cap: nat)
  (i idx: nat) (key_val: int)
  : Lemma
    (requires
      AP.bst_search_reaches keys valid cap i idx key_val /\
      idx < Seq.length keys /\ idx < Seq.length valid /\
      Seq.length keys == Seq.length valid /\ Seq.length keys >= cap /\
      Seq.index valid idx == false)
    (ensures
      key_in_subtree (Seq.upd keys idx key_val) (Seq.upd valid idx true) cap i key_val)
    (decreases (if i < cap then cap - i else 0))
  = if i = idx then ()
    else begin
      let k_i = Seq.index keys i in
      if key_val < k_i then
        lemma_insert_key_reachable keys valid cap (op_Multiply 2 i + 1) idx key_val
      else
        lemma_insert_key_reachable keys valid cap (op_Multiply 2 i + 2) idx key_val
    end

// Tree insert
//SNIPPET_START: tree_insert
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
                    idx < Seq.length keys_seq /\
                    idx < Seq.length valid_seq /\
                    Seq.index valid_seq idx == false /\
                    Seq.equal keys_seq' (Seq.upd keys_seq idx key) /\
                    Seq.equal valid_seq' (Seq.upd valid_seq idx true))) /\
      (success ==> key_in_subtree keys_seq' valid_seq' (SZ.v t.cap) 0 key) /\
      AP.well_formed_bst keys_seq' valid_seq' (SZ.v t.cap) 0 (Ghost.reveal lo) (Ghost.reveal hi)
    )
//SNIPPET_END: tree_insert
{
  let mut current : SZ.t = 0sz;
  let mut done = false;
  let mut success_flag = false;
  
  while (
    let vc = !current;
    let vd = !done;
    SZ.lt vc t.cap && not vd
  )
  invariant exists* vc vd vs vticks.
    R.pts_to current vc **
    R.pts_to done vd **
    R.pts_to success_flag vs **
    GR.pts_to ticks vticks **
    (exists* ks vs'. A.pts_to t.keys ks ** A.pts_to t.valid vs' ** 
      pure (Seq.length ks == A.length t.keys /\ Seq.length vs' == A.length t.valid /\
        // If not yet successful, arrays unchanged
        (not vs ==> Seq.equal ks keys_seq /\ Seq.equal vs' valid_seq) /\
        // If successful, arrays are exactly Seq.upd at the inserted index (frame)
        (vs ==> (exists (idx: nat). idx < SZ.v t.cap /\
                 idx < Seq.length keys_seq /\
                 idx < Seq.length valid_seq /\
                 Seq.index valid_seq idx == false /\
                 Seq.equal ks (Seq.upd keys_seq idx key) /\
                 Seq.equal vs' (Seq.upd valid_seq idx true))) /\
        // If successful, key is reachable from root
        (vs ==> key_in_subtree ks vs' (SZ.v t.cap) 0 key) /\
        // BST invariant preserved
        AP.well_formed_bst ks vs' (SZ.v t.cap) 0 (Ghost.reveal lo) (Ghost.reveal hi)
      )) **
    pure (SZ.v vc <= SZ.v t.cap /\
      vticks >= 'n /\
      // Complexity: tick count tracks node depth
      (~vs /\ ~vd /\ SZ.v vc < SZ.v t.cap ==> vticks - 'n == node_depth (SZ.v vc)) /\
      (SZ.v t.cap > 0 ==> vticks - 'n <= tree_height (SZ.v t.cap)) /\
      (vs ==> vd) /\
      // BST search reaches current position (when still searching)
      (not vs /\ not vd /\ SZ.v vc < SZ.v t.cap ==>
        AP.bst_search_reaches keys_seq valid_seq (SZ.v t.cap) 0 (SZ.v vc) key))
  decreases (SZ.v t.cap - SZ.v !current + (if not !done then 1 else 0))
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
      // Prove well_formed_bst preserved after insertion
      AP.lemma_insert_wfb keys_seq valid_seq (SZ.v t.cap) 0
        (Ghost.reveal lo) (Ghost.reveal hi) (SZ.v idx) key;
      // Prove key is reachable from root after insertion
      lemma_insert_key_reachable keys_seq valid_seq (SZ.v t.cap) 0 (SZ.v idx) key;
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
          AP.lemma_bsr_extend_left keys_seq valid_seq (SZ.v t.cap) 0 (SZ.v idx) key;
          // Complexity: moving to left child increases depth by 1
          with vticks_v. assert (GR.pts_to ticks vticks_v);
          node_depth_left_child (SZ.v idx);
          node_depth_bounded (SZ.v t.cap) (SZ.v left_idx);
          GR.op_Colon_Equals ticks (hide (vticks_v + 1));
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
          AP.lemma_bsr_extend_right keys_seq valid_seq (SZ.v t.cap) 0 (SZ.v idx) key;
          // Complexity: moving to right child increases depth by 1
          with vticks_v. assert (GR.pts_to ticks vticks_v);
          node_depth_right_child (SZ.v idx);
          node_depth_bounded (SZ.v t.cap) (SZ.v right_idx);
          GR.op_Colon_Equals ticks (hide (vticks_v + 1));
          current := right_idx;
        };
      };
    };
  };
  
  !success_flag
}

// Pure specification: inorder traversal returns list of keys in sorted order
//SNIPPET_START: inorder_spec
let rec inorder_spec
  (keys: Seq.seq int)
  (valid: Seq.seq bool)
  (cap: nat)
  (i: nat)
  : Tot (list int) (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= Seq.length keys || i >= Seq.length valid then []
    else if not (Seq.index valid i) then []
    else
      let left = op_Multiply 2 i + 1 in
      let right = op_Multiply 2 i + 2 in
      inorder_spec keys valid cap left @
      [Seq.index keys i] @
      inorder_spec keys valid cap right
//SNIPPET_END: inorder_spec

// Inorder tree walk (CLRS §12.1) — recursive helper
// Walks the subtree rooted at index `idx`, writing keys to `output` at `write_pos`
//SNIPPET_START: inorder_helper
fn rec inorder_helper
  (#p: perm)
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (idx: SZ.t)
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
  decreases (if SZ.v idx < SZ.v t.cap then SZ.v t.cap - SZ.v idx else 0)
{
  if (SZ.gte idx t.cap) {
    // Base case: index out of bounds, nothing to do
    ()
  } else {
    let is_valid = t.valid.(idx);
    if (not is_valid) {
      // Node is invalid: nothing to do
      ()
    } else {
      // Compute child indices
      child_indices_fit (SZ.v t.cap) (SZ.v idx);
      let two_idx = SZ.mul 2sz idx;
      let left_idx = SZ.add two_idx 1sz;
      let right_idx = SZ.add two_idx 2sz;

      // Recurse on left subtree
      inorder_helper #p t #keys_seq #valid_seq left_idx output write_pos out_len;

      // Open existential from left recursive call
      with out_seq1 wp1. assert (A.pts_to output out_seq1 ** R.pts_to write_pos wp1);

      // Write current node's key to output, then recurse on right subtree
      let wp = !write_pos;
      if (SZ.lt wp out_len) {
        let key = t.keys.(idx);
        output.(wp) <- key;
        write_pos := SZ.add wp 1sz;
        // Recurse on right subtree (after writing)
        inorder_helper #p t #keys_seq #valid_seq right_idx output write_pos out_len;
      } else {
        // Recurse on right subtree (without writing — output full)
        inorder_helper #p t #keys_seq #valid_seq right_idx output write_pos out_len;
      };
    }
  }
}
//SNIPPET_END: inorder_helper

// Inorder tree walk — main entry point starting from root (index 0)
//SNIPPET_START: inorder_walk
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
{
  inorder_helper #p t #keys_seq #valid_seq 0sz output write_pos out_len
}
//SNIPPET_END: inorder_walk

// ============================================================
// Bridge: AP.well_formed_bst → local subtree_in_range
//
// Two-step bridge:
// 1. AP.lemma_well_formed_implies_sir: AP.well_formed_bst → AP.subtree_in_range
// 2. sir_bridge: AP.subtree_in_range → local subtree_in_range
// ============================================================

let rec sir_bridge
  (keys: Seq.seq int) (valid: Seq.seq bool) (cap: nat) (i: nat) (lo hi: int)
  : Lemma
    (requires AP.subtree_in_range keys valid cap i lo hi)
    (ensures subtree_in_range keys valid cap i lo hi)
    (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= Seq.length keys || i >= Seq.length valid then ()
    else if not (Seq.index valid i) then ()
    else begin
      let k = Seq.index keys i in
      sir_bridge keys valid cap (op_Multiply 2 i + 1) lo k;
      sir_bridge keys valid cap (op_Multiply 2 i + 2) k hi
    end

let wfb_to_sir
  (keys: Seq.seq int) (valid: Seq.seq bool)
  (cap: nat) (i: nat) (lo hi: int)
  : Lemma
    (requires AP.well_formed_bst keys valid cap i lo hi)
    (ensures subtree_in_range keys valid cap i lo hi)
  = AP.lemma_well_formed_implies_sir keys valid cap i lo hi;
    sir_bridge keys valid cap i lo hi
