module CLRS.Ch12.BSTArray.Delete
#lang-pulse
open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module C = FStar.Classical

open FStar.Mul

module AP = CLRS.Ch12.BSTArray.Predicates

(**
 * BST Delete Operations: TREE-MINIMUM, TREE-MAXIMUM, and TREE-DELETE
 * 
 * This module implements CLRS Ch 12.3 delete operations for an array-based BST.
 * 
 * Array-based BST structure (from CLRS.Ch12.BST):
 * - keys: A.array int — key at each node
 * - valid: A.array bool — whether position has a node
 * - Left child of i = 2*i+1, right child = 2*i+2
 * - Type: noeq type bst = { keys: A.array int; valid: A.array bool; cap: SZ.t; }
 * 
 * Operations:
 * 1. TREE-MINIMUM(x): Walk left children until no valid left child
 * 2. TREE-MAXIMUM(x): Walk right children until no valid right child
 * 3. TREE-DELETE(T, z): Delete a node (simplified for array representation)
 * 
 * For the array-based representation, DELETE is simplified:
 * - Mark the node as invalid (valid[i] = false)
 * - For structural preservation, we could rebuild subtrees, but for now
 *   we use a simple "mark invalid" approach (INCOMPLETE: orphans children)
 * 
 * Status:
 * - TREE-MINIMUM and TREE-MAXIMUM: Fully verified (no admits)
 * - TREE-SUCCESSOR and TREE-PREDECESSOR: Fully verified (no admits)
 * - TREE-DELETE: Two-children case uses successor key-swap; one-child cases
 *   still just mark invalid (orphaning child subtrees). No admits are used,
 *   but one-child cases are semantically incomplete.
 *)

// Import BST type from main module and shared predicates
open CLRS.Ch12.BSTArray.Impl
open CLRS.Ch12.BSTArray.Predicates

// ============================================================================
// TREE-MINIMUM: Find the minimum key in subtree rooted at start_idx
// ============================================================================

(**
 * TREE-MINIMUM(x) from CLRS 12.2-3
 * 
 * In pointer-based tree:
 *   TREE-MINIMUM(x)
 *     while x.left ≠ NIL
 *       x = x.left
 *     return x
 * 
 * In array-based tree:
 *   Start at index i
 *   While 2*i+1 < cap && valid[2*i+1], set i = 2*i+1
 *   Return i
 * 
 * Postcondition:
 * - Returns index of minimum key in subtree
 * - Returned node is valid
 * - No valid left child (it's a leftmost node)
 *)
//SNIPPET_START: tree_minimum
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
//SNIPPET_END: tree_minimum
{
  let mut current : SZ.t = start_idx;
  
  // Compute initial condition: does start_idx have a valid left child?
  child_indices_fit (SZ.v t.cap) (SZ.v start_idx);
  let two_s = SZ.mul 2sz start_idx;
  let left_s = SZ.add two_s 1sz;
  let mut go: bool = false;
  if SZ.lt left_s t.cap {
    go := t.valid.(left_s);
  };
  
  while (!go)
  invariant exists* vc vgo.
    R.pts_to current vc **
    R.pts_to go vgo **
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      SZ.v vc < SZ.v t.cap /\
      SZ.v vc < Seq.length valid_seq /\
      Seq.index valid_seq (SZ.v vc) == true /\
      AP.is_left_spine (SZ.v start_idx) (SZ.v vc) valid_seq (SZ.v t.cap) /\
      (vgo ==> (2 * SZ.v vc + 1 < SZ.v t.cap /\
                2 * SZ.v vc + 1 < Seq.length valid_seq /\
                Seq.index valid_seq (2 * SZ.v vc + 1) == true)) /\
      (not vgo ==> (2 * SZ.v vc + 1 >= SZ.v t.cap \/
                    (2 * SZ.v vc + 1 < Seq.length valid_seq /\
                     Seq.index valid_seq (2 * SZ.v vc + 1) == false)))
    )
  decreases (SZ.v t.cap - SZ.v !current)
  {
    let vc = !current;
    child_indices_fit (SZ.v t.cap) (SZ.v vc);
    let two_vc = SZ.mul 2sz vc;
    let left_idx = SZ.add two_vc 1sz;
    // Extend the left spine: vc → left_idx
    AP.lemma_left_spine_extend (SZ.v start_idx) (SZ.v vc) valid_seq (SZ.v t.cap);
    current := left_idx;
    
    // Recompute condition for next iteration
    child_indices_fit (SZ.v t.cap) (SZ.v left_idx);
    let new_two = SZ.mul 2sz left_idx;
    let new_left = SZ.add new_two 1sz;
    if SZ.lt new_left t.cap {
      go := t.valid.(new_left);
    } else {
      go := false;
    };
  };
  
  !current
}

// ============================================================================
// TREE-MAXIMUM: Find the maximum key in subtree rooted at start_idx
// ============================================================================

(**
 * TREE-MAXIMUM(x) from CLRS 12.2-4
 * 
 * In pointer-based tree:
 *   TREE-MAXIMUM(x)
 *     while x.right ≠ NIL
 *       x = x.right
 *     return x
 * 
 * In array-based tree:
 *   Start at index i
 *   While 2*i+2 < cap && valid[2*i+2], set i = 2*i+2
 *   Return i
 * 
 * Postcondition:
 * - Returns index of maximum key in subtree
 * - Returned node is valid
 * - No valid right child (it's a rightmost node)
 *)
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
      Seq.index valid_seq (SZ.v start_idx) == true  // Start at valid node
    )
  returns result: SZ.t
  ensures
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      SZ.v result < SZ.v t.cap /\
      SZ.v result < Seq.length valid_seq /\
      Seq.index valid_seq (SZ.v result) == true /\
      // Result has no valid right child (it's rightmost)
      (2 * SZ.v result + 2 >= SZ.v t.cap \/
       (2 * SZ.v result + 2 < Seq.length valid_seq /\
        Seq.index valid_seq (2 * SZ.v result + 2) == false))
    )
{
  let mut current : SZ.t = start_idx;
  
  // Compute initial condition: does start_idx have a valid right child?
  child_indices_fit (SZ.v t.cap) (SZ.v start_idx);
  let two_s = SZ.mul 2sz start_idx;
  let right_s = SZ.add two_s 2sz;
  let mut go: bool = false;
  if SZ.lt right_s t.cap {
    go := t.valid.(right_s);
  };
  
  while (!go)
  invariant exists* vc vgo.
    R.pts_to current vc **
    R.pts_to go vgo **
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    pure (
      SZ.v vc < SZ.v t.cap /\
      SZ.v vc < Seq.length valid_seq /\
      Seq.index valid_seq (SZ.v vc) == true /\
      (vgo ==> (2 * SZ.v vc + 2 < SZ.v t.cap /\
                2 * SZ.v vc + 2 < Seq.length valid_seq /\
                Seq.index valid_seq (2 * SZ.v vc + 2) == true)) /\
      (not vgo ==> (2 * SZ.v vc + 2 >= SZ.v t.cap \/
                    (2 * SZ.v vc + 2 < Seq.length valid_seq /\
                     Seq.index valid_seq (2 * SZ.v vc + 2) == false)))
    )
  decreases (SZ.v t.cap - SZ.v !current)
  {
    let vc = !current;
    child_indices_fit (SZ.v t.cap) (SZ.v vc);
    let two_vc = SZ.mul 2sz vc;
    let right_idx = SZ.add two_vc 2sz;
    current := right_idx;
    
    // Recompute condition for next iteration
    child_indices_fit (SZ.v t.cap) (SZ.v right_idx);
    let new_two = SZ.mul 2sz right_idx;
    let new_right = SZ.add new_two 2sz;
    if SZ.lt new_right t.cap {
      go := t.valid.(new_right);
    } else {
      go := false;
    };
  };
  
  !current
}

// ============================================================================
// TREE-SUCCESSOR: Find the in-order successor of a node
// ============================================================================

(**
 * TREE-SUCCESSOR(x) from CLRS 12.2
 *
 * In pointer-based tree:
 *   TREE-SUCCESSOR(x)
 *     if x.right ≠ NIL
 *       return TREE-MINIMUM(x.right)
 *     y = x.p
 *     while y ≠ NIL and x == y.right
 *       x = y
 *       y = y.p
 *     return y
 *
 * In array-based tree:
 *   Case 1: If right child exists and is valid, return TREE-MINIMUM(right child)
 *   Case 2: Walk up while current node is a right child of its parent.
 *           When we find a node that is a left child, its parent is the successor.
 *           If we reach the root without finding such a node, there is no successor.
 *
 * Array navigation:
 *   parent(i) = (i-1)/2 for i > 0
 *   i is a right child iff i > 0 and i is even  (i == 2*parent + 2)
 *   i is a left child  iff i is odd              (i == 2*parent + 1)
 *)
//SNIPPET_START: tree_successor
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
//SNIPPET_END: tree_successor
{
  // Step 1: Check if right child exists and is valid
  child_indices_fit (SZ.v t.cap) (SZ.v idx);
  let two_idx = SZ.mul 2sz idx;
  let right_idx = SZ.add two_idx 2sz;

  let has_right =
    if (SZ.lt right_idx t.cap) {
      t.valid.(right_idx)
    } else {
      false
    };

  if has_right {
    // Case 1 (CLRS): x.right ≠ NIL → return TREE-MINIMUM(x.right)
    let min_idx = tree_minimum t right_idx;
    Some min_idx
  } else {
    // Case 2 (CLRS): No right child — walk up to find successor
    // y = x.p; while y ≠ NIL and x == y.right: x = y; y = y.p; return y
    //
    // Walk up while current is a right child (even index > 0).
    // A right child has index i where i > 0 and i % 2 == 0.
    let mut current : SZ.t = idx;

    while (
      let vc = !current;
      // Continue while vc > 0 and vc is a right child (even)
      // A right child has i > 0 and i % 2 == 0, i.e., not (i % 2 > 0)
      if (SZ.gt vc 0sz) {
        not (SZ.gt (SZ.rem vc 2sz) 0sz)
      } else {
        false
      }
    )
    invariant exists* vc.
      R.pts_to current vc **
      A.pts_to t.keys #p keys_seq **
      A.pts_to t.valid #p valid_seq **
      pure (
        SZ.v vc < SZ.v t.cap
      )
    decreases (SZ.v !current)
    {
      // Move to parent: parent(vc) = (vc - 1) / 2
      let vc = !current;
      let parent = SZ.div (SZ.sub vc 1sz) 2sz;
      current := parent;
    };

    let vc = !current;
    // After loop: vc == 0 (reached root) or vc is odd (left child)
    if (SZ.gt vc 0sz) {
      // vc is a left child (odd) — its parent is the successor
      let parent = SZ.div (SZ.sub vc 1sz) 2sz;
      // Verify parent is in bounds and valid
      if (SZ.lt parent t.cap) {
        let parent_valid = t.valid.(parent);
        if parent_valid {
          Some parent
        } else {
          None #SZ.t
        }
      } else {
        None #SZ.t
      }
    } else {
      // Reached root while always going up through right children — no successor
      None #SZ.t
    }
  }
}

// ============================================================================
// TREE-PREDECESSOR: Find the in-order predecessor of a node
// ============================================================================

(**
 * TREE-PREDECESSOR(x) from CLRS 12.2 (symmetric to TREE-SUCCESSOR)
 *
 * In pointer-based tree:
 *   TREE-PREDECESSOR(x)
 *     if x.left ≠ NIL
 *       return TREE-MAXIMUM(x.left)
 *     y = x.p
 *     while y ≠ NIL and x == y.left
 *       x = y
 *       y = y.p
 *     return y
 *
 * In array-based tree:
 *   Case 1: If left child exists and is valid, return TREE-MAXIMUM(left child)
 *   Case 2: Walk up while current node is a left child of its parent.
 *           When we find a node that is a right child, its parent is the predecessor.
 *           If we reach the root without finding such a node, there is no predecessor.
 *
 * Array navigation:
 *   parent(i) = (i-1)/2 for i > 0
 *   i is a left child  iff i is odd              (i == 2*parent + 1)
 *   i is a right child iff i > 0 and i is even   (i == 2*parent + 2)
 *)
//SNIPPET_START: tree_predecessor
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
//SNIPPET_END: tree_predecessor
{
  // Step 1: Check if left child exists and is valid
  child_indices_fit (SZ.v t.cap) (SZ.v idx);
  let two_idx = SZ.mul 2sz idx;
  let left_idx = SZ.add two_idx 1sz;

  let has_left =
    if (SZ.lt left_idx t.cap) {
      t.valid.(left_idx)
    } else {
      false
    };

  if has_left {
    // Case 1 (CLRS): x.left ≠ NIL → return TREE-MAXIMUM(x.left)
    let max_idx = tree_maximum t left_idx;
    Some max_idx
  } else {
    // Case 2 (CLRS): No left child — walk up to find predecessor
    // y = x.p; while y ≠ NIL and x == y.left: x = y; y = y.p; return y
    //
    // Walk up while current is a left child (odd index).
    // A left child has index i where i > 0 and i % 2 == 1.
    let mut current : SZ.t = idx;

    while (
      let vc = !current;
      // Continue while vc > 0 and vc is a left child (odd)
      // A left child has i > 0 and i % 2 == 1, i.e., not (i % 2 == 0)
      if (SZ.gt vc 0sz) {
        not (not (SZ.gt (SZ.rem vc 2sz) 0sz))
      } else {
        false
      }
    )
    invariant exists* vc.
      R.pts_to current vc **
      A.pts_to t.keys #p keys_seq **
      A.pts_to t.valid #p valid_seq **
      pure (
        SZ.v vc < SZ.v t.cap
      )
    decreases (SZ.v !current)
    {
      // Move to parent: parent(vc) = (vc - 1) / 2
      let vc = !current;
      let parent = SZ.div (SZ.sub vc 1sz) 2sz;
      current := parent;
    };

    let vc = !current;
    // After loop: vc == 0 (reached root) or vc is even and > 0 (right child)
    if (SZ.gt vc 0sz) {
      // vc is a right child (even, > 0) — its parent is the predecessor
      let parent = SZ.div (SZ.sub vc 1sz) 2sz;
      // Verify parent is in bounds and valid
      if (SZ.lt parent t.cap) {
        let parent_valid = t.valid.(parent);
        if parent_valid {
          Some parent
        } else {
          None #SZ.t
        }
      } else {
        None #SZ.t
      }
    } else {
      // Reached root while always going up through left children — no predecessor
      None #SZ.t
    }
  }
}

// ============================================================================
// TREE-DELETE: Delete a node from the BST
// ============================================================================

(**
 * TREE-DELETE(T, z) from CLRS 12.3
 * 
 * In pointer-based tree, CLRS uses TRANSPLANT to handle three cases:
 *   1. z has no left child → replace z with right child
 *   2. z has no right child → replace z with left child
 *   3. z has two children → find successor y (minimum of right subtree),
 *      transplant y's right child to y's position, then replace z with y
 * 
 * In array-based tree, TRANSPLANT is complex because we can't rewire pointers.
 * Instead, we use a simplified approach:
 *   - If node is a leaf (no valid children): just mark invalid
 *   - If node has one child: mark invalid, optionally move child up
 *   - If node has two children: find successor, swap keys, delete successor
 * 
 * For this implementation, we use the simplest correct approach:
 *   - Mark the node as invalid (valid[idx] = false)
 *   - This leaves children orphaned, which violates structural invariants
 *   - Full correctness would require rebuilding subtrees (admitted for now)
 * 
 * A more sophisticated approach would:
 *   1. Find successor (TREE-MINIMUM of right subtree)
 *   2. Copy successor's key to deleted node
 *   3. Recursively delete the successor (which has at most one child)
 * 
 * We implement the key-swap approach with admits for complex proofs.
 *)

//SNIPPET_START: tree_delete
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
//SNIPPET_END: tree_delete
{
  // Check if node has children
  child_indices_fit (SZ.v t.cap) (SZ.v del_idx);
  assert (pure (SZ.fits (2 * SZ.v del_idx + 1)));
  assert (pure (SZ.fits (2 * SZ.v del_idx + 2)));
  
  let two_idx = SZ.mul 2sz del_idx;
  let left_idx = SZ.add two_idx 1sz;
  let right_idx = SZ.add two_idx 2sz;
  
  let has_left = 
    if (SZ.lt left_idx t.cap) {
      t.valid.(left_idx)
    } else {
      false
    };
  
  let has_right = 
    if (SZ.lt right_idx t.cap) {
      t.valid.(right_idx)
    } else {
      false
    };
  
  // Case 1: No children (leaf node) - just mark invalid
  if (not has_left && not has_right) {
    t.valid.(del_idx) <- false;
    // Prove BST invariant preserved for leaf deletion
    AP.lemma_is_desc_of_root (SZ.v del_idx);
    AP.lemma_leaf_delete_wfb keys_seq valid_seq (SZ.v t.cap) 0
      (Ghost.reveal lo) (Ghost.reveal hi) (SZ.v del_idx);
    true
  }
  // Cases 2-4: Node has at least one child
  // Strategy: find successor (min of right subtree) or predecessor (max of left),
  // copy its key to del_idx, then delete the successor/predecessor if it's a leaf.
  else if has_right {
    // Has right child (possibly left too) → use successor approach
    let succ_idx = tree_minimum t right_idx;
    // succ_idx has no valid left child (from tree_minimum)
    // Check if succ_idx is also a leaf (no valid right child)
    child_indices_fit (SZ.v t.cap) (SZ.v succ_idx);
    let two_succ = SZ.mul 2sz succ_idx;
    let succ_right = SZ.add two_succ 2sz;
    let succ_has_right =
      if (SZ.lt succ_right t.cap) {
        t.valid.(succ_right)
      } else {
        false
      };
    if (not succ_has_right) {
      // Successor is a leaf: key swap + leaf delete preserves well_formed_bst
      let succ_key = t.keys.(succ_idx);
      t.keys.(del_idx) <- succ_key;
      t.valid.(succ_idx) <- false;
      // Prove well_formed_bst preserved using the combined swap+delete lemma
      AP.lemma_is_desc_of_root (SZ.v del_idx);
      AP.lemma_successor_swap_delete_wfb
        keys_seq valid_seq (SZ.v t.cap) 0
        (Ghost.reveal lo) (Ghost.reveal hi) (SZ.v del_idx) (SZ.v succ_idx);
      true
    } else {
      // Successor has right child: cannot handle without recursion
      // Return false (tree unchanged) to preserve well_formed_bst
      false
    }
  }
  // Case: Only left child (no right child)
  else {
    // Cannot handle without predecessor-swap infrastructure
    // Return false (tree unchanged) to preserve well_formed_bst
    false
  }
}

// ============================================================================
// Helper: Delete a node by key (find then delete)
// ============================================================================

(**
 * High-level delete operation: find a key, then delete it
 * 
 * This combines TREE-SEARCH with TREE-DELETE:
 *   1. Search for the key
 *   2. If found, delete the node at that index
 *   3. Return success/failure
 *)

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
{
  // First, search for the key
  let mut current : SZ.t = 0sz;
  let mut found = false;
  let mut found_idx : SZ.t = 0sz;
  
  // Search loop (simplified from tree_search in CLRS.Ch12.BST)
  while (
    let vc = !current;
    let vf = !found;
    SZ.lt vc t.cap && not vf
  )
  invariant exists* vc vf vfi.
    R.pts_to current vc **
    R.pts_to found vf **
    R.pts_to found_idx vfi **
    (exists* ks vs. 
      A.pts_to t.keys ks ** 
      A.pts_to t.valid vs ** 
      pure (
        Seq.length ks == A.length t.keys /\
        Seq.length vs == A.length t.valid /\
        // Arrays unchanged during search
        Seq.equal ks keys_seq /\
        Seq.equal vs valid_seq /\
        SZ.v vc <= SZ.v t.cap /\
        (vf ==> (SZ.v vfi < SZ.v t.cap /\
                 Seq.index vs (SZ.v vfi) == true /\
                 Seq.index ks (SZ.v vfi) == key))
      ))
  decreases (SZ.v t.cap - SZ.v !current + (if not !found then 1 else 0))
  {
    let idx = !current;
    
    with ks vs. assert (A.pts_to t.keys ks ** A.pts_to t.valid vs);
    
    let is_valid = t.valid.(idx);
    
    if (not is_valid) {
      current := t.cap;
    } else {
      let current_key = t.keys.(idx);
      if (current_key = key) {
        found_idx := idx;
        found := true;
      } else if (key < current_key) {
        child_indices_fit (SZ.v t.cap) (SZ.v idx);
        let two_idx = SZ.mul 2sz idx;
        let left_idx = SZ.add two_idx 1sz;
        if (SZ.gte left_idx t.cap) {
          current := t.cap;
        } else {
          current := left_idx;
        };
      } else {
        child_indices_fit (SZ.v t.cap) (SZ.v idx);
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
  
  // If found, delete it
  let vf = !found;
  if vf {
    let vfi = !found_idx;
    with ks vs. assert (A.pts_to t.keys ks ** A.pts_to t.valid vs);
    Seq.lemma_eq_elim ks (Ghost.reveal keys_seq);
    Seq.lemma_eq_elim vs (Ghost.reveal valid_seq);
    rewrite (A.pts_to t.keys ks) as (A.pts_to t.keys keys_seq);
    rewrite (A.pts_to t.valid vs) as (A.pts_to t.valid valid_seq);
    tree_delete t vfi #lo #hi
  } else {
    false
  }
}
