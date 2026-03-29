module CLRS.Ch12.BSTArray.Predicates

(**
 * Shared array-based BST predicates and lemmas
 *
 * Used by both the Pulse implementation (CLRS.Ch12.BST) and the
 * pure search specification (CLRS.Ch12.BST.Spec).
 *)

open FStar.Seq
open FStar.Classical
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
  = assert_norm (pow2 16 = 65536)

// Stronger BST property: all keys in subtree are bounded by lo and hi
let rec subtree_in_range 
  (keys: seq int) 
  (valid: seq bool) 
  (cap: nat) 
  (i: nat) 
  (lo hi: int)
  : Tot prop (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then True
    else if not (index valid i) then True
    else 
      let k = index keys i in
      let left = 2 * i + 1 in
      let right = 2 * i + 2 in
      lo < k /\ k < hi /\
      subtree_in_range keys valid cap left lo k /\
      subtree_in_range keys valid cap right k hi

// Key membership in subtree rooted at i
let rec key_in_subtree 
  (keys: seq int) 
  (valid: seq bool) 
  (cap: nat) 
  (i: nat) 
  (key: int)
  : Tot prop (decreases (if i < cap then cap - i else 0))
  = i < cap /\ i < length keys /\ i < length valid /\
    index valid i /\
    (index keys i == key \/
     key_in_subtree keys valid cap (2 * i + 1) key \/
     key_in_subtree keys valid cap (2 * i + 2) key)

// Lemma: If key is in a bounded subtree, it must be within the bounds
let rec lemma_key_in_bounded_subtree
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma 
    (requires subtree_in_range keys valid cap i lo hi /\ key_in_subtree keys valid cap i key)
    (ensures lo < key /\ key < hi)
    (decreases (if i < cap then cap - i else 0))
  = let left = 2 * i + 1 in
    let right = 2 * i + 2 in
    or_elim
      #(key_in_subtree keys valid cap left key)
      #(key_in_subtree keys valid cap right key)
      #(fun _ -> lo < key /\ key < hi)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap left lo (index keys i) key)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap right (index keys i) hi key)

// Lemma: If key < current_key and BST property holds, key can only be in left subtree
[@@"opaque_to_smt"]
let lemma_key_not_in_right_if_less
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma
    (requires 
      subtree_in_range keys valid cap i lo hi /\
      i < cap /\ i < length keys /\ i < length valid /\
      index valid i /\
      key < index keys i /\
      key_in_subtree keys valid cap i key)
    (ensures key_in_subtree keys valid cap (2 * i + 1) key)
  = let k = index keys i in
    let right = 2 * i + 2 in
    or_elim
      #(key_in_subtree keys valid cap right key)
      #(~(key_in_subtree keys valid cap right key))
      #(fun _ -> key_in_subtree keys valid cap (2 * i + 1) key)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap right k hi key)
      (fun _ -> ())

// Lemma: If key > current_key and BST property holds, key can only be in right subtree  
[@@"opaque_to_smt"]
let lemma_key_not_in_left_if_greater
  (keys: seq int)
  (valid: seq bool)
  (cap: nat)
  (i: nat)
  (lo hi: int)
  (key: int)
  : Lemma
    (requires 
      subtree_in_range keys valid cap i lo hi /\
      i < cap /\ i < length keys /\ i < length valid /\
      index valid i /\
      key > index keys i /\
      key_in_subtree keys valid cap i key)
    (ensures key_in_subtree keys valid cap (2 * i + 2) key)
  = let k = index keys i in
    let left = 2 * i + 1 in
    or_elim
      #(key_in_subtree keys valid cap left key)
      #(~(key_in_subtree keys valid cap left key))
      #(fun _ -> key_in_subtree keys valid cap (2 * i + 2) key)
      (fun _ -> lemma_key_in_bounded_subtree keys valid cap left lo k key)
      (fun _ -> ())

// ====================================================================
// Well-formed BST: BST property + structural invariant
// (no valid nodes below invalid ones)
// ====================================================================

/// All positions in the subtree rooted at i are invalid
let rec subtree_all_invalid (valid: seq bool) (cap: nat) (i: nat)
  : Tot prop (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length valid then True
    else (index valid i == false) /\
         subtree_all_invalid valid cap (2 * i + 1) /\
         subtree_all_invalid valid cap (2 * i + 2)

/// BST ordering + no valid nodes below invalid nodes
let rec well_formed_bst 
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat) (lo hi: int)
  : Tot prop (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then True
    else if not (index valid i) then subtree_all_invalid valid cap i
    else 
      let k = index keys i in
      let left = 2 * i + 1 in
      let right = 2 * i + 2 in
      lo < k /\ k < hi /\
      well_formed_bst keys valid cap left lo k /\
      well_formed_bst keys valid cap right k hi

/// well_formed_bst implies the weaker subtree_in_range
let rec lemma_well_formed_implies_sir
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat) (lo hi: int)
  : Lemma (requires well_formed_bst keys valid cap i lo hi)
          (ensures subtree_in_range keys valid cap i lo hi)
          (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then ()
    else if not (index valid i) then ()
    else begin
      let k = index keys i in
      lemma_well_formed_implies_sir keys valid cap (2 * i + 1) lo k;
      lemma_well_formed_implies_sir keys valid cap (2 * i + 2) k hi
    end

#push-options "--fuel 2 --ifuel 1"

/// Frame: subtree_all_invalid unchanged by Seq.upd at idx < j
let rec lemma_sai_frame (valid: seq bool) (cap j idx: nat) (v: bool)
  : Lemma (requires idx < j /\ idx < length valid)
          (ensures subtree_all_invalid valid cap j == 
                   subtree_all_invalid (upd valid idx v) cap j)
          (decreases (if j < cap then cap - j else 0))
  = if j >= cap || j >= length valid then ()
    else begin
      lemma_sai_frame valid cap (2 * j + 1) idx v;
      lemma_sai_frame valid cap (2 * j + 2) idx v
    end

/// Frame: well_formed_bst unchanged by Seq.upd at idx < j
let rec lemma_wfb_frame 
  (keys: seq int) (valid: seq bool) (cap j: nat) (lo hi: int) (idx: nat) (k: int) (v: bool)
  : Lemma (requires idx < j /\ idx < length keys /\ idx < length valid)
          (ensures well_formed_bst keys valid cap j lo hi == 
                   well_formed_bst (upd keys idx k) (upd valid idx v) cap j lo hi)
          (decreases (if j < cap then cap - j else 0))
  = if j >= cap || j >= length keys || j >= length valid then ()
    else if not (index valid j) then
      lemma_sai_frame valid cap j idx v
    else begin
      let k_j = index keys j in
      lemma_wfb_frame keys valid cap (2 * j + 1) lo k_j idx k v;
      lemma_wfb_frame keys valid cap (2 * j + 2) k_j hi idx k v
    end

#pop-options

/// subtree_all_invalid implies well_formed_bst for any bounds
let lemma_sai_implies_wfb
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat) (lo hi: int)
  : Lemma (requires subtree_all_invalid valid cap i)
          (ensures well_formed_bst keys valid cap i lo hi)
  = if i >= cap || i >= length keys || i >= length valid then ()
    else ()

(* ====================================================================
   Descendant relation and frame lemmas based on it
   ==================================================================== *)

#push-options "--fuel 2 --ifuel 1"

/// Is `desc` a descendant of `root` in a binary heap layout?
/// Bottom-up walk via parent pointers. Every position's parent is `(p-1)/2`.
let rec is_desc_of (root desc: nat)
  : Tot bool (decreases desc)
  = root = desc || (desc > root && is_desc_of root ((desc - 1) / 2))

/// If desc is a descendant of a child of root, it's a descendant of root
let rec lemma_desc_of_child (root desc: nat)
  : Lemma (requires is_desc_of (2 * root + 1) desc \/ is_desc_of (2 * root + 2) desc)
          (ensures is_desc_of root desc)
          (decreases desc)
  = if desc = root then ()
    else if desc = 2 * root + 1 || desc = 2 * root + 2 then ()
    else lemma_desc_of_child root ((desc - 1) / 2)

/// Left and right subtrees are disjoint
let rec lemma_desc_disjoint (i idx: nat)
  : Lemma (requires is_desc_of (2 * i + 1) idx /\ is_desc_of (2 * i + 2) idx)
          (ensures False)
          (decreases idx)
  = if idx = 2 * i + 1 then ()
    else if idx = 2 * i + 2 then ()
    else lemma_desc_disjoint i ((idx - 1) / 2)

/// A descendant of root (but not root itself) is a descendant of exactly one child
let rec lemma_desc_split (root idx: nat)
  : Lemma (requires is_desc_of root idx /\ root <> idx)
          (ensures is_desc_of (2 * root + 1) idx \/ is_desc_of (2 * root + 2) idx)
          (decreases idx)
  = let parent = (idx - 1) / 2 in
    if parent = root then ()
    else begin
      lemma_desc_split root parent
    end

/// Transitivity: if b is a descendant of a, and c is a descendant of b,
/// then c is a descendant of a.
let rec lemma_desc_of_trans (a b c: nat)
  : Lemma (requires is_desc_of a b /\ is_desc_of b c)
          (ensures is_desc_of a c)
          (decreases c)
  = if b = c then ()
    else lemma_desc_of_trans a b ((c - 1) / 2)

/// is_desc_of implies desc >= root
let rec lemma_desc_of_ge (root desc: nat)
  : Lemma (requires is_desc_of root desc)
          (ensures desc >= root)
          (decreases desc)
  = if root = desc then ()
    else lemma_desc_of_ge root ((desc - 1) / 2)

/// Frame: subtree_all_invalid unchanged by Seq.upd at non-descendant idx
let rec lemma_sai_frame_desc (valid: seq bool) (cap j idx: nat) (v: bool)
  : Lemma (requires ~(is_desc_of j idx) /\ idx < length valid)
          (ensures subtree_all_invalid valid cap j == 
                   subtree_all_invalid (upd valid idx v) cap j)
          (decreases (if j < cap then cap - j else 0))
  = if j >= cap || j >= length valid then ()
    else begin
      move_requires (lemma_desc_of_child j) idx;
      lemma_sai_frame_desc valid cap (2 * j + 1) idx v;
      lemma_sai_frame_desc valid cap (2 * j + 2) idx v
    end

/// Frame: well_formed_bst unchanged by Seq.upd at non-descendant idx
let rec lemma_wfb_frame_desc 
  (keys: seq int) (valid: seq bool) (cap j: nat) (lo hi: int) (idx: nat) (k: int) (v: bool)
  : Lemma (requires ~(is_desc_of j idx) /\ idx < length keys /\ idx < length valid)
          (ensures well_formed_bst keys valid cap j lo hi == 
                   well_formed_bst (upd keys idx k) (upd valid idx v) cap j lo hi)
          (decreases (if j < cap then cap - j else 0))
  = if j >= cap || j >= length keys || j >= length valid then ()
    else begin
      move_requires (lemma_desc_of_child j) idx;
      if not (index valid j) then
        lemma_sai_frame_desc valid cap j idx v
      else begin
        let k_j = index keys j in
        lemma_wfb_frame_desc keys valid cap (2 * j + 1) lo k_j idx k v;
        lemma_wfb_frame_desc keys valid cap (2 * j + 2) k_j hi idx k v
      end
    end

#pop-options

// =======================================================================
// BST search path and insertion preservation
// =======================================================================

/// Following BST key comparisons from position `i` reaches position `idx`
let rec bst_search_reaches
  (keys: seq int) (valid: seq bool) (cap: nat) (i idx: nat) (key_val: int)
  : Tot bool (decreases (if i < cap then cap - i else 0))
  = i < cap && i < length keys && i < length valid &&
    (i = idx ||
     (index valid i &&
      ((key_val < index keys i && bst_search_reaches keys valid cap (2 * i + 1) idx key_val) ||
       (key_val > index keys i && bst_search_reaches keys valid cap (2 * i + 2) idx key_val))))

/// BST search reaches implies descendant relationship
let rec lemma_bsr_implies_desc
  (keys: seq int) (valid: seq bool) (cap: nat) (i idx: nat) (key_val: int)
  : Lemma
    (requires bst_search_reaches keys valid cap i idx key_val)
    (ensures is_desc_of i idx)
    (decreases (if i < cap then cap - i else 0))
  = if i = idx then ()
    else begin
      let k_i = index keys i in
      if key_val < k_i then begin
        lemma_bsr_implies_desc keys valid cap (2 * i + 1) idx key_val;
        lemma_desc_of_child i idx
      end else begin
        lemma_bsr_implies_desc keys valid cap (2 * i + 2) idx key_val;
        lemma_desc_of_child i idx
      end
    end

/// If search reaches `j` and key < keys[j], search also reaches left child of j
#push-options "--fuel 2 --ifuel 1"
let rec lemma_bsr_extend_left
  (keys: seq int) (valid: seq bool) (cap: nat) (i j: nat) (key_val: int)
  : Lemma
    (requires
      bst_search_reaches keys valid cap i j key_val /\
      j < cap /\ j < length keys /\ j < length valid /\
      length keys >= cap /\ length valid >= cap /\
      index valid j /\
      key_val < index keys j /\
      2 * j + 1 < cap)
    (ensures bst_search_reaches keys valid cap i (2 * j + 1) key_val)
    (decreases (if i < cap then cap - i else 0))
  = if i = j then begin
      assert (2 * j + 1 < length keys /\ 2 * j + 1 < length valid);
      assert (bst_search_reaches keys valid cap (2 * j + 1) (2 * j + 1) key_val)
    end else begin
      let k_i = index keys i in
      if key_val < k_i then
        lemma_bsr_extend_left keys valid cap (2 * i + 1) j key_val
      else
        lemma_bsr_extend_left keys valid cap (2 * i + 2) j key_val
    end
#pop-options

/// Same for right child
#push-options "--fuel 2 --ifuel 1"
let rec lemma_bsr_extend_right
  (keys: seq int) (valid: seq bool) (cap: nat) (i j: nat) (key_val: int)
  : Lemma
    (requires
      bst_search_reaches keys valid cap i j key_val /\
      j < cap /\ j < length keys /\ j < length valid /\
      length keys >= cap /\ length valid >= cap /\
      index valid j /\
      key_val > index keys j /\
      2 * j + 2 < cap)
    (ensures bst_search_reaches keys valid cap i (2 * j + 2) key_val)
    (decreases (if i < cap then cap - i else 0))
  = if i = j then begin
      assert (2 * j + 2 < length keys /\ 2 * j + 2 < length valid);
      assert (bst_search_reaches keys valid cap (2 * j + 2) (2 * j + 2) key_val)
    end else begin
      let k_i = index keys i in
      if key_val < k_i then
        lemma_bsr_extend_right keys valid cap (2 * i + 1) j key_val
      else
        lemma_bsr_extend_right keys valid cap (2 * i + 2) j key_val
    end
#pop-options

/// Insertion at invalid position preserves well_formed_bst
///
/// Key lemma for BST insert: if `idx` is reachable by BST search from `i`
/// and `idx` is currently invalid, then writing `key_val` at `idx` and
/// marking it valid preserves the `well_formed_bst` invariant.
#push-options "--fuel 2 --ifuel 1"
let rec lemma_insert_wfb
  (keys: seq int) (valid: seq bool) (cap: nat)
  (i: nat) (lo hi: int) (idx: nat) (key_val: int)
  : Lemma
    (requires
      well_formed_bst keys valid cap i lo hi /\
      idx < cap /\ idx < length keys /\ idx < length valid /\
      length keys == length valid /\ length keys >= cap /\
      index valid idx == false /\
      bst_search_reaches keys valid cap i idx key_val /\
      lo < key_val /\ key_val < hi)
    (ensures
      well_formed_bst (upd keys idx key_val) (upd valid idx true) cap i lo hi)
    (decreases (if i < cap then cap - i else 0))
  = let keys' = upd keys idx key_val in
    let valid' = upd valid idx true in
    if i = idx then begin
      // Inserting at this position.
      // well_formed_bst keys valid cap idx lo hi = subtree_all_invalid valid cap idx
      // (since valid[idx] = false)
      // After update: valid'[idx] = true, keys'[idx] = key_val
      // Need: lo < key_val < hi (have it)
      //   AND well_formed_bst keys' valid' cap (2*idx+1) lo key_val
      //   AND well_formed_bst keys' valid' cap (2*idx+2) key_val hi

      // For left child (2*idx+1):
      // idx < 2*idx+1 always (for nat: 2*idx+1 >= idx+1 > idx)
      lemma_sai_frame valid cap (2 * idx + 1) idx true;
      lemma_sai_implies_wfb keys valid cap (2 * idx + 1) lo key_val;
      lemma_wfb_frame keys valid cap (2 * idx + 1) lo key_val idx key_val true;

      // For right child (2*idx+2): similarly idx < 2*idx+2
      lemma_sai_frame valid cap (2 * idx + 2) idx true;
      lemma_sai_implies_wfb keys valid cap (2 * idx + 2) key_val hi;
      lemma_wfb_frame keys valid cap (2 * idx + 2) key_val hi idx key_val true
    end else begin
      // i <> idx, follow BST search path
      // bst_search_reaches with i <> idx gives valid[i] = true
      let k_i = index keys i in
      assert (index valid i == true);
      assert (index valid' i == index valid i);
      assert (index keys' i == index keys i);

      if key_val < k_i then begin
        // Go left: bsr (2*i+1) idx key_val
        lemma_insert_wfb keys valid cap (2 * i + 1) lo k_i idx key_val;

        // Frame right subtree: idx is descendant of left child, not right
        lemma_bsr_implies_desc keys valid cap (2 * i + 1) idx key_val;
        // is_desc_of (2*i+1) idx AND is_desc_of (2*i+2) idx ==> False
        // So ~(is_desc_of (2*i+2) idx)
        Classical.move_requires (lemma_desc_disjoint i) idx;
        assert (~(is_desc_of (2 * i + 2) idx));
        lemma_wfb_frame_desc keys valid cap (2 * i + 2) k_i hi idx key_val true
      end else begin
        // Go right: bsr (2*i+2) idx key_val
        lemma_insert_wfb keys valid cap (2 * i + 2) k_i hi idx key_val;

        // Frame left subtree: idx is descendant of right child, not left
        lemma_bsr_implies_desc keys valid cap (2 * i + 2) idx key_val;
        Classical.move_requires (lemma_desc_disjoint i) idx;
        assert (~(is_desc_of (2 * i + 1) idx));
        lemma_wfb_frame_desc keys valid cap (2 * i + 1) lo k_i idx key_val true
      end
    end
#pop-options

/// After inserting key_val at position idx (reached by BST search from i),
/// key_val is in the subtree rooted at i.
///
/// Proof: structural induction on the BST search path.
/// Base case (i = idx): valid'[idx] = true and keys'[idx] = key_val,
///   so key_in_subtree holds trivially.
/// Inductive case (i <> idx): bst_search_reaches gives valid[i] = true
///   and routes to left or right child. By induction, key_val is in the
///   child subtree. Since valid'[i] = valid[i] = true, key_in_subtree
///   at i follows from the disjunction in its definition.
let rec lemma_insert_key_in_subtree
  (keys: seq int) (valid: seq bool) (cap: nat)
  (i idx: nat) (key_val: int)
  : Lemma
    (requires
      bst_search_reaches keys valid cap i idx key_val /\
      idx < length keys /\ idx < length valid /\
      length keys == length valid /\ length keys >= cap /\
      index valid idx == false)
    (ensures
      key_in_subtree (upd keys idx key_val) (upd valid idx true) cap i key_val)
    (decreases (if i < cap then cap - i else 0))
  = if i = idx then ()
    else begin
      // bst_search_reaches with i <> idx gives: valid[i] = true
      // and (key_val < keys[i] ==> bsr (2i+1) idx) || (key_val > keys[i] ==> bsr (2i+2) idx)
      let k_i = index keys i in
      if key_val < k_i then
        lemma_insert_key_in_subtree keys valid cap (2 * i + 1) idx key_val
      else
        lemma_insert_key_in_subtree keys valid cap (2 * i + 2) idx key_val
    end

(* ====================================================================
   Lemmas for BST deletion
   ==================================================================== *)

/// If subtree_all_invalid holds at root, then all descendants are invalid.
/// Proof by top-down induction on the tree structure (decreasing cap - root).
/// At each step, use lemma_desc_split to determine which child subtree
/// the descendant belongs to, then recurse into that subtree.
#push-options "--fuel 2 --ifuel 1"
let rec lemma_sai_desc
  (valid: seq bool) (cap root desc: nat)
  : Lemma
    (requires
      subtree_all_invalid valid cap root /\
      is_desc_of root desc /\
      desc < cap /\ desc < length valid)
    (ensures index valid desc == false)
    (decreases (if root < cap then cap - root else 0))
  = if root = desc then ()
    else begin
      // root <> desc and is_desc_of root desc, so desc > root.
      // Therefore root < desc < cap and root < desc < length valid.
      // subtree_all_invalid valid cap root gives:
      //   valid[root] == false /\
      //   subtree_all_invalid valid cap (2*root+1) /\
      //   subtree_all_invalid valid cap (2*root+2)
      lemma_desc_split root desc;
      if is_desc_of (2 * root + 1) desc then
        lemma_sai_desc valid cap (2 * root + 1) desc
      else
        lemma_sai_desc valid cap (2 * root + 2) desc
    end
#pop-options

/// Frame: well_formed_bst unchanged by valid-only update at non-descendant.
/// Derived from lemma_wfb_frame_desc by updating keys with the same value
/// (a no-op), then using Seq.equal to recover the original keys sequence.
let lemma_wfb_frame_valid_desc
  (keys: seq int) (valid: seq bool) (cap j del_idx: nat) (lo hi: int) (v: bool)
  : Lemma
    (requires ~(is_desc_of j del_idx) /\ del_idx < length keys /\ del_idx < length valid)
    (ensures well_formed_bst keys valid cap j lo hi ==
             well_formed_bst keys (upd valid del_idx v) cap j lo hi)
  = lemma_wfb_frame_desc keys valid cap j lo hi del_idx (index keys del_idx) v;
    // lemma_wfb_frame_desc establishes:
    //   wfb keys valid ... == wfb (upd keys del_idx (index keys del_idx)) (upd valid del_idx v) ...
    // Show the keys update is a no-op:
    assert (Seq.equal (upd keys del_idx (index keys del_idx)) keys)
    // By congruence: wfb keys valid ... == wfb keys (upd valid del_idx v) ...

/// Marking a leaf node as invalid preserves well_formed_bst.
///
/// Base case (i == del_idx): After setting valid[del_idx] = false, need
/// subtree_all_invalid at del_idx. Children are either OOB or already invalid
/// (leaf precondition), so frame their SAI through the update.
///
/// Recursive case (i < del_idx): First show valid[i] must be true (otherwise
/// subtree_all_invalid at i and lemma_sai_desc give valid[del_idx] = false,
/// contradiction). Then split into child subtrees: recurse on the subtree
/// containing del_idx, frame the other using lemma_wfb_frame_valid_desc.
#push-options "--fuel 2 --ifuel 1"
let rec lemma_leaf_delete_wfb
  (keys: seq int) (valid: seq bool) (cap: nat)
  (i: nat) (lo hi: int) (del_idx: nat)
  : Lemma
    (requires
      well_formed_bst keys valid cap i lo hi /\
      del_idx < cap /\ del_idx < length keys /\ del_idx < length valid /\
      length keys == length valid /\ length keys >= cap /\
      index valid del_idx == true /\
      is_desc_of i del_idx /\
      (2 * del_idx + 1 >= cap \/ 2 * del_idx + 1 >= length valid \/
       index valid (2 * del_idx + 1) == false) /\
      (2 * del_idx + 2 >= cap \/ 2 * del_idx + 2 >= length valid \/
       index valid (2 * del_idx + 2) == false))
    (ensures
      well_formed_bst keys (upd valid del_idx false) cap i lo hi)
    (decreases (if i < cap then cap - i else 0))
  = let valid' = upd valid del_idx false in
    let left_del = 2 * del_idx + 1 in
    let right_del = 2 * del_idx + 2 in
    if i = del_idx then begin
      // valid[del_idx] = true, so wfb gives lo < keys[del_idx] < hi and child wfbs
      // After update: valid'[del_idx] = false, so need subtree_all_invalid valid' cap del_idx
      // i.e., valid'[del_idx] == false /\ sai valid' cap left_del /\ sai valid' cap right_del
      //
      // For each child: if OOB, sai is True; if in-bounds, child is invalid (leaf),
      // so original wfb gives sai at child, and lemma_sai_frame_desc frames it.
      if left_del < cap && left_del < length valid then
        lemma_sai_frame_desc valid cap left_del del_idx false;
      if right_del < cap && right_del < length valid then
        lemma_sai_frame_desc valid cap right_del del_idx false
    end else begin
      // i <> del_idx, so del_idx > i (from is_desc_of), meaning i < del_idx < cap
      // Show valid[i] must be true: if false, wfb gives subtree_all_invalid at i,
      // then lemma_sai_desc gives valid[del_idx] == false, contradicting precondition
      if not (index valid i) then
        lemma_sai_desc valid cap i del_idx
      else begin
        let k_i = index keys i in
        let left = 2 * i + 1 in
        let right = 2 * i + 2 in
        // del_idx is a descendant of exactly one child
        lemma_desc_split i del_idx;
        if is_desc_of left del_idx then begin
          // Recurse on left subtree (contains del_idx)
          lemma_leaf_delete_wfb keys valid cap left lo k_i del_idx;
          // Frame right subtree (del_idx not a descendant of right)
          Classical.move_requires (lemma_desc_disjoint i) del_idx;
          lemma_wfb_frame_valid_desc keys valid cap right del_idx k_i hi false
        end else begin
          // Recurse on right subtree (contains del_idx)
          lemma_leaf_delete_wfb keys valid cap right k_i hi del_idx;
          // Frame left subtree (del_idx not a descendant of left)
          Classical.move_requires (lemma_desc_disjoint i) del_idx;
          lemma_wfb_frame_valid_desc keys valid cap left del_idx lo k_i false
        end
      end
    end
#pop-options

/// Every position is a descendant of the root (position 0).
let rec lemma_is_desc_of_root (n: nat)
  : Lemma (ensures is_desc_of 0 n) (decreases n)
  = if n = 0 then () else lemma_is_desc_of_root ((n - 1) / 2)

(* ====================================================================
   Additional lemmas for BST deletion (non-leaf cases)
   ==================================================================== *)

/// Any valid descendant in a well_formed_bst subtree has key within bounds.
#push-options "--fuel 2 --ifuel 1"
let rec lemma_wfb_valid_desc_in_bounds
  (keys: seq int) (valid: seq bool) (cap: nat)
  (i desc: nat) (lo hi: int)
  : Lemma
    (requires
      well_formed_bst keys valid cap i lo hi /\
      is_desc_of i desc /\
      desc < cap /\ desc < length keys /\ desc < length valid /\
      index valid desc == true)
    (ensures lo < index keys desc /\ index keys desc < hi)
    (decreases (if i < cap then cap - i else 0))
  = if i = desc then ()
    else begin
      if not (index valid i) then
        lemma_sai_desc valid cap i desc
      else begin
        let k_i = index keys i in
        lemma_desc_split i desc;
        if is_desc_of (2 * i + 1) desc then
          lemma_wfb_valid_desc_in_bounds keys valid cap (2 * i + 1) desc lo k_i
        else
          lemma_wfb_valid_desc_in_bounds keys valid cap (2 * i + 2) desc k_i hi
      end
    end
#pop-options

/// Widening the upper bound preserves well_formed_bst.
#push-options "--fuel 2 --ifuel 1"
let rec lemma_wfb_widen_upper
  (keys: seq int) (valid: seq bool) (cap: nat)
  (i: nat) (lo hi1 hi2: int)
  : Lemma
    (requires well_formed_bst keys valid cap i lo hi1 /\ hi1 <= hi2)
    (ensures well_formed_bst keys valid cap i lo hi2)
    (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then ()
    else if not (index valid i) then ()
    else begin
      let k = index keys i in
      lemma_wfb_widen_upper keys valid cap (2 * i + 2) k hi1 hi2
    end
#pop-options

/// Widening the lower bound preserves well_formed_bst.
#push-options "--fuel 2 --ifuel 1"
let rec lemma_wfb_widen_lower
  (keys: seq int) (valid: seq bool) (cap: nat)
  (i: nat) (lo1 lo2: int) (hi: int)
  : Lemma
    (requires well_formed_bst keys valid cap i lo1 hi /\ lo2 <= lo1)
    (ensures well_formed_bst keys valid cap i lo2 hi)
    (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then ()
    else if not (index valid i) then ()
    else begin
      let k = index keys i in
      lemma_wfb_widen_lower keys valid cap (2 * i + 1) lo1 lo2 k
    end
#pop-options

(* ====================================================================
   Left-spine predicate: min_idx is reachable from root by always
   following left children, with all intermediate nodes valid.
   This characterizes the path taken by tree_minimum.
   ==================================================================== *)

/// min_idx is on the left spine of the subtree rooted at root.
let rec is_left_spine (root min_idx: nat) (valid: seq bool) (cap: nat)
  : Tot bool (decreases (if root < cap then cap - root else 0))
  = if root >= cap || root >= length valid then false
    else root = min_idx ||
         (index valid root && is_left_spine (2 * root + 1) min_idx valid cap)

/// Extending a left spine by one left step.
#push-options "--fuel 2 --ifuel 1"
let rec lemma_left_spine_extend
  (root mid: nat) (valid: seq bool) (cap: nat)
  : Lemma
    (requires
      is_left_spine root mid valid cap /\
      mid < cap /\ mid < length valid /\
      index valid mid /\
      2 * mid + 1 < cap /\ 2 * mid + 1 < length valid)
    (ensures is_left_spine root (2 * mid + 1) valid cap)
    (decreases (if root < cap then cap - root else 0))
  = if root = mid then ()
    else lemma_left_spine_extend (2 * root + 1) mid valid cap
#pop-options

/// A node on the left spine is a descendant of root.
#push-options "--fuel 2 --ifuel 1"
let rec lemma_left_spine_is_desc
  (root min_idx: nat) (valid: seq bool) (cap: nat)
  : Lemma
    (requires is_left_spine root min_idx valid cap)
    (ensures is_desc_of root min_idx)
    (decreases (if root < cap then cap - root else 0))
  = if root = min_idx then ()
    else begin
      lemma_left_spine_is_desc (2 * root + 1) min_idx valid cap;
      lemma_desc_of_child root min_idx
    end
#pop-options

/// On the left spine, min_idx is always in the left subtree of any ancestor.
#push-options "--fuel 2 --ifuel 1"
let lemma_left_spine_in_left
  (root min_idx: nat) (valid: seq bool) (cap: nat)
  : Lemma
    (requires is_left_spine root min_idx valid cap /\ root <> min_idx)
    (ensures
      root < cap /\ root < length valid /\
      index valid root /\
      is_left_spine (2 * root + 1) min_idx valid cap)
  = ()
#pop-options

(* ====================================================================
   Successor swap + leaf delete preserves well_formed_bst
   
   This is the key lemma for the two-children delete case.
   After finding the successor (minimum of right subtree), we:
   1. Copy successor's key to the deleted position
   2. Mark the successor as invalid (it's a leaf)
   
   We prove this preserves well_formed_bst by walking from the root:
   - Above del_idx: frame both updates
   - At del_idx: left subtree widens upper bound, right subtree
     uses delete_min_narrow
   - Below del_idx in right subtree: handled by delete_min_narrow
   ==================================================================== *)

/// After deleting the minimum (a leaf on the left spine) from a subtree,
/// well_formed_bst holds with the lower bound narrowed to the minimum's key.
#push-options "--fuel 2 --ifuel 1"
let rec lemma_delete_min_narrow_wfb
  (keys: seq int) (valid: seq bool) (cap: nat)
  (i: nat) (lo hi: int) (min_idx: nat)
  : Lemma
    (requires
      well_formed_bst keys valid cap i lo hi /\
      min_idx < cap /\ min_idx < length keys /\ min_idx < length valid /\
      length keys == length valid /\ length keys >= cap /\
      index valid min_idx == true /\
      is_left_spine i min_idx valid cap /\
      // min_idx is a leaf
      (2 * min_idx + 1 >= cap \/ 2 * min_idx + 1 >= length valid \/
       index valid (2 * min_idx + 1) == false) /\
      (2 * min_idx + 2 >= cap \/ 2 * min_idx + 2 >= length valid \/
       index valid (2 * min_idx + 2) == false) /\
      lo < index keys min_idx /\ index keys min_idx < hi)
    (ensures
      well_formed_bst keys (upd valid min_idx false) cap i (index keys min_idx) hi)
    (decreases (if i < cap then cap - i else 0))
  = let valid' = upd valid min_idx false in
    if i >= cap || i >= length keys || i >= length valid then ()
    else if i = min_idx then begin
      // After deletion: valid'[min_idx] = false → need subtree_all_invalid
      let left_min = 2 * min_idx + 1 in
      let right_min = 2 * min_idx + 2 in
      if left_min < cap && left_min < length valid then
        lemma_sai_frame_desc valid cap left_min min_idx false;
      if right_min < cap && right_min < length valid then
        lemma_sai_frame_desc valid cap right_min min_idx false
    end else begin
      // i ≠ min_idx: by is_left_spine, min_idx is in the LEFT subtree
      // valid[i] must be true (from is_left_spine definition)
      let k_i = index keys i in
      let left = 2 * i + 1 in
      let right = 2 * i + 2 in
      // Derive bounds: keys[min_idx] is in (lo, k_i) since it's in the left subtree
      lemma_left_spine_is_desc (2 * i + 1) min_idx valid cap;
      lemma_wfb_valid_desc_in_bounds keys valid cap left min_idx lo k_i;
      // Left subtree: recurse (min_idx is on the left spine of left child)
      lemma_delete_min_narrow_wfb keys valid cap left lo k_i min_idx;
      // Right subtree: min_idx is NOT in right subtree → frame
      Classical.move_requires (lemma_desc_disjoint i) min_idx;
      lemma_wfb_frame_valid_desc keys valid cap right min_idx k_i hi false
    end
#pop-options

/// Explicitly construct well_formed_bst at a valid node from its components.
#push-options "--fuel 2 --ifuel 1"
let lemma_wfb_node
  (keys: seq int) (valid: seq bool) (cap i: nat) (lo hi: int)
  : Lemma
    (requires
      i < cap /\ i < length keys /\ i < length valid /\
      index valid i == true /\
      lo < index keys i /\ index keys i < hi /\
      well_formed_bst keys valid cap (2 * i + 1) lo (index keys i) /\
      well_formed_bst keys valid cap (2 * i + 2) (index keys i) hi)
    (ensures well_formed_bst keys valid cap i lo hi)
  = ()
#pop-options

/// Frame: keys-only update at non-descendant preserves well_formed_bst.
#push-options "--fuel 2 --ifuel 1"
let lemma_wfb_frame_keys_desc
  (keys: seq int) (valid: seq bool) (cap j: nat) (lo hi: int) (idx: nat) (k: int)
  : Lemma
    (requires ~(is_desc_of j idx) /\ idx < length keys /\ idx < length valid)
    (ensures well_formed_bst keys valid cap j lo hi ==
             well_formed_bst (upd keys idx k) valid cap j lo hi)
  = lemma_wfb_frame_desc keys valid cap j lo hi idx k (index valid idx);
    assert (Seq.equal (upd valid idx (index valid idx)) valid)
#pop-options

/// Combined successor swap and leaf deletion preserves well_formed_bst.
///
/// Given a well-formed BST, at position del_idx with two children:
///   succ_idx = minimum of right subtree (on left spine of right child)
///   After: keys[del_idx] := keys[succ_idx], valid[succ_idx] := false
///   Proves: well_formed_bst is preserved
#push-options "--fuel 2 --ifuel 1"
let rec lemma_successor_swap_delete_wfb
  (keys: seq int) (valid: seq bool) (cap: nat)
  (i: nat) (lo hi: int) (del_idx succ_idx: nat)
  : Lemma
    (requires
      well_formed_bst keys valid cap i lo hi /\
      del_idx < cap /\ del_idx < length keys /\ del_idx < length valid /\
      succ_idx < cap /\ succ_idx < length keys /\ succ_idx < length valid /\
      length keys == length valid /\ length keys >= cap /\
      index valid del_idx == true /\
      index valid succ_idx == true /\
      del_idx <> succ_idx /\
      is_desc_of i del_idx /\
      // succ_idx is the minimum of the right subtree of del_idx
      is_left_spine (2 * del_idx + 2) succ_idx valid cap /\
      // succ is a leaf
      (2 * succ_idx + 1 >= cap \/ 2 * succ_idx + 1 >= length valid \/
       index valid (2 * succ_idx + 1) == false) /\
      (2 * succ_idx + 2 >= cap \/ 2 * succ_idx + 2 >= length valid \/
       index valid (2 * succ_idx + 2) == false))
    (ensures
      well_formed_bst (upd keys del_idx (index keys succ_idx))
                      (upd valid succ_idx false) cap i lo hi)
    (decreases (if i < cap then cap - i else 0))
  = let keys' = upd keys del_idx (index keys succ_idx) in
    let valid' = upd valid succ_idx false in
    let succ_key = index keys succ_idx in
    if i >= cap || i >= length keys || i >= length valid then ()
    else begin
      // valid[i] must be true (otherwise sai gives valid[del_idx] = false)
      if not (index valid i) then
        lemma_sai_desc valid cap i del_idx
      else begin
        let k_i = index keys i in
        let left = 2 * i + 1 in
        let right = 2 * i + 2 in
        if i = del_idx then begin
          // === AT THE DELETION POINT ===
          // keys'[del_idx] = succ_key, valid'[del_idx] = true (unchanged)

          // Establish succ_key bounds: succ is in right subtree
          lemma_left_spine_is_desc (2 * del_idx + 2) succ_idx valid cap;
          lemma_desc_of_child del_idx succ_idx;
          lemma_wfb_valid_desc_in_bounds keys valid cap right succ_idx k_i hi;
          // Now: k_i < succ_key < hi, and lo < k_i, so lo < succ_key < hi

          // succ_idx is in right subtree of del_idx, disjoint from left
          Classical.move_requires (lemma_desc_disjoint del_idx) succ_idx;

          // --- LEFT SUBTREE: wfb keys' valid' cap left lo succ_key ---
          // Step 1: Frame valid update at succ_idx (not in left subtree)
          lemma_wfb_frame_valid_desc keys valid cap left succ_idx lo k_i false;
          // Now: wfb keys valid' cap left lo k_i
          // Step 2: Widen upper bound from k_i to succ_key
          lemma_wfb_widen_upper keys valid' cap left lo k_i succ_key;
          // Now: wfb keys valid' cap left lo succ_key
          // Step 3: Frame keys update at del_idx (del_idx not desc of left)
          lemma_wfb_frame_keys_desc keys valid' cap left lo succ_key del_idx succ_key;
          // Now: wfb keys' valid' cap left lo succ_key ✓

          // --- RIGHT SUBTREE: wfb keys' valid' cap right succ_key hi ---
          // Step 1: Delete min (succ) from right subtree and narrow lower bound
          lemma_delete_min_narrow_wfb keys valid cap right k_i hi succ_idx;
          // Now: wfb keys valid' cap right succ_key hi
          // Step 2: Frame keys update at del_idx (del_idx not desc of right)
          lemma_wfb_frame_keys_desc keys valid' cap right succ_key hi del_idx succ_key;
          // Now: wfb keys' valid' cap right succ_key hi ✓

          // Assemble: at del_idx, valid is still true and key is succ_key
          assert (index valid' del_idx == true);
          assert (index keys' del_idx == succ_key);
          assert (lo < succ_key /\ succ_key < hi);
          lemma_wfb_node keys' valid' cap del_idx lo hi
        end else begin
          // === ABOVE THE DELETION POINT ===
          // i ≠ del_idx, so del_idx > i (from is_desc_of i del_idx)
          // succ_idx > del_idx (succ is deeper in right subtree)
          // Therefore i ≠ succ_idx, so valid'[i] = valid[i] = true, keys'[i] = keys[i] = k_i
          lemma_desc_of_ge i del_idx;
          lemma_left_spine_is_desc (2 * del_idx + 2) succ_idx valid cap;
          lemma_desc_of_ge (2 * del_idx + 2) succ_idx;
          assert (del_idx > i);
          assert (succ_idx >= 2 * del_idx + 2);
          assert (succ_idx > i);
          assert (index valid' i == true);
          assert (index keys' i == k_i);

          // del_idx in exactly one child subtree; succ_idx is descendant of del_idx
          lemma_desc_split i del_idx;
          lemma_desc_of_child del_idx succ_idx;
          if is_desc_of left del_idx then begin
            // Recurse on left subtree
            lemma_successor_swap_delete_wfb keys valid cap left lo k_i del_idx succ_idx;
            // Frame right subtree: neither del_idx nor succ_idx is a descendant
            Classical.move_requires (lemma_desc_disjoint i) del_idx;
            lemma_desc_of_trans left del_idx succ_idx;
            Classical.move_requires (lemma_desc_disjoint i) succ_idx;
            // Step 1: Frame keys update on right subtree
            lemma_wfb_frame_keys_desc keys valid cap right k_i hi del_idx succ_key;
            // Now: wfb keys' valid cap right k_i hi
            // Step 2: Frame valid update on right subtree (using keys')
            lemma_wfb_frame_valid_desc keys' valid cap right succ_idx k_i hi false;
            // Now: wfb keys' valid' cap right k_i hi
            lemma_wfb_node keys' valid' cap i lo hi
          end else begin
            // Recurse on right subtree
            lemma_successor_swap_delete_wfb keys valid cap right k_i hi del_idx succ_idx;
            // Frame left subtree
            Classical.move_requires (lemma_desc_disjoint i) del_idx;
            lemma_desc_of_trans right del_idx succ_idx;
            Classical.move_requires (lemma_desc_disjoint i) succ_idx;
            // Step 1: Frame keys update on left subtree
            lemma_wfb_frame_keys_desc keys valid cap left lo k_i del_idx succ_key;
            // Now: wfb keys' valid cap left lo k_i
            // Step 2: Frame valid update on left subtree (using keys')
            lemma_wfb_frame_valid_desc keys' valid cap left succ_idx lo k_i false;
            // Now: wfb keys' valid' cap left lo k_i
            lemma_wfb_node keys' valid' cap i lo hi
          end
        end
      end
    end
#pop-options
