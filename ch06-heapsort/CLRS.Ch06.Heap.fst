(*
   CLRS Chapter 6: Heapsort Implementation in Pulse
   
   Implements the real CLRS heapsort algorithm:
   1. BUILD-MAX-HEAP: bottom-up heapification
   2. Extract-max loop: swap root (max) to end, shrink heap, MAX-HEAPIFY
   
   Uses max-heap property on int arrays with parent >= children.
   Heap predicates and sift-down lemmas follow the structure of
   Pulse.Lib.PriorityQueue (adapted for max-heap on int).
   
   Proves:
   1. The result is sorted
   2. The result is a permutation of the input
   
   NO admits. NO assumes.
*)

module CLRS.Ch06.Heap
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module Classical = FStar.Classical

// ========== Heap index functions ==========

//SNIPPET_START: heap_indices
let parent_idx (i:nat{i > 0}) : nat = (i - 1) / 2
let left_idx (i:nat) : nat = op_Multiply 2 i + 1
let right_idx (i:nat) : nat = op_Multiply 2 i + 2
//SNIPPET_END: heap_indices

let parent_idx_lt (i:nat{i > 0}) : Lemma (parent_idx i < i) = ()

let bad_is_child_of_parent (bad:nat{bad > 0})
  : Lemma (left_idx (parent_idx bad) = bad \/ right_idx (parent_idx bad) = bad)
  = ()

let left_idx_inj (i j:nat) : Lemma (requires left_idx i = j /\ j > 0) (ensures parent_idx j = i) = ()
let right_idx_inj (i j:nat) : Lemma (requires right_idx i = j /\ j > 0) (ensures parent_idx j = i) = ()
let left_neq_right (i j:nat) : Lemma (left_idx i <> right_idx j) = ()

let left_idx_parent (bad:nat{bad > 0}) (i:nat)
  : Lemma (requires left_idx i = bad) (ensures i = parent_idx bad) = ()
let right_idx_parent (bad:nat{bad > 0}) (i:nat)
  : Lemma (requires right_idx i = bad) (ensures i = parent_idx bad) = ()

// ========== Max-heap predicates ==========
// Defined over a prefix of length `len` of the sequence

//SNIPPET_START: heap_predicates
// Node i satisfies max-heap with children: s[i] >= s[children] (within heap_size)
let heap_down_at (s:Seq.seq int) (len:nat) (i:nat{i < len /\ len <= Seq.length s}) : prop =
  (left_idx i < len ==> Seq.index s i >= Seq.index s (left_idx i)) /\
  (right_idx i < len ==> Seq.index s i >= Seq.index s (right_idx i))

// Full max-heap over prefix of length len
let is_max_heap (s:Seq.seq int) (len:nat{len <= Seq.length s}) : prop =
  forall (i:nat). i < len ==> heap_down_at s len i

// heap_down_at holds for all nodes from k to len-1, except possibly at bad
let almost_heaps_from (s:Seq.seq int) (len:nat{len <= Seq.length s}) 
  (k:nat) (bad:nat{bad < len}) : prop =
  bad >= k /\
  (forall (j:nat). k <= j /\ j < len /\ j <> bad ==> heap_down_at s len j)
//SNIPPET_END: heap_predicates

// heap_down_at holds for all nodes from k to len-1
let heaps_from (s:Seq.seq int) (len:nat{len <= Seq.length s}) (k:nat) : prop =
  forall (j:nat). k <= j /\ j < len ==> heap_down_at s len j

// ========== Core lemmas ==========

let heaps_from_to_almost (s:Seq.seq int) (len:nat{len <= Seq.length s}) 
  (k:nat) (bad:nat{bad < len})
  : Lemma (requires bad >= k /\ heaps_from s len (bad + 1))
          (ensures almost_heaps_from s len bad bad)
  = ()

let almost_to_full (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (k:nat) (bad:nat{bad < len})
  : Lemma (requires almost_heaps_from s len k bad /\ heap_down_at s len bad)
          (ensures heaps_from s len k)
  = ()

// ========== Sorted and permutation ==========

let sorted (s: Seq.seq int) =
  forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let suffix_sorted (s: Seq.seq int) (k: nat) : prop =
  k <= Seq.length s /\
  (forall (i j: nat). k <= i /\ i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j)

let prefix_le_suffix (s: Seq.seq int) (k: nat) : prop =
  k <= Seq.length s /\
  (forall (i j: nat). i < k /\ k <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j)

[@@"opaque_to_smt"]
let permutation (s1 s2: Seq.seq int) : prop = (SeqP.permutation int s1 s2)

let permutation_same_length (s1 s2 : Seq.seq int)
  : Lemma (requires permutation s1 s2)
          (ensures Seq.length s1 == Seq.length s2)
          [SMTPat (permutation s1 s2)]
  = reveal_opaque (`%permutation) (permutation s1 s2);
    SeqP.perm_len s1 s2

let permutation_refl (s: Seq.seq int)
  : Lemma (ensures permutation s s)
    [SMTPat (permutation s s)]
  = reveal_opaque (`%permutation) (permutation s s)

let compose_permutations (s1 s2 s3: Seq.seq int)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
    (ensures permutation s1 s3)
    [SMTPat (permutation s1 s2); SMTPat (permutation s2 s3)]
  = reveal_opaque (`%permutation) (permutation s1 s2);
    reveal_opaque (`%permutation) (permutation s2 s3);
    reveal_opaque (`%permutation) (permutation s1 s3);
    Seq.perm_len s1 s2;
    Seq.perm_len s1 s3;
    Seq.lemma_trans_perm s1 s2 s3 0 (Seq.length s1)

// ========== Swap ==========

let swap_seq (s:Seq.seq int) (i j:nat{i < Seq.length s /\ j < Seq.length s}) : Seq.seq int =
  Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i)

let swap_length (s:Seq.seq int) (i j:nat{i < Seq.length s /\ j < Seq.length s})
  : Lemma (Seq.length (swap_seq s i j) == Seq.length s) = ()

let swap_index_i (s:Seq.seq int) (i j:nat{i < Seq.length s /\ j < Seq.length s})
  : Lemma (Seq.index (swap_seq s i j) i == Seq.index s j) = ()

let swap_index_j (s:Seq.seq int) (i j:nat{i < Seq.length s /\ j < Seq.length s /\ i <> j})
  : Lemma (Seq.index (swap_seq s i j) j == Seq.index s i) = ()

let swap_index_other (s:Seq.seq int) (i j k:nat{i < Seq.length s /\ j < Seq.length s /\ k < Seq.length s /\ k <> i /\ k <> j})
  : Lemma (Seq.index (swap_seq s i j) k == Seq.index s k) = ()

let swap_is_permutation (s: Seq.seq int) (i j: nat)
  : Lemma (requires i < Seq.length s /\ j < Seq.length s)
          (ensures permutation s (swap_seq s i j))
  = reveal_opaque (`%permutation) (permutation s (swap_seq s i j));
    if i = j then
      Seq.lemma_eq_elim s (swap_seq s i j)
    else if i < j then (
      assert (Seq.equal (swap_seq s i j) (Seq.swap s i j));
      SeqP.lemma_swap_permutes s i j
    ) else (
      assert (Seq.equal (swap_seq s i j) (Seq.swap s j i));
      SeqP.lemma_swap_permutes s j i
    )

// ========== Sift-down swap lemma (max-heap, subtree version) ==========
// After swapping parent with larger child, almost_heaps_from shifts to the child

// Swap preserves heap_down_at for nodes outside {p, ch} that don't have p or ch as children
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let swap_preserves_heap_down_other (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (p:nat{p < len}) (ch:nat{ch < len /\ p <> ch})
  (j:nat{j < len /\ j <> p /\ j <> ch})
  : Lemma (requires 
            heap_down_at s len j /\
            left_idx j <> p /\ left_idx j <> ch /\
            right_idx j <> p /\ right_idx j <> ch)
          (ensures heap_down_at (swap_seq s p ch) len j)
  = swap_length s p ch;
    swap_index_other s p ch j;
    if left_idx j < len then swap_index_other s p ch (left_idx j);
    if right_idx j < len then swap_index_other s p ch (right_idx j)
#pop-options

// After swap at (p, ch): heap_down_at at p holds if ch is the largest child
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let swap_heap_down_at_parent (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (p:nat{p < len}) (ch:nat{ch < len /\ p <> ch})
  : Lemma (requires 
            (ch = left_idx p \/ ch = right_idx p) /\
            Seq.index s ch > Seq.index s p /\
            // ch is the largest child (or only child)
            (left_idx p < len /\ left_idx p <> ch ==> Seq.index s ch >= Seq.index s (left_idx p)) /\
            (right_idx p < len /\ right_idx p <> ch ==> Seq.index s ch >= Seq.index s (right_idx p)))
          (ensures heap_down_at (swap_seq s p ch) len p)
  = swap_length s p ch;
    swap_index_i s p ch;
    swap_index_j s p ch;
    // s'[p] = s[ch], s'[ch] = s[p]
    // Need: s'[p] >= s'[left_idx p] and s'[p] >= s'[right_idx p] (when they exist and < len)
    // Case: left_idx p = ch. Then s'[ch] = s[p]. s'[p] = s[ch] > s[p] = s'[ch]. ✓
    //   For right_idx p (the sibling): if it exists and < len, s'[right_idx p] = s[right_idx p]
    //   (since right_idx p <> p and right_idx p <> ch). s'[p] = s[ch] >= s[right_idx p] by precondition.
    // Case: right_idx p = ch. Symmetric.
    if ch = left_idx p then (
      // right_idx p is the sibling
      let rp = right_idx p in
      if rp < len then (
        // rp <> p (since rp = 2p+2 > p) and rp <> ch (since left <> right)
        left_neq_right p p;  // left_idx p <> right_idx p
        swap_index_other s p ch rp
      )
    ) else (
      // left_idx p is the sibling
      let lp = left_idx p in
      if lp < len then (
        left_neq_right p p;
        swap_index_other s p ch lp
      )
    )
#pop-options

// After swap, heap_down_at for j where j has p as a child (j = parent_idx p)
// Requires grandparent condition: s[j] >= s[ch]
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let swap_heap_down_at_grandparent (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (p:nat{p < len /\ p > 0}) (ch:nat{ch < len /\ p <> ch})
  (j:nat{j < len /\ j <> p /\ j <> ch /\ (left_idx j = p \/ right_idx j = p)})
  : Lemma (requires 
            heap_down_at s len j /\
            Seq.index s j >= Seq.index s ch /\
            left_idx j <> ch /\ right_idx j <> ch)
          (ensures heap_down_at (swap_seq s p ch) len j)
  = swap_length s p ch;
    swap_index_other s p ch j;
    // s'[j] = s[j], s'[p] = s[ch]
    // j has p as a child. The other child of j might exist.
    // Need: s'[j] >= s'[p] = s[ch] -- from precondition s[j] >= s[ch] ✓
    // Need: s'[j] >= s'[other_child]. other_child <> p, <> ch, so s'[other_child] = s[other_child]
    // From heap_down_at s len j: s[j] >= s[other_child] ✓
    if left_idx j = p then (
      swap_index_i s p ch; // not quite right, this is swap_index_i for indices p,ch
      // Actually: the swap is at positions p and ch
      // s'[left_idx j] = s'[p] = s[ch]
      // We need s'[j] >= s'[left j] i.e. s[j] >= s[ch], which we have
      if right_idx j < len then
        swap_index_other s p ch (right_idx j)
    ) else (
      // right_idx j = p
      if left_idx j < len then
        swap_index_other s p ch (left_idx j)
    )
#pop-options

// Main sift-down swap lemma for almost_heaps_from
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let sift_down_swap_lemma_from (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (k:nat) (p:nat{p < len /\ p >= k}) (ch:nat{ch < len /\ p <> ch})
  : Lemma (requires 
            almost_heaps_from s len k p /\
            (ch = left_idx p \/ ch = right_idx p) /\
            Seq.index s ch > Seq.index s p /\
            (left_idx p < len /\ left_idx p <> ch ==> Seq.index s ch >= Seq.index s (left_idx p)) /\
            (right_idx p < len /\ right_idx p <> ch ==> Seq.index s ch >= Seq.index s (right_idx p)) /\
            // Grandparent condition: only needed if parent_idx p >= k
            (p > 0 /\ parent_idx p >= k ==> Seq.index s (parent_idx p) >= Seq.index s ch))
          (ensures almost_heaps_from (swap_seq s p ch) len k ch)
  = let s' = swap_seq s p ch in
    swap_length s p ch;
    // 1. heap_down_at s' len p holds (swap_heap_down_at_parent)
    swap_heap_down_at_parent s len p ch;
    // 2. For j >= k, j <> ch, j <> p: heap_down_at s' len j
    let aux (j:nat{k <= j /\ j < len /\ j <> ch})
      : Lemma (heap_down_at s' len j)
      = if j = p then ()  // already proved above
        else (
          // j <> p, j <> ch. Need to check if j has p or ch as a child.
          let lj = left_idx j in
          let rj = right_idx j in
          // Can lj = ch? ch = left_idx p or right_idx p.
          // If lj = ch = left_idx p, then j = p (injectivity of left_idx), contradiction.
          // If lj = ch = right_idx p, then left_idx j = right_idx p, impossible (left_neq_right).
          (if ch = left_idx p then
             (if lj = ch then left_idx_inj p ch)
           else
             (if lj = ch then left_neq_right j p));
          // Similarly rj <> ch
          (if ch = left_idx p then
             (if rj = ch then left_neq_right p j)
           else
             (if rj = ch then right_idx_inj p ch));
          // So lj <> ch and rj <> ch
          if lj = p || rj = p then (
            // j has p as a child, so j = parent_idx p
            if lj = p then left_idx_parent p j
            else right_idx_parent p j;
            // Need grandparent condition
            if p > 0 then (
              // j = parent_idx p >= k by precondition
              swap_heap_down_at_grandparent s len p ch j
            )
          ) else (
            // Neither child is p or ch
            swap_preserves_heap_down_other s len p ch j
          )
        )
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

// Grandparent property: child's children are bounded by child in the original sequence
let grandparent_after_swap_from (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (k:nat) (p:nat{p < len /\ p >= k}) (ch:nat{ch < len /\ p <> ch})
  : Lemma (requires almost_heaps_from s len k p /\ (ch = left_idx p \/ ch = right_idx p))
          (ensures (left_idx ch < len ==> Seq.index s ch >= Seq.index s (left_idx ch)) /\
                   (right_idx ch < len ==> Seq.index s ch >= Seq.index s (right_idx ch)))
  = ()

// ========== MAX-HEAPIFY (sift_down for max-heap) ==========

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
//SNIPPET_START: max_heapify_sig
fn rec max_heapify
  (a: A.array int) (idx: SZ.t) (heap_size: SZ.t) (start: Ghost.erased nat)
  (#s: erased (Seq.seq int) {
    SZ.v idx < SZ.v heap_size /\
    SZ.v heap_size <= Seq.length s /\
    Seq.length s == A.length a /\
    SZ.fits (op_Multiply 2 (Seq.length s) + 2)
  })
requires
  A.pts_to a s **
  pure (
    SZ.v idx >= start /\
    almost_heaps_from s (SZ.v heap_size) start (SZ.v idx) /\
    // Grandparent condition (only if parent is in range)
    (SZ.v idx > 0 /\ parent_idx (SZ.v idx) >= start ==>
      (left_idx (SZ.v idx) < SZ.v heap_size ==>
        Seq.index s (parent_idx (SZ.v idx)) >= Seq.index s (left_idx (SZ.v idx))) /\
      (right_idx (SZ.v idx) < SZ.v heap_size ==>
        Seq.index s (parent_idx (SZ.v idx)) >= Seq.index s (right_idx (SZ.v idx))))
  )
ensures exists* s'.
  A.pts_to a s' **
  pure (
    Seq.length s' == Seq.length s /\
    heaps_from s' (SZ.v heap_size) start /\
    permutation s s' /\
    (forall (k:nat). SZ.v heap_size <= k /\ k < Seq.length s ==> Seq.index s' k == Seq.index s k)
  )
//SNIPPET_END: max_heapify_sig
{
  let left = SZ.add (SZ.mul 2sz idx) 1sz;
  if (SZ.gte left heap_size) {
    // Leaf: heap_down_at trivially holds
    almost_to_full s (SZ.v heap_size) start (SZ.v idx);
    ()
  } else {
    let right = SZ.add (SZ.mul 2sz idx) 2sz;
    let cur = a.(idx);
    let lv = a.(left);
    if (SZ.lt right heap_size) {
      // Two children
      let rv = a.(right);
      if (lv >= rv) {
        if (lv > cur) {
          sift_down_swap_lemma_from s (SZ.v heap_size) start (SZ.v idx) (SZ.v left);
          grandparent_after_swap_from s (SZ.v heap_size) start (SZ.v idx) (SZ.v left);
          left_idx_inj (SZ.v idx) (SZ.v left);
          let vi = a.(idx);
          let vl = a.(left);
          a.(idx) <- vl;
          a.(left) <- vi;
          with s_after. assert (A.pts_to a s_after);
          swap_is_permutation s (SZ.v idx) (SZ.v left);
          swap_length s (SZ.v idx) (SZ.v left);
          swap_index_i s (SZ.v idx) (SZ.v left);
          max_heapify a left heap_size start #(swap_seq s (SZ.v idx) (SZ.v left))
        } else {
          almost_to_full s (SZ.v heap_size) start (SZ.v idx);
          ()
        }
      } else {
        if (rv > cur) {
          sift_down_swap_lemma_from s (SZ.v heap_size) start (SZ.v idx) (SZ.v right);
          grandparent_after_swap_from s (SZ.v heap_size) start (SZ.v idx) (SZ.v right);
          // right = right_idx idx, so parent_idx right = idx
          right_idx_inj (SZ.v idx) (SZ.v right);
          let vi = a.(idx);
          let vr = a.(right);
          a.(idx) <- vr;
          a.(right) <- vi;
          with s_after. assert (A.pts_to a s_after);
          swap_is_permutation s (SZ.v idx) (SZ.v right);
          swap_length s (SZ.v idx) (SZ.v right);
          swap_index_i s (SZ.v idx) (SZ.v right);
          max_heapify a right heap_size start #(swap_seq s (SZ.v idx) (SZ.v right))
        } else {
          almost_to_full s (SZ.v heap_size) start (SZ.v idx);
          ()
        }
      }
    } else {
      // Only left child
      if (lv > cur) {
        sift_down_swap_lemma_from s (SZ.v heap_size) start (SZ.v idx) (SZ.v left);
        grandparent_after_swap_from s (SZ.v heap_size) start (SZ.v idx) (SZ.v left);
        left_idx_inj (SZ.v idx) (SZ.v left);
        let vi = a.(idx);
        let vl = a.(left);
        a.(idx) <- vl;
        a.(left) <- vi;
        with s_after. assert (A.pts_to a s_after);
        swap_is_permutation s (SZ.v idx) (SZ.v left);
        swap_length s (SZ.v idx) (SZ.v left);
        swap_index_i s (SZ.v idx) (SZ.v left);
        max_heapify a left heap_size start #(swap_seq s (SZ.v idx) (SZ.v left))
      } else {
        almost_to_full s (SZ.v heap_size) start (SZ.v idx);
        ()
      }
    }
  }
}
#pop-options

// ========== BUILD-MAX-HEAP ==========

// heaps_from s len k means all nodes from k satisfy heap_down_at
// When k >= len, it's vacuously true

// ========== Extract-max lemmas ==========

// Root of max-heap is >= all elements in the heap
let rec root_ge_element (s:Seq.seq int) (len:nat{len <= Seq.length s}) (i:nat)
  : Lemma (requires is_max_heap s len /\ len > 0 /\ i < len)
          (ensures Seq.index s 0 >= Seq.index s i)
          (decreases i)
  = if i = 0 then ()
    else (
      let p = parent_idx i in
      parent_idx_lt i;
      root_ge_element s len p;
      bad_is_child_of_parent i
    )

// After swapping root with s[len-1] and shrinking, almost_heaps_from at 0
let extract_almost_heaps (s:Seq.seq int) (len:nat{len <= Seq.length s /\ len > 1})
  : Lemma (requires is_max_heap s len)
          (ensures (let new_len = len - 1 in
                    almost_heaps_from (swap_seq s 0 new_len) new_len 0 0))
  = let new_len = len - 1 in
    let s' = swap_seq s 0 new_len in
    swap_length s 0 new_len;
    let aux (j:nat{j < new_len /\ j > 0})
      : Lemma (heap_down_at s' new_len j)
      = swap_index_other s 0 new_len j;
        let lj = left_idx j in
        let rj = right_idx j in
        if lj < new_len then swap_index_other s 0 new_len lj;
        if rj < new_len then swap_index_other s 0 new_len rj
    in
    Classical.forall_intro (Classical.move_requires aux)

// Suffix sorted + prefix_le_suffix after extract step
let extract_extends_sorted (s:Seq.seq int) (len:nat{len <= Seq.length s /\ len > 1})
  : Lemma (requires is_max_heap s len /\
                    suffix_sorted s len /\
                    prefix_le_suffix s len)
          (ensures (let nl : nat = len - 1 in
                    let z : nat = 0 in
                    let s' = swap_seq s z nl in
                    suffix_sorted s' nl /\
                    prefix_le_suffix s' nl))
  = let z : nat = 0 in
    let nl : nat = len - 1 in
    let s' = swap_seq s z nl in
    swap_length s z nl;
    swap_index_i s z nl;
    swap_index_j s z nl;
    let aux_root (i:nat{i < len})
      : Lemma (Seq.index s z >= Seq.index s i)
      = root_ge_element s len i
    in
    Classical.forall_intro (Classical.move_requires aux_root)

// heaps_from with start=0 is the same as is_max_heap
let heaps_from_zero (s:Seq.seq int) (len:nat{len <= Seq.length s})
  : Lemma (requires heaps_from s len 0) (ensures is_max_heap s len)
  = ()

// Permuting within [0, k) preserves suffix_sorted and prefix_le_suffix

// Helper: if slices at [k, n) are element-wise equal, they are Seq.equal
let slice_suffix_eq (s1 s2:Seq.seq int) (k:nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    k <= Seq.length s1 /\
                    (forall (j:nat). k <= j /\ j < Seq.length s1 ==> Seq.index s2 j == Seq.index s1 j))
          (ensures Seq.equal (Seq.slice s1 k (Seq.length s1)) (Seq.slice s2 k (Seq.length s2)))
  = ()

// Helper: if x appears at index idx in s, then mem x s
// Proved by using lemma_mem_count with a filter that accepts only x
let index_mem_intro (s:Seq.seq int) (idx:nat{idx < Seq.length s})
  : Lemma (ensures SeqP.mem (Seq.index s idx) s)
  = let x = Seq.index s idx in
    let suffix = Seq.slice s idx (Seq.length s) in
    assert (Seq.head suffix == x);
    SeqP.lemma_mem_inversion suffix;
    assert (SeqP.mem x suffix);
    SeqP.lemma_mem_append (Seq.slice s 0 idx) suffix;
    Seq.lemma_split s idx

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"
let perm_preserves_sorted_suffix (s1 s2:Seq.seq int) (k:nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    k <= Seq.length s1 /\
                    suffix_sorted s1 k /\
                    prefix_le_suffix s1 k /\
                    (forall (j:nat). k <= j /\ j < Seq.length s1 ==> Seq.index s2 j == Seq.index s1 j) /\
                    permutation s1 s2)
          (ensures suffix_sorted s2 k /\ prefix_le_suffix s2 k)
  = reveal_opaque (`%permutation) (permutation s1 s2);
    let n = Seq.length s1 in
    // suffix_sorted: elements at >= k are same, trivially preserved
    // prefix_le_suffix: for i < k, j >= k, need s2[i] <= s2[j] = s1[j]
    slice_suffix_eq s1 s2 k;
    // Now slice s1 k n = slice s2 k n
    // From permutation: count x s1 = count x s2 for all x
    // lemma_count_slice: count x s = count x (slice s 0 k) + count x (slice s k n)
    // Since slice s1 k n = slice s2 k n, their counts match.
    // Therefore count x (slice s1 0 k) = count x (slice s2 0 k).
    let prefix_perm (x:int)
      : Lemma (SeqP.count x (Seq.slice s1 0 k) == SeqP.count x (Seq.slice s2 0 k))
      = SeqP.lemma_count_slice s1 k;
        SeqP.lemma_count_slice s2 k
    in
    Classical.forall_intro prefix_perm;
    // For any j >= k, all elements in prefix of s1 are <= s1[j] (from prefix_le_suffix)
    // Use lemma_mem_count on slice s1 0 k:
    // forall m < k. s1[m] <= s1[j], so f(s1[m]) = true where f = (fun v -> v <= s1[j])
    // By lemma_mem_count: forall x. mem x (slice s1 0 k) ==> f x
    // Since count x (slice s1 0 k) = count x (slice s2 0 k),
    // mem x (slice s2 0 k) ==> mem x (slice s1 0 k) ==> f x
    // s2[i] for i < k: index (slice s2 0 k) i = s2[i], so mem s2[i] (slice s2 0 k)
    // Therefore f(s2[i]) = s2[i] <= s1[j] = s2[j]. ✓
    let aux (j:nat{j >= k /\ j < n})
      : Lemma (forall (i:nat). i < k ==> Seq.index s2 i <= Seq.index s2 j)
      = let sj = Seq.index s1 j in
        let f : int -> bool = fun v -> v <= sj in
        // All elements in prefix of s1 satisfy f (from prefix_le_suffix)
        SeqP.lemma_mem_count (Seq.slice s1 0 k) f;
        // forall x. mem x (slice s1 0 k) ==> x <= sj
        let aux2 (i:nat{i < k}) : Lemma (Seq.index s2 i <= sj)
          = let sl2 = Seq.slice s2 0 k in
            let sl1 = Seq.slice s1 0 k in
            let x = Seq.index s2 i in
            // x appears at position i in sl2
            index_mem_intro sl2 i;
            // mem x sl2, so count x sl2 > 0
            // count x sl1 = count x sl2 (from prefix_perm), so count x sl1 > 0
            // mem x sl1, and from lemma_mem_count: f x, i.e., x <= sj
            assert (SeqP.mem x sl2);
            assert (SeqP.count x sl1 == SeqP.count x sl2)
        in
        Classical.forall_intro (Classical.move_requires aux2)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

// ========== Main HeapSort ==========

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
//SNIPPET_START: heapsort_sig
fn heapsort
  (a: A.array int)
  (n: SZ.t)
  (#s0: erased (Seq.seq int))
requires
  A.pts_to a s0 **
  pure (
    SZ.v n <= A.length a /\
    SZ.v n == Seq.length s0 /\
    Seq.length s0 == A.length a /\
    SZ.v n > 0 /\
    SZ.fits (op_Multiply 2 (Seq.length s0) + 2)
  )
ensures exists* s.
  A.pts_to a s **
  pure (
    Seq.length s == Seq.length s0 /\
    sorted s /\
    permutation s0 s
  )
//SNIPPET_END: heapsort_sig
{
  //SNIPPET_START: build_max_heap_loop
  // Phase 1: BUILD-MAX-HEAP (bottom-up)
  let half = SZ.div n 2sz;
  let mut i: SZ.t = half;
  
  while (!i >^ 0sz)
  invariant exists* vi s_cur.
    R.pts_to i vi **
    A.pts_to a s_cur **
    pure (
      SZ.v vi <= SZ.v half /\
      Seq.length s_cur == Seq.length s0 /\
      Seq.length s_cur == A.length a /\
      permutation s0 s_cur /\
      SZ.fits (op_Multiply 2 (Seq.length s_cur) + 2) /\
      heaps_from s_cur (SZ.v n) (SZ.v vi)
    )
  //SNIPPET_END: build_max_heap_loop
  {
    let vi = !i;
    let idx = vi - 1sz;
    i := idx;
    
    with s_cur. assert (A.pts_to a s_cur);
    // heaps_from s_cur n vi means all j >= vi satisfy heap_down_at
    // idx = vi - 1, so all j > idx satisfy heap_down_at
    // This gives us almost_heaps_from s_cur n idx idx
    heaps_from_to_almost s_cur (SZ.v n) (SZ.v idx) (SZ.v idx);
    max_heapify a idx n (SZ.v idx) #s_cur;
    ()
  };
  
  //SNIPPET_START: extract_max_loop
  // Phase 2: Extract-max loop
  let mut heap_sz: SZ.t = n;
  
  while (!heap_sz >^ 1sz)
  invariant exists* vsz s_cur.
    R.pts_to i 0sz **
    R.pts_to heap_sz vsz **
    A.pts_to a s_cur **
    pure (
      SZ.v vsz > 0 /\
      SZ.v vsz <= SZ.v n /\
      Seq.length s_cur == Seq.length s0 /\
      Seq.length s_cur == A.length a /\
      permutation s0 s_cur /\
      SZ.fits (op_Multiply 2 (Seq.length s_cur) + 2) /\
      is_max_heap s_cur (SZ.v vsz) /\
      suffix_sorted s_cur (SZ.v vsz) /\
      prefix_le_suffix s_cur (SZ.v vsz)
    )
  //SNIPPET_END: extract_max_loop
  {
    let vsz = !heap_sz;
    with s_cur. assert (A.pts_to a s_cur);
    
    // vsz > 1 from loop condition, so last >= 1
    let last = vsz - 1sz;
    let v0 = a.(0sz);
    let vl = a.(last);
    a.(0sz) <- vl;
    a.(last) <- v0;
    
    with s_swapped. assert (A.pts_to a s_swapped);
    swap_is_permutation s_cur 0 (SZ.v last);
    extract_extends_sorted s_cur (SZ.v vsz);
    
    // last >= 1 means new_sz = last >= 1 > 0
    // (actually last = vsz - 1, and vsz > 1, so last >= 1, new_sz = last >= 1)
    // But we need new_sz > 0 for max_heapify. Since vsz > 1, new_sz = vsz - 1 >= 1 > 0
    let new_sz = vsz - 1sz;
    // new_sz >= 1 since vsz >= 2
    extract_almost_heaps s_cur (SZ.v vsz);
    let zero : Ghost.erased nat = 0;
    max_heapify a 0sz new_sz zero #(swap_seq s_cur 0 (SZ.v last));
    with s_heapified. assert (A.pts_to a s_heapified);
    heaps_from_zero s_heapified (SZ.v new_sz);
    // Elements outside [0, new_sz) are unchanged by max_heapify
    // So suffix_sorted and prefix_le_suffix are preserved
    perm_preserves_sorted_suffix (swap_seq s_cur 0 (SZ.v last)) s_heapified (SZ.v new_sz);
    
    heap_sz := new_sz;
  };
  
  ()
}
#pop-options
