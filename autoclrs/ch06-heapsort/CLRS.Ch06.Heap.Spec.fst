(*
   CLRS Chapter 6: Heapsort — Pure Specification

   Pure F* definitions for max-heap operations from CLRS §6.1–6.4:
   - Heap index functions (PARENT, LEFT, RIGHT) with 0-based indexing
   - Max-heap property predicates (heap_down_at, is_max_heap, almost_heaps_from, heaps_from)
   - Sorted and permutation predicates
   - Swap on sequences

   NO admits. NO assumes.
*)

module CLRS.Ch06.Heap.Spec

module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties

// ========== Heap index functions ==========

//SNIPPET_START: heap_indices
let parent_idx (i:nat{i > 0}) : nat = (i - 1) / 2
let left_idx (i:nat) : nat = op_Multiply 2 i + 1
let right_idx (i:nat) : nat = op_Multiply 2 i + 2
//SNIPPET_END: heap_indices

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

// ========== Swap ==========

let swap_seq (s:Seq.seq int) (i j:nat{i < Seq.length s /\ j < Seq.length s}) : Seq.seq int =
  Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i)
