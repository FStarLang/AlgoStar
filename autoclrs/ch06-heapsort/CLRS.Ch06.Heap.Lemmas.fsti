(*
   CLRS Chapter 6: Heapsort — Lemma Signatures

   Interface for correctness lemmas about max-heap operations.
*)

module CLRS.Ch06.Heap.Lemmas

open CLRS.Ch06.Heap.Spec

module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties

// ========== Index lemmas ==========

val parent_idx_lt (i:nat{i > 0}) : Lemma (parent_idx i < i)

val bad_is_child_of_parent (bad:nat{bad > 0})
  : Lemma (left_idx (parent_idx bad) = bad \/ right_idx (parent_idx bad) = bad)

val left_idx_inj (i j:nat) : Lemma (requires left_idx i = j /\ j > 0) (ensures parent_idx j = i)
val right_idx_inj (i j:nat) : Lemma (requires right_idx i = j /\ j > 0) (ensures parent_idx j = i)
val left_neq_right (i j:nat) : Lemma (left_idx i <> right_idx j)

val left_idx_parent (bad:nat{bad > 0}) (i:nat)
  : Lemma (requires left_idx i = bad) (ensures i = parent_idx bad)
val right_idx_parent (bad:nat{bad > 0}) (i:nat)
  : Lemma (requires right_idx i = bad) (ensures i = parent_idx bad)

// ========== Core heap lemmas ==========

val heaps_from_to_almost (s:Seq.seq int) (len:nat{len <= Seq.length s}) 
  (k:nat) (bad:nat{bad < len})
  : Lemma (requires bad >= k /\ heaps_from s len (bad + 1))
          (ensures almost_heaps_from s len bad bad)

val almost_to_full (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (k:nat) (bad:nat{bad < len})
  : Lemma (requires almost_heaps_from s len k bad /\ heap_down_at s len bad)
          (ensures heaps_from s len k)

// ========== Permutation lemmas ==========

val permutation_same_length (s1 s2 : Seq.seq int)
  : Lemma (requires permutation s1 s2)
          (ensures Seq.length s1 == Seq.length s2)
          [SMTPat (permutation s1 s2)]

val permutation_refl (s: Seq.seq int)
  : Lemma (ensures permutation s s)
    [SMTPat (permutation s s)]

val compose_permutations (s1 s2 s3: Seq.seq int)
  : Lemma (requires permutation s1 s2 /\ permutation s2 s3)
    (ensures permutation s1 s3)
    [SMTPat (permutation s1 s2); SMTPat (permutation s2 s3)]

// ========== Swap lemmas ==========

val swap_length (s:Seq.seq int) (i j:nat{i < Seq.length s /\ j < Seq.length s})
  : Lemma (Seq.length (swap_seq s i j) == Seq.length s)

val swap_index_i (s:Seq.seq int) (i j:nat{i < Seq.length s /\ j < Seq.length s})
  : Lemma (Seq.index (swap_seq s i j) i == Seq.index s j)

val swap_index_j (s:Seq.seq int) (i j:nat{i < Seq.length s /\ j < Seq.length s /\ i <> j})
  : Lemma (Seq.index (swap_seq s i j) j == Seq.index s i)

val swap_index_other (s:Seq.seq int) (i j k:nat{i < Seq.length s /\ j < Seq.length s /\ k < Seq.length s /\ k <> i /\ k <> j})
  : Lemma (Seq.index (swap_seq s i j) k == Seq.index s k)

val swap_unchanged_above (s:Seq.seq int) (i j:nat{i < Seq.length s /\ j < Seq.length s}) (bound:nat)
  : Lemma (requires i < bound /\ j < bound)
          (ensures forall (k:nat). bound <= k /\ k < Seq.length s ==> 
                    Seq.index (swap_seq s i j) k == Seq.index s k)

val swap_is_permutation (s: Seq.seq int) (i j: nat)
  : Lemma (requires i < Seq.length s /\ j < Seq.length s)
          (ensures permutation s (swap_seq s i j))

// ========== Sift-down swap lemmas ==========

val swap_preserves_heap_down_other (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (p:nat{p < len}) (ch:nat{ch < len /\ p <> ch})
  (j:nat{j < len /\ j <> p /\ j <> ch})
  : Lemma (requires 
            heap_down_at s len j /\
            left_idx j <> p /\ left_idx j <> ch /\
            right_idx j <> p /\ right_idx j <> ch)
          (ensures heap_down_at (swap_seq s p ch) len j)

val swap_heap_down_at_parent (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (p:nat{p < len}) (ch:nat{ch < len /\ p <> ch})
  : Lemma (requires 
            (ch = left_idx p \/ ch = right_idx p) /\
            Seq.index s ch > Seq.index s p /\
            (left_idx p < len /\ left_idx p <> ch ==> Seq.index s ch >= Seq.index s (left_idx p)) /\
            (right_idx p < len /\ right_idx p <> ch ==> Seq.index s ch >= Seq.index s (right_idx p)))
          (ensures heap_down_at (swap_seq s p ch) len p)

val swap_heap_down_at_grandparent (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (p:nat{p < len /\ p > 0}) (ch:nat{ch < len /\ p <> ch})
  (j:nat{j < len /\ j <> p /\ j <> ch /\ (left_idx j = p \/ right_idx j = p)})
  : Lemma (requires 
            heap_down_at s len j /\
            Seq.index s j >= Seq.index s ch /\
            left_idx j <> ch /\ right_idx j <> ch)
          (ensures heap_down_at (swap_seq s p ch) len j)

val sift_down_swap_lemma_from (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (k:nat) (p:nat{p < len /\ p >= k}) (ch:nat{ch < len /\ p <> ch})
  : Lemma (requires 
            almost_heaps_from s len k p /\
            (ch = left_idx p \/ ch = right_idx p) /\
            Seq.index s ch > Seq.index s p /\
            (left_idx p < len /\ left_idx p <> ch ==> Seq.index s ch >= Seq.index s (left_idx p)) /\
            (right_idx p < len /\ right_idx p <> ch ==> Seq.index s ch >= Seq.index s (right_idx p)) /\
            (p > 0 /\ parent_idx p >= k ==> Seq.index s (parent_idx p) >= Seq.index s ch))
          (ensures almost_heaps_from (swap_seq s p ch) len k ch)

val grandparent_after_swap_from (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (k:nat) (p:nat{p < len /\ p >= k}) (ch:nat{ch < len /\ p <> ch})
  : Lemma (requires almost_heaps_from s len k p /\ (ch = left_idx p \/ ch = right_idx p))
          (ensures (left_idx ch < len ==> Seq.index s ch >= Seq.index s (left_idx ch)) /\
                   (right_idx ch < len ==> Seq.index s ch >= Seq.index s (right_idx ch)))

// ========== Build/Extract lemmas ==========

val heaps_from_zero (s:Seq.seq int) (len:nat{len <= Seq.length s})
  : Lemma (requires heaps_from s len 0) (ensures is_max_heap s len)

val root_ge_element (s:Seq.seq int) (len:nat{len <= Seq.length s}) (i:nat)
  : Lemma (requires is_max_heap s len /\ len > 0 /\ i < len)
          (ensures Seq.index s 0 >= Seq.index s i)

val extract_almost_heaps (s:Seq.seq int) (len:nat{len <= Seq.length s /\ len > 1})
  : Lemma (requires is_max_heap s len)
          (ensures (let new_len = len - 1 in
                    almost_heaps_from (swap_seq s 0 new_len) new_len 0 0))

val slice_suffix_eq (s1 s2:Seq.seq int) (k:nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    k <= Seq.length s1 /\
                    (forall (j:nat). k <= j /\ j < Seq.length s1 ==> Seq.index s2 j == Seq.index s1 j))
          (ensures Seq.equal (Seq.slice s1 k (Seq.length s1)) (Seq.slice s2 k (Seq.length s2)))

val index_mem_intro (s:Seq.seq int) (idx:nat{idx < Seq.length s})
  : Lemma (ensures SeqP.mem (Seq.index s idx) s)

// ========== Range-bounded extract/perm lemmas ==========
// The _upto versions are the general form; non-_upto versions delegate to them.

val extract_extends_sorted_upto (s:Seq.seq int) (len n:nat)
  : Lemma (requires n <= Seq.length s /\ len <= n /\ len > 1 /\
                    is_max_heap s len /\
                    suffix_sorted_upto s len n /\
                    prefix_le_suffix_upto s len n)
          (ensures (let s' = swap_seq s 0 (len - 1) in
                    suffix_sorted_upto s' (len - 1) n /\
                    prefix_le_suffix_upto s' (len - 1) n))

val perm_preserves_sorted_suffix_upto (s1 s2:Seq.seq int) (k n:nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    k <= n /\ n <= Seq.length s1 /\
                    suffix_sorted_upto s1 k n /\
                    prefix_le_suffix_upto s1 k n /\
                    (forall (j:nat). k <= j /\ j < Seq.length s1 ==> Seq.index s2 j == Seq.index s1 j) /\
                    permutation s1 s2)
          (ensures suffix_sorted_upto s2 k n /\ prefix_le_suffix_upto s2 k n)

val sorted_upto_from_parts (s:Seq.seq int) (n:nat)
  : Lemma (requires suffix_sorted_upto s 1 n /\ prefix_le_suffix_upto s 1 n)
          (ensures sorted_upto s n)

// ========== Extract-step helper (combines all per-iteration proof work) ==========

val extract_step_lemma
  (s_cur: Seq.seq int) (s_heapified: Seq.seq int) (s0: Seq.seq int)
  (vsz n: nat)
  : Lemma
    (requires
      vsz > 1 /\ vsz <= n /\ n <= Seq.length s_cur /\
      Seq.length s_cur == Seq.length s0 /\
      permutation s_cur (swap_seq s_cur 0 (vsz - 1)) /\
      Seq.length (swap_seq s_cur 0 (vsz - 1)) == Seq.length s_cur /\
      is_max_heap s_cur vsz /\
      suffix_sorted_upto s_cur vsz n /\
      prefix_le_suffix_upto s_cur vsz n /\
      permutation s0 s_cur /\
      (forall (k:nat). n <= k /\ k < Seq.length s_cur ==> Seq.index s_cur k == Seq.index s0 k) /\
      // From max_heapify postcondition:
      Seq.length s_heapified == Seq.length (swap_seq s_cur 0 (vsz - 1)) /\
      heaps_from s_heapified (vsz - 1) 0 /\
      permutation (swap_seq s_cur 0 (vsz - 1)) s_heapified /\
      (forall (k:nat). (vsz - 1) <= k /\ k < Seq.length s_heapified ==>
        Seq.index s_heapified k == Seq.index (swap_seq s_cur 0 (vsz - 1)) k))
    (ensures
      vsz - 1 > 0 /\
      vsz - 1 <= n /\
      Seq.length s_heapified == Seq.length s0 /\
      permutation s0 s_heapified /\
      (forall (k:nat). n <= k /\ k < Seq.length s_heapified ==> Seq.index s_heapified k == Seq.index s0 k) /\
      is_max_heap s_heapified (vsz - 1) /\
      suffix_sorted_upto s_heapified (vsz - 1) n /\
      prefix_le_suffix_upto s_heapified (vsz - 1) n)

val extract_extends_sorted (s:Seq.seq int) (len:nat{len <= Seq.length s /\ len > 1})
  : Lemma (requires is_max_heap s len /\
                    suffix_sorted s len /\
                    prefix_le_suffix s len)
          (ensures (let nl : nat = len - 1 in
                    let z : nat = 0 in
                    let s' = swap_seq s z nl in
                    suffix_sorted s' nl /\
                    prefix_le_suffix s' nl))

val perm_preserves_sorted_suffix (s1 s2:Seq.seq int) (k:nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    k <= Seq.length s1 /\
                    suffix_sorted s1 k /\
                    prefix_le_suffix s1 k /\
                    (forall (j:nat). k <= j /\ j < Seq.length s1 ==> Seq.index s2 j == Seq.index s1 j) /\
                    permutation s1 s2)
          (ensures suffix_sorted s2 k /\ prefix_le_suffix s2 k)
