(*
   CLRS Chapter 6: Heapsort — Correctness Lemmas

   Proofs of correctness properties for max-heap operations:
   - Index arithmetic (parent/child relationships)
   - Heap predicate maintenance (sift-down, swap)
   - Permutation properties
   - Extract-max correctness (sorted suffix, prefix ≤ suffix)

   NO admits. NO assumes.
*)

module CLRS.Ch06.Heap.Lemmas

open CLRS.Ch06.Heap.Spec

module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module Classical = FStar.Classical

// ========== Index lemmas ==========

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

// ========== Core heap lemmas ==========

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

// ========== Permutation lemmas ==========

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

// ========== Swap lemmas ==========

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

// ========== Sift-down swap lemmas (max-heap, subtree version) ==========

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
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

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let swap_heap_down_at_parent (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (p:nat{p < len}) (ch:nat{ch < len /\ p <> ch})
  : Lemma (requires 
            (ch = left_idx p \/ ch = right_idx p) /\
            Seq.index s ch > Seq.index s p /\
            (left_idx p < len /\ left_idx p <> ch ==> Seq.index s ch >= Seq.index s (left_idx p)) /\
            (right_idx p < len /\ right_idx p <> ch ==> Seq.index s ch >= Seq.index s (right_idx p)))
          (ensures heap_down_at (swap_seq s p ch) len p)
  = swap_length s p ch;
    swap_index_i s p ch;
    swap_index_j s p ch;
    if ch = left_idx p then (
      let rp = right_idx p in
      if rp < len then (
        left_neq_right p p;
        swap_index_other s p ch rp
      )
    ) else (
      let lp = left_idx p in
      if lp < len then (
        left_neq_right p p;
        swap_index_other s p ch lp
      )
    )
#pop-options

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
    if left_idx j = p then (
      swap_index_i s p ch;
      if right_idx j < len then
        swap_index_other s p ch (right_idx j)
    ) else (
      if left_idx j < len then
        swap_index_other s p ch (left_idx j)
    )
#pop-options

// Main sift-down swap lemma for almost_heaps_from
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let sift_down_swap_lemma_from (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (k:nat) (p:nat{p < len /\ p >= k}) (ch:nat{ch < len /\ p <> ch})
  : Lemma (requires 
            almost_heaps_from s len k p /\
            (ch = left_idx p \/ ch = right_idx p) /\
            Seq.index s ch > Seq.index s p /\
            (left_idx p < len /\ left_idx p <> ch ==> Seq.index s ch >= Seq.index s (left_idx p)) /\
            (right_idx p < len /\ right_idx p <> ch ==> Seq.index s ch >= Seq.index s (right_idx p)) /\
            (p > 0 /\ parent_idx p >= k ==> Seq.index s (parent_idx p) >= Seq.index s ch))
          (ensures almost_heaps_from (swap_seq s p ch) len k ch)
  = let s' = swap_seq s p ch in
    swap_length s p ch;
    swap_heap_down_at_parent s len p ch;
    let aux (j:nat{k <= j /\ j < len /\ j <> ch})
      : Lemma (heap_down_at s' len j)
      = if j = p then ()
        else (
          let lj = left_idx j in
          let rj = right_idx j in
          (if ch = left_idx p then
             (if lj = ch then left_idx_inj p ch)
           else
             (if lj = ch then left_neq_right j p));
          (if ch = left_idx p then
             (if rj = ch then left_neq_right p j)
           else
             (if rj = ch then right_idx_inj p ch));
          if lj = p || rj = p then (
            if lj = p then left_idx_parent p j
            else right_idx_parent p j;
            if p > 0 then (
              swap_heap_down_at_grandparent s len p ch j
            )
          ) else (
            swap_preserves_heap_down_other s len p ch j
          )
        )
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

let grandparent_after_swap_from (s:Seq.seq int) (len:nat{len <= Seq.length s})
  (k:nat) (p:nat{p < len /\ p >= k}) (ch:nat{ch < len /\ p <> ch})
  : Lemma (requires almost_heaps_from s len k p /\ (ch = left_idx p \/ ch = right_idx p))
          (ensures (left_idx ch < len ==> Seq.index s ch >= Seq.index s (left_idx ch)) /\
                   (right_idx ch < len ==> Seq.index s ch >= Seq.index s (right_idx ch)))
  = ()

// ========== Build/Extract lemmas ==========

let heaps_from_zero (s:Seq.seq int) (len:nat{len <= Seq.length s})
  : Lemma (requires heaps_from s len 0) (ensures is_max_heap s len)
  = ()

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

let slice_suffix_eq (s1 s2:Seq.seq int) (k:nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    k <= Seq.length s1 /\
                    (forall (j:nat). k <= j /\ j < Seq.length s1 ==> Seq.index s2 j == Seq.index s1 j))
          (ensures Seq.equal (Seq.slice s1 k (Seq.length s1)) (Seq.slice s2 k (Seq.length s2)))
  = ()

let index_mem_intro (s:Seq.seq int) (idx:nat{idx < Seq.length s})
  : Lemma (ensures SeqP.mem (Seq.index s idx) s)
  = let x = Seq.index s idx in
    let suffix = Seq.slice s idx (Seq.length s) in
    assert (Seq.head suffix == x);
    SeqP.lemma_mem_inversion suffix;
    assert (SeqP.mem x suffix);
    SeqP.lemma_mem_append (Seq.slice s 0 idx) suffix;
    Seq.lemma_split s idx

// ========== Range-bounded lemmas for prefix sorting ==========
// The _upto versions are the general form; non-_upto versions delegate to them.

#push-options "--split_queries always"
let extract_extends_sorted_upto (s:Seq.seq int) (len n:nat)
  : Lemma (requires n <= Seq.length s /\ len <= n /\ len > 1 /\
                    is_max_heap s len /\
                    suffix_sorted_upto s len n /\
                    prefix_le_suffix_upto s len n)
          (ensures (let s' = swap_seq s 0 (len - 1) in
                    suffix_sorted_upto s' (len - 1) n /\
                    prefix_le_suffix_upto s' (len - 1) n))
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
#pop-options

// Helper 1: If s1 and s2 are permutations with the same suffix from k,
// then any element in the prefix of s2 also appears in the prefix of s1.
#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
private
let perm_prefix_witness (s1 s2:Seq.seq int) (k:nat) (x:int)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    k <= Seq.length s1 /\
                    (forall (m:nat). k <= m /\ m < Seq.length s1 ==> Seq.index s2 m == Seq.index s1 m) /\
                    SeqP.permutation int s1 s2 /\
                    SeqP.mem x (Seq.slice s2 0 k))
          (ensures SeqP.mem x (Seq.slice s1 0 k))
  = let len = Seq.length s1 in
    let sl1 = Seq.slice s1 0 k in
    let sl2 = Seq.slice s2 0 k in
    let suf1 = Seq.slice s1 k len in
    let suf2 = Seq.slice s2 k len in
    slice_suffix_eq s1 s2 k;
    Seq.lemma_eq_elim suf1 suf2;
    SeqP.lemma_count_slice s1 k;
    SeqP.lemma_count_slice s2 k
#pop-options

// Helper: element at index i in s2 exists at some index in s1's prefix
#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
private
let perm_prefix_bounded_aux_upto (s1 s2:Seq.seq int) (k n:nat) (i:nat) (j:nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    k <= n /\ n <= Seq.length s1 /\
                    suffix_sorted_upto s1 k n /\
                    prefix_le_suffix_upto s1 k n /\
                    (forall (m:nat). k <= m /\ m < Seq.length s1 ==> Seq.index s2 m == Seq.index s1 m) /\
                    permutation s1 s2 /\
                    i < k /\ j >= k /\ j < n)
          (ensures Seq.index s2 i <= Seq.index s2 j)
  = reveal_opaque (`%permutation) (permutation s1 s2);
    let len = Seq.length s1 in
    let sl1 = Seq.slice s1 0 k in
    let sl2 = Seq.slice s2 0 k in
    let x = Seq.index sl2 i in
    Seq.lemma_index_slice s2 0 k i;
    index_mem_intro sl2 i;
    perm_prefix_witness s1 s2 k x;
    let m = SeqP.index_mem x sl1 in
    Seq.lemma_index_slice s1 0 k m;
    assert (Seq.index s1 m == x);
    assert (m < k /\ k <= j /\ j < n);
    assert (Seq.index s2 j == Seq.index s1 j)
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
let perm_preserves_sorted_suffix_upto (s1 s2:Seq.seq int) (k n:nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    k <= n /\ n <= Seq.length s1 /\
                    suffix_sorted_upto s1 k n /\
                    prefix_le_suffix_upto s1 k n /\
                    (forall (j:nat). k <= j /\ j < Seq.length s1 ==> Seq.index s2 j == Seq.index s1 j) /\
                    permutation s1 s2)
          (ensures suffix_sorted_upto s2 k n /\ prefix_le_suffix_upto s2 k n)
  = permutation_same_length s1 s2;
    let aux (i:nat) (j:nat)
      : Lemma (ensures (i < k /\ k <= j /\ j < n) ==> Seq.index s2 i <= Seq.index s2 j)
      = if i < k && k <= j && j < n then
          perm_prefix_bounded_aux_upto s1 s2 k n i j
        else ()
    in
    Classical.forall_intro_2 aux
#pop-options

let sorted_upto_from_parts (s:Seq.seq int) (n:nat)
  : Lemma (requires suffix_sorted_upto s 1 n /\ prefix_le_suffix_upto s 1 n)
          (ensures sorted_upto s n)
  = ()

// ========== Non-_upto convenience wrappers ==========
// These delegate to the _upto versions with n = Seq.length s.
// suffix_sorted s k ≡ suffix_sorted_upto s k (Seq.length s)
// prefix_le_suffix s k ≡ prefix_le_suffix_upto s k (Seq.length s)

#push-options "--split_queries always"
let extract_extends_sorted (s:Seq.seq int) (len:nat{len <= Seq.length s /\ len > 1})
  : Lemma (requires is_max_heap s len /\
                    suffix_sorted s len /\
                    prefix_le_suffix s len)
          (ensures (let nl : nat = len - 1 in
                    let z : nat = 0 in
                    let s' = swap_seq s z nl in
                    suffix_sorted s' nl /\
                    prefix_le_suffix s' nl))
  = extract_extends_sorted_upto s len (Seq.length s)
#pop-options

let perm_preserves_sorted_suffix (s1 s2:Seq.seq int) (k:nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    k <= Seq.length s1 /\
                    suffix_sorted s1 k /\
                    prefix_le_suffix s1 k /\
                    (forall (j:nat). k <= j /\ j < Seq.length s1 ==> Seq.index s2 j == Seq.index s1 j) /\
                    permutation s1 s2)
          (ensures suffix_sorted s2 k /\ prefix_le_suffix s2 k)
  = perm_preserves_sorted_suffix_upto s1 s2 k (Seq.length s1)
