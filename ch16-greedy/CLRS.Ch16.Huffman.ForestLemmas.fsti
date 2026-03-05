module CLRS.Ch16.Huffman.ForestLemmas
open FStar.SizeT
open FStar.Mul
open CLRS.Ch16.Huffman.Defs
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
module PQ = Pulse.Lib.PriorityQueue
module HSpec = CLRS.Ch16.Huffman.Spec
module HOpt = CLRS.Ch16.Huffman.Optimality

// ========== Section 1: Forest-PQ structural lemmas ==========

val pq_forest_extends (s0 s1: Seq.seq pq_entry) (x: pq_entry) (forest: list forest_entry)
  : Lemma (requires PQ.extends s0 s1 x /\
                    pq_indices_in_forest s0 forest /\
                    Some? (find_entry_by_idx forest (snd x)))
          (ensures pq_indices_in_forest s1 forest)

val pq_forest_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry) (forest: list forest_entry)
  : Lemma (requires PQ.extends s1 s0 x /\ pq_indices_in_forest s0 forest)
          (ensures pq_indices_in_forest s1 forest /\
                   Some? (find_entry_by_idx forest (snd x)))

val find_entry_prepend (entries: list forest_entry) (idx: SZ.t) (p: hnode_ptr) (ft: HSpec.htree)
  : Lemma (ensures Some? (find_entry_by_idx ((idx, p, ft) :: entries) idx) /\
                   find_entry_by_idx ((idx, p, ft) :: entries) idx == Some 0)

val find_entry_prepend_other (entries: list forest_entry) (e: forest_entry) (idx: SZ.t)
  : Lemma (ensures Some? (find_entry_by_idx entries idx) ==>
                   Some? (find_entry_by_idx (e :: entries) idx))

val pq_forest_prepend (pq: Seq.seq pq_entry) (forest: list forest_entry) (e: forest_entry)
  : Lemma (requires pq_indices_in_forest pq forest)
          (ensures pq_indices_in_forest pq (e :: forest))



val pq_forest_remove_two (pq: Seq.seq pq_entry) (forest: list forest_entry)
  (j1 j2: nat)
  : Lemma (requires j1 < L.length forest /\ j2 < L.length forest /\ j1 <> j2 /\
                    pq_indices_in_forest pq forest /\
                    (forall (k: nat). k < Seq.length pq ==>
                      snd (Seq.index pq k) =!= entry_idx (L.index forest j1) /\
                      snd (Seq.index pq k) =!= entry_idx (L.index forest j2)))
          (ensures pq_indices_in_forest pq (list_remove_two forest j1 j2))

val forest_distinct_indices_remove_at (entries: list forest_entry) (j: nat)
  : Lemma (requires forest_distinct_indices entries /\ j < L.length entries)
          (ensures forest_distinct_indices (list_remove_at entries j))

val forest_distinct_indices_remove_two (entries: list forest_entry) (j1 j2: nat)
  : Lemma (requires forest_distinct_indices entries /\ j1 < L.length entries /\
                    j2 < L.length entries /\ j1 <> j2)
          (ensures forest_distinct_indices (list_remove_two entries j1 j2))

val list_remove_at_no_idx (entries: list forest_entry) (j: nat) (idx: SZ.t)
  : Lemma (requires forest_distinct_indices entries /\ j < L.length entries /\
                    entry_idx (L.index entries j) == idx)
          (ensures forall (k: nat). k < L.length (list_remove_at entries j) ==>
                    entry_idx (L.index (list_remove_at entries j) k) <> idx)

val list_remove_two_no_idx (entries: list forest_entry) (j1 j2: nat) (idx: SZ.t)
  : Lemma (requires forest_distinct_indices entries /\ j1 < L.length entries /\
                    j2 < L.length entries /\ j1 <> j2 /\
                    entry_idx (L.index entries j1) == idx)
          (ensures forall (k: nat). k < L.length (list_remove_two entries j1 j2) ==>
                    entry_idx (L.index (list_remove_two entries j1 j2) k) <> idx)

val forest_distinct_indices_prepend (entries: list forest_entry) (e: forest_entry)
  : Lemma (requires forest_distinct_indices entries /\
                    (forall (k: nat). k < L.length entries ==>
                      entry_idx (L.index entries k) <> entry_idx e))
          (ensures forest_distinct_indices (e :: entries))

val forest_distinct_indices_after_merge
  (active0: list forest_entry) (j1 j2: nat) (idx: SZ.t)
  (merged: hnode_ptr) (tree: HSpec.htree)
  : Lemma (requires forest_distinct_indices active0 /\
                    j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
                    entry_idx (L.index active0 j1) == idx)
          (ensures forest_distinct_indices
                    ((idx, merged, tree) :: list_remove_two active0 j1 j2))



val node_ptr_correspondence_upd_nat
  (active0: list forest_entry) (j1 j2: nat)
  (idx1: SZ.t) (merged: hnode_ptr) (tree: HSpec.htree)
  (nd_contents: Seq.seq hnode_ptr) (n: nat)
  : Lemma (requires
      SZ.fits n /\
      forest_distinct_indices active0 /\
      j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
      entry_idx (L.index active0 j1) == idx1 /\
      SZ.v idx1 < Seq.length nd_contents /\
      Seq.length nd_contents == n /\
      (forall (k: nat). k < L.length active0 ==>
        SZ.v (entry_idx (L.index active0 k)) < n /\
        Seq.index nd_contents (SZ.v (entry_idx (L.index active0 k))) == entry_ptr (L.index active0 k)))
    (ensures (
      let new_active = (idx1, merged, tree) :: list_remove_two active0 j1 j2 in
      let nd' = Seq.upd nd_contents (SZ.v idx1) merged in
      forall (k: nat). k < L.length new_active ==>
        SZ.v (entry_idx (L.index new_active k)) < n /\
        Seq.index nd' (SZ.v (entry_idx (L.index new_active k))) ==
        entry_ptr (L.index new_active k)))

// ========== Section 2: Init-step helpers ==========

val forest_idx_fresh (entries: list forest_entry) (bound: SZ.t)
  : Lemma (requires forall (k: nat). k < L.length entries ==> SZ.v (entry_idx (L.index entries k)) < SZ.v bound)
          (ensures forall (k: nat). k < L.length entries ==> entry_idx (L.index entries k) <> bound)

val node_ptr_correspondence_init_step
  (active_old: list forest_entry) (vi: SZ.t) (leaf: hnode_ptr) (tree: HSpec.htree)
  (nd_old: Seq.seq hnode_ptr) (n: SZ.t)
  : Lemma (requires
      SZ.v vi < SZ.v n /\
      Seq.length nd_old == SZ.v n /\
      (forall (k: nat). k < L.length active_old ==>
        SZ.v (entry_idx (L.index active_old k)) < SZ.v vi /\
        Seq.index nd_old (SZ.v (entry_idx (L.index active_old k))) == entry_ptr (L.index active_old k)))
    (ensures (
      let new_active = (vi, leaf, tree) :: active_old in
      let nd' = Seq.upd nd_old (SZ.v vi) leaf in
      forall (k: nat). k < L.length new_active ==>
        SZ.v (entry_idx (L.index new_active k)) < SZ.v vi + 1 /\
        Seq.index nd' (SZ.v (entry_idx (L.index new_active k))) == entry_ptr (L.index new_active k)))

// ========== Section 3: Leaf frequency multiset tracking ==========






val all_leaf_freqs_init_step
  (entries: list forest_entry) (idx: SZ.t) (p: hnode_ptr) (f: pos)
  (s: Seq.seq int) (k: nat)
  : Lemma (requires k < Seq.length s /\
                    Seq.index s k > 0 /\
                    Seq.index s k == f /\
                    (forall (x: pos). L.count x (all_leaf_freqs entries) + L.count x (seq_to_pos_list s k) ==
                                      L.count x (seq_to_pos_list s 0)))
          (ensures (forall (x: pos). 
                    L.count x (all_leaf_freqs ((idx, p, HSpec.Leaf 0 f) :: entries)) +
                    L.count x (seq_to_pos_list s (k + 1)) ==
                    L.count x (seq_to_pos_list s 0)))

val all_leaf_freqs_merge_step_full
  (entries: list forest_entry) (j1 j2: nat)
  (idx: SZ.t) (p: hnode_ptr) (f: pos) (freqs: list pos)
  : Lemma (requires j1 < L.length entries /\ j2 < L.length entries /\ j1 <> j2 /\
                    (forall (x: pos). L.count x (all_leaf_freqs entries) == L.count x freqs))
          (ensures (
            let t1 = entry_tree (L.index entries j1) in
            let t2 = entry_tree (L.index entries j2) in
            let merged = HSpec.Internal f t1 t2 in
            let new_entries = (idx, p, merged) :: list_remove_two entries j1 j2 in
            forall (x: pos). L.count x (all_leaf_freqs new_entries) == L.count x freqs))

val all_leaf_freqs_singleton_full (entries: list forest_entry) (freqs: list pos)
  : Lemma (requires L.length entries == 1 /\
                    (forall (x: pos). L.count x (all_leaf_freqs entries) == L.count x freqs))
          (ensures HSpec.same_frequency_multiset (entry_tree (L.index entries 0)) freqs)

// ========== Section 4: Cost tracking lemmas ==========













val forest_root_freqs_singleton (entries: list forest_entry)
  : Lemma (requires L.length entries == 1)
          (ensures forest_root_freqs entries == [HSpec.freq_of (entry_tree (L.index entries 0))])

val forest_total_cost_singleton (entries: list forest_entry)
  : Lemma (requires L.length entries == 1)
          (ensures forest_total_cost entries == HSpec.cost (entry_tree (L.index entries 0)))

val greedy_cost_singleton (f: pos)
  : Lemma (HOpt.greedy_cost [f] == 0)

val forest_root_freqs_length (entries: list forest_entry)
  : Lemma (ensures L.length (forest_root_freqs entries) == L.length entries)

val cost_invariant_merge_step
  (active0: list forest_entry) (j1 j2: nat)
  (freq1 freq2 sum_freq: pos) (idx1: SZ.t) (merged: hnode_ptr)
  (t1 t2: HSpec.htree) (initial_freqs: list pos)
  : Lemma (requires
      j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
      entry_tree (L.index active0 j1) == t1 /\
      entry_tree (L.index active0 j2) == t2 /\
      freq1 == HSpec.freq_of t1 /\ freq2 == HSpec.freq_of t2 /\
      sum_freq == freq1 + freq2 /\
      forest_total_cost active0 + HOpt.greedy_cost (forest_root_freqs active0) ==
        HOpt.greedy_cost initial_freqs /\
      (forall (x: pos). L.mem x (forest_root_freqs active0) ==> freq1 <= x) /\
      (forall (x: pos). L.count x (forest_root_freqs active0) ==
        (if x = freq1 then 1 else 0) +
        (if x = freq2 then 1 else 0) +
        L.count x (forest_root_freqs (list_remove_two active0 j1 j2))) /\
      (forall (x: pos). L.mem x (forest_root_freqs (list_remove_two active0 j1 j2)) ==> freq2 <= x) /\
      L.length (forest_root_freqs active0) >= 2)
    (ensures (
      let new_tree = HSpec.Internal sum_freq t1 t2 in
      let new_active = (idx1, merged, new_tree) :: list_remove_two active0 j1 j2 in
      forest_total_cost new_active + HOpt.greedy_cost (forest_root_freqs new_active) ==
        HOpt.greedy_cost initial_freqs))



val forest_root_freqs_remove_two_forall (entries: list forest_entry) (j1 j2: nat)
  : Lemma (requires j1 < L.length entries /\ j2 < L.length entries /\ j1 <> j2)
          (ensures forall (x: pos). L.count x (forest_root_freqs entries) ==
                    (if x = HSpec.freq_of (entry_tree (L.index entries j1)) then 1 else 0) +
                    (if x = HSpec.freq_of (entry_tree (L.index entries j2)) then 1 else 0) +
                    L.count x (forest_root_freqs (list_remove_two entries j1 j2)))

// ========== Section 5: forest_all_leaves helpers ==========



// ========== Section 6: cost_zero helper ==========

val cost_zero_root_eq_leaf_freqs (entries: list forest_entry) (x: pos)
  : Lemma (requires forest_total_cost entries == 0)
          (ensures L.count x (forest_root_freqs entries) == L.count x (all_leaf_freqs entries))

// ========== Section 7: remaining_no_idx ==========

