module CLRS.Ch16.Huffman.PQForest
open FStar.Mul
open CLRS.Ch16.Huffman.Defs
open CLRS.Ch16.Huffman.PQLemmas
open CLRS.Ch16.Huffman.ForestLemmas
open Pulse.Lib.TotalOrder
open FStar.Order
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
module PQ = Pulse.Lib.PriorityQueue
module HSpec = CLRS.Ch16.Huffman.Spec
module HOpt = CLRS.Ch16.Huffman.Optimality
module Box = Pulse.Lib.Box

// ========== Section 1: Opaque predicate intro/elim ==========

val pq_entry_freq_ok_intro_at (f: int) (idx: SZ.t) (active: list forest_entry) (k: nat)
  : Lemma (requires find_entry_by_idx active idx == Some k /\
                    k < L.length active /\
                    f == HSpec.freq_of (entry_tree (L.index active k)))
          (ensures pq_entry_freq_ok f idx active)

val pq_entry_freq_ok_elim (f: int) (idx: SZ.t) (active: list forest_entry)
  : Lemma (requires pq_entry_freq_ok f idx active)
          (ensures Some? (find_entry_by_idx active idx) /\
                   (let k = Some?.v (find_entry_by_idx active idx) in
                    k < L.length active /\
                    f == HSpec.freq_of (entry_tree (L.index active k))))

val pq_tree_freq_match_intro (pq: Seq.seq pq_entry) (active: list forest_entry)
  (pf: (j:nat) -> Lemma
    (ensures (j < Seq.length pq ==> pq_entry_freq_ok (fst (Seq.index pq j)) (snd (Seq.index pq j)) active)))
  : Lemma (ensures pq_tree_freq_match pq active)

val pq_tree_freq_match_elim (pq: Seq.seq pq_entry) (active: list forest_entry) (j: nat)
  : Lemma (requires pq_tree_freq_match pq active /\ j < Seq.length pq)
          (ensures pq_entry_freq_ok (fst (Seq.index pq j)) (snd (Seq.index pq j)) active)

val pq_tree_freq_match_elim_mem (pq: Seq.seq pq_entry) (active: list forest_entry) (y: pq_entry)
  : Lemma (requires pq_tree_freq_match pq active /\ Seq.mem y pq)
          (ensures pq_entry_freq_ok (fst y) (snd y) active)

val pq_no_idx_intro (pq: Seq.seq pq_entry) (idx: SZ.t)
  : Lemma (requires forall (j: nat). j < Seq.length pq ==> snd (Seq.index pq j) <> idx)
          (ensures pq_no_idx pq idx)

val pq_no_idx_elim_mem (pq: Seq.seq pq_entry) (idx: SZ.t) (y: pq_entry)
  : Lemma (requires pq_no_idx pq idx /\ Seq.mem y pq)
          (ensures snd y <> idx)

// ========== Section 2: PQ minimum vs forest root freqs ==========

val pq_min_le_forest_root_freqs
  (pq: Seq.seq pq_entry) (active: list forest_entry) (fmin: int) (imin: SZ.t) (k: nat)
  : Lemma (requires
      PQ.is_minimum (fmin, imin) pq /\
      pq_tree_freq_match pq active /\
      forest_has_pq_entry pq active /\
      forest_distinct_indices active /\
      pq_indices_in_forest pq active /\
      k < L.length active)
    (ensures fmin <= HSpec.freq_of (entry_tree (L.index active k)))

val forest_root_freqs_mem (active: list forest_entry) (x: pos)
  : Lemma (requires L.mem x (forest_root_freqs active))
          (ensures exists (k: nat). k < L.length active /\ HSpec.freq_of (entry_tree (L.index active k)) == x)

val pq_min_le_all_root_freqs
  (pq: Seq.seq pq_entry) (active: list forest_entry) (fmin: int) (imin: SZ.t)
  : Lemma (requires
      PQ.is_minimum (fmin, imin) pq /\
      pq_tree_freq_match pq active /\
      forest_has_pq_entry pq active /\
      forest_distinct_indices active /\
      pq_indices_in_forest pq active)
    (ensures forall (x: pos). L.mem x (forest_root_freqs active) ==> fmin <= x)

val freq2_le_at_rem_pos
  (pq0 pq1: Seq.seq pq_entry) (active0: list forest_entry)
  (freq1 freq2: pos) (idx1 idx2: SZ.t) (j1 j2: nat) (k: nat)
  : Lemma (requires
      PQ.is_minimum (freq1, idx1) pq0 /\
      PQ.extends pq1 pq0 (freq1, idx1) /\
      PQ.is_minimum (freq2, idx2) pq1 /\
      pq_tree_freq_match pq0 active0 /\
      forest_has_pq_entry pq0 active0 /\
      forest_distinct_indices active0 /\
      pq_idx_unique pq0 /\
      j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
      entry_idx (L.index active0 j1) == idx1 /\
      entry_idx (L.index active0 j2) == idx2 /\
      k < L.length (list_remove_two active0 j1 j2))
    (ensures freq2 <= HSpec.freq_of (entry_tree (L.index (list_remove_two active0 j1 j2) k)))

val freq2_le_remaining_root_freqs
  (pq0 pq1: Seq.seq pq_entry) (active0: list forest_entry)
  (freq1 freq2: pos) (idx1 idx2: SZ.t) (j1 j2: nat)
  : Lemma (requires
      PQ.is_minimum (freq1, idx1) pq0 /\
      PQ.extends pq1 pq0 (freq1, idx1) /\
      PQ.is_minimum (freq2, idx2) pq1 /\
      pq_tree_freq_match pq0 active0 /\
      forest_has_pq_entry pq0 active0 /\
      forest_distinct_indices active0 /\
      pq_indices_in_forest pq0 active0 /\
      pq_idx_unique pq0 /\
      j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
      entry_idx (L.index active0 j1) == idx1 /\
      entry_idx (L.index active0 j2) == idx2)
    (ensures
      forall (x: pos). L.mem x (forest_root_freqs (list_remove_two active0 j1 j2)) ==> freq2 <= x)

// ========== Section 3: Maintaining pq_tree_freq_match ==========

val pq_tree_freq_match_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry) (active: list forest_entry)
  : Lemma (requires PQ.extends s1 s0 x /\ pq_tree_freq_match s0 active)
          (ensures pq_tree_freq_match s1 active)

// ========== Section 4: Maintaining forest_has_pq_entry ==========

val forest_has_pq_entry_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry) (active: list forest_entry)
  : Lemma (requires PQ.extends s1 s0 x /\
                    forest_has_pq_entry s0 active /\
                    pq_idx_unique s0 /\
                    (forall (k: nat). k < L.length active ==> entry_idx (L.index active k) <> snd x))
          (ensures forest_has_pq_entry s1 active)

val pq_tree_freq_match_init_step
  (s0 s1: Seq.seq pq_entry) (f: pos) (idx: SZ.t)
  (active_old: list forest_entry) (p: hnode_ptr)
  : Lemma (requires PQ.extends s0 s1 (f, idx) /\
                    pq_tree_freq_match s0 active_old /\
                    pq_indices_in_forest s0 active_old /\
                    (forall (k: nat). k < L.length active_old ==> entry_idx (L.index active_old k) <> idx))
          (ensures pq_tree_freq_match s1 ((idx, p, HSpec.Leaf f) :: active_old))

val forest_has_pq_entry_init_step
  (s0 s1: Seq.seq pq_entry) (f: pos) (idx: SZ.t)
  (active_old: list forest_entry) (p: hnode_ptr)
  : Lemma (requires PQ.extends s0 s1 (f, idx) /\
                    forest_has_pq_entry s0 active_old /\
                    pq_idx_unique s0 /\
                    (forall (k: nat). k < L.length active_old ==> entry_idx (L.index active_old k) <> idx))
          (ensures forest_has_pq_entry s1 ((idx, p, HSpec.Leaf f) :: active_old))

val forest_has_pq_entry_remove_at (pq: Seq.seq pq_entry) (active: list forest_entry) (j: nat)
  : Lemma (requires forest_has_pq_entry pq active /\ j < L.length active)
          (ensures forest_has_pq_entry pq (list_remove_at active j))

val forest_has_pq_entry_prepend
  (s0 s1: Seq.seq pq_entry) (f: pos) (idx: SZ.t)
  (active_old: list forest_entry) (e: forest_entry)
  : Lemma (requires PQ.extends s0 s1 (f, idx) /\
                    entry_idx e == idx /\
                    forest_has_pq_entry s0 active_old /\
                    pq_idx_unique s0 /\
                    (forall (k: nat). k < L.length active_old ==> entry_idx (L.index active_old k) <> idx))
          (ensures forest_has_pq_entry s1 (e :: active_old))

// ========== Section 5: Merge step helpers ==========

val list_remove_two_preserves_entry (entries: list forest_entry) (j1 j2 k: nat)
  : Lemma (requires j1 < L.length entries /\ j2 < L.length entries /\ j1 <> j2 /\
                    k < L.length entries /\ k <> j1 /\ k <> j2 /\
                    forest_distinct_indices entries /\
                    forest_distinct_indices (list_remove_two entries j1 j2))
          (ensures (let rem = list_remove_two entries j1 j2 in
                    let idx = entry_idx (L.index entries k) in
                    match find_entry_by_idx rem idx with
                    | Some kr -> kr < L.length rem /\ L.index rem kr == L.index entries k
                    | None -> False))

val pq_entry_freq_ok_remove_two
  (f: int) (idx: SZ.t) (active0: list forest_entry) (j1 j2: nat)
  : Lemma (requires pq_entry_freq_ok f idx active0 /\
                    j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
                    idx <> entry_idx (L.index active0 j1) /\
                    idx <> entry_idx (L.index active0 j2) /\
                    forest_distinct_indices active0 /\
                    forest_distinct_indices (list_remove_two active0 j1 j2))
          (ensures pq_entry_freq_ok f idx (list_remove_two active0 j1 j2))

val pq_entry_freq_ok_prepend
  (f: int) (idx: SZ.t) (entries: list forest_entry) (e: forest_entry)
  : Lemma (requires pq_entry_freq_ok f idx entries /\ idx <> entry_idx e)
          (ensures pq_entry_freq_ok f idx (e :: entries))

val pq_merge_step_single_mem
  (active0: list forest_entry) (y: pq_entry)
  (j1 j2: nat) (idx1: SZ.t) (merged: hnode_ptr) (sum_freq: pos)
  (t1 t2: HSpec.htree)
  : Lemma (requires pq_entry_freq_ok (fst y) (snd y) active0 /\
                    j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
                    snd y <> idx1 /\
                    snd y <> entry_idx (L.index active0 j2) /\
                    entry_idx (L.index active0 j1) == idx1 /\
                    forest_distinct_indices active0 /\
                    forest_distinct_indices (list_remove_two active0 j1 j2))
          (ensures (let rem = list_remove_two active0 j1 j2 in
                    let new_entry : forest_entry = (idx1, merged, HSpec.Internal sum_freq t1 t2) in
                    pq_entry_freq_ok (fst y) (snd y) (new_entry :: rem)))

val merge_step_new_entry_freq_ok
  (rem: list forest_entry) (idx1: SZ.t) (merged: hnode_ptr) (sum_freq: pos)
  (t1 t2: HSpec.htree)
  : Lemma (requires sum_freq == HSpec.freq_of t1 + HSpec.freq_of t2)
          (ensures pq_entry_freq_ok sum_freq idx1
    ((idx1, merged, HSpec.Internal sum_freq t1 t2) :: rem))

val pq_tree_freq_match_merge_step
  (pq2 pq3: Seq.seq pq_entry) (active0: list forest_entry)
  (j1 j2: nat) (idx1: SZ.t) (freq1 freq2: int) (merged: hnode_ptr)
  (t1 t2: HSpec.htree) (sum_freq: pos)
  : Lemma (requires PQ.extends pq2 pq3 (sum_freq, idx1) /\
                    pq_tree_freq_match pq2 active0 /\
                    j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
                    entry_idx (L.index active0 j1) == idx1 /\
                    sum_freq == freq1 + freq2 /\
                    sum_freq == HSpec.freq_of t1 + HSpec.freq_of t2 /\
                    pq_no_idx pq2 idx1 /\
                    pq_no_idx pq2 (entry_idx (L.index active0 j2)) /\
                    forest_distinct_indices active0 /\
                    forest_distinct_indices (list_remove_two active0 j1 j2))
          (ensures (let new_active = (idx1, merged, HSpec.Internal sum_freq t1 t2) :: list_remove_two active0 j1 j2 in
                    pq_tree_freq_match pq3 new_active))

// ========== Section 6: Bundle management ==========

val init_bundle_intro_empty (freq_seq: Seq.seq int) (nd_contents: Seq.seq hnode_ptr) (n: nat)
  : Lemma (requires Seq.length nd_contents == n)
          (ensures init_bundle freq_seq nd_contents Seq.empty [] 0 n)

val init_bundle_step
  (freq_seq: Seq.seq int)
  (nd_old nd_new: Seq.seq hnode_ptr)
  (pq_old pq_new: Seq.seq pq_entry)
  (active_old: list forest_entry)
  (vi: SZ.t) (n: SZ.t)
  (freq_val: pos) (leaf: hnode_ptr)
  : Lemma
    (requires
      init_bundle freq_seq nd_old pq_old active_old (SZ.v vi) (SZ.v n) /\
      Seq.length nd_old == SZ.v n /\
      SZ.v vi < SZ.v n /\
      SZ.v vi < Seq.length freq_seq /\
      Seq.length freq_seq == SZ.v n /\
      Seq.length pq_old == SZ.v vi /\
      L.length active_old == SZ.v vi /\
      nd_new == Seq.upd nd_old (SZ.v vi) leaf /\
      freq_val == Seq.index freq_seq (SZ.v vi) /\
      SZ.fits (2 * SZ.v n + 2) /\
      PQ.extends pq_old pq_new (freq_val, vi) /\
      Seq.length pq_new == SZ.v vi + 1)
    (ensures
      init_bundle freq_seq nd_new pq_new ((vi, leaf, HSpec.Leaf freq_val) :: active_old) (SZ.v vi + 1) (SZ.v n))

val init_to_merge_bundle
  (freq_seq: Seq.seq int) (nd_contents: Seq.seq hnode_ptr)
  (pq: Seq.seq pq_entry) (active: list forest_entry) (n: nat)
  : Lemma (requires init_bundle freq_seq nd_contents pq active n n /\
                    SZ.fits n /\
                    Seq.length nd_contents == n /\
                    Seq.length freq_seq == n /\
                    L.length active == n /\ Seq.length pq == n /\ n > 0)
          (ensures merge_bundle freq_seq nd_contents pq active n)

val merge_bundle_elim (freq_seq: Seq.seq int) (nd_contents: Seq.seq hnode_ptr)
                      (pq: Seq.seq pq_entry) (active: list forest_entry) (n: nat)
  : Lemma (requires merge_bundle freq_seq nd_contents pq active n)
          (ensures
            SZ.fits n /\
            Seq.length nd_contents == n /\
            valid_pq_entries pq n /\
            pq_freqs_positive pq /\
            pq_idx_unique pq /\
            pq_indices_in_forest pq active /\
            pq_tree_freq_match pq active /\
            forest_has_pq_entry pq active /\
            forest_distinct_indices active /\
            (forall (k: nat). k < L.length active ==>
              SZ.v (entry_idx (L.index active k)) < n /\
              Seq.index nd_contents (SZ.v (entry_idx (L.index active k))) == entry_ptr (L.index active k)) /\
            (forall (x: pos). L.count x (all_leaf_freqs active) == L.count x (seq_to_pos_list freq_seq 0)) /\
            forest_total_cost active + HOpt.greedy_cost (forest_root_freqs active) ==
              HOpt.greedy_cost (seq_to_pos_list freq_seq 0))

val merge_bundle_intro (freq_seq: Seq.seq int) (nd_contents: Seq.seq hnode_ptr)
                       (pq: Seq.seq pq_entry) (active: list forest_entry) (n: nat)
  : Lemma (requires
            SZ.fits n /\
            Seq.length nd_contents == n /\
            valid_pq_entries pq n /\
            pq_freqs_positive pq /\
            pq_idx_unique pq /\
            pq_indices_in_forest pq active /\
            pq_tree_freq_match pq active /\
            forest_has_pq_entry pq active /\
            forest_distinct_indices active /\
            (forall (k: nat). k < L.length active ==>
              SZ.v (entry_idx (L.index active k)) < n /\
              Seq.index nd_contents (SZ.v (entry_idx (L.index active k))) == entry_ptr (L.index active k)) /\
            (forall (x: pos). L.count x (all_leaf_freqs active) == L.count x (seq_to_pos_list freq_seq 0)) /\
            forest_total_cost active + HOpt.greedy_cost (forest_root_freqs active) ==
              HOpt.greedy_cost (seq_to_pos_list freq_seq 0))
          (ensures merge_bundle freq_seq nd_contents pq active n)

val cost_invariant_from_merge_bundle
  (freq_seq: Seq.seq int) (nd_old: Seq.seq hnode_ptr)
  (pq0 pq1: Seq.seq pq_entry)
  (active0: list forest_entry) (n: nat)
  (freq1 freq2: pos) (idx1 idx2: SZ.t)
  (j1 j2: nat)
  : Lemma (requires
      merge_bundle freq_seq nd_old pq0 active0 n /\
      L.length active0 >= 2 /\
      Seq.length pq0 >= 2 /\
      PQ.extends pq1 pq0 (freq1, idx1) /\
      PQ.is_minimum (freq1, idx1) pq0 /\
      PQ.is_minimum (freq2, idx2) pq1 /\
      j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
      entry_idx (L.index active0 j1) == idx1 /\
      entry_idx (L.index active0 j2) == idx2 /\
      freq1 == HSpec.freq_of (entry_tree (L.index active0 j1)) /\
      freq2 == HSpec.freq_of (entry_tree (L.index active0 j2)))
    (ensures
      // Old cost invariant
      forest_total_cost active0 + HOpt.greedy_cost (forest_root_freqs active0) ==
        HOpt.greedy_cost (seq_to_pos_list freq_seq 0) /\
      // freq1 <= all root freqs
      (forall (x: pos). L.mem x (forest_root_freqs active0) ==> freq1 <= x) /\
      // Multiset decomposition
      (forall (x: pos). L.count x (forest_root_freqs active0) ==
        (if x = freq1 then 1 else 0) +
        (if x = freq2 then 1 else 0) +
        L.count x (forest_root_freqs (list_remove_two active0 j1 j2))) /\
      // freq2 <= remaining root freqs
      (forall (x: pos). L.mem x (forest_root_freqs (list_remove_two active0 j1 j2)) ==> freq2 <= x) /\
      L.length (forest_root_freqs active0) >= 2)

val merge_bundle_step
  (freq_seq: Seq.seq int)
  (nd_old nd_new: Seq.seq hnode_ptr)
  (pq0 pq1 pq2 pq3: Seq.seq pq_entry)
  (active0: list forest_entry)
  (n: nat)
  (freq1 freq2: pos) (idx1 idx2: SZ.t) (sum_freq: pos) (merged: hnode_ptr)
  (j1 j2: nat)
  : Lemma
    (requires
      merge_bundle freq_seq nd_old pq0 active0 n /\
      L.length active0 >= 2 /\
      Seq.length pq0 >= 2 /\
      // Two extract_mins
      PQ.is_minimum (freq1, idx1) pq0 /\
      PQ.extends pq1 pq0 (freq1, idx1) /\
      PQ.is_minimum (freq2, idx2) pq1 /\
      PQ.extends pq2 pq1 (freq2, idx2) /\
      Seq.length pq1 == Seq.length pq0 - 1 /\
      Seq.length pq2 == Seq.length pq1 - 1 /\
      // Insert
      PQ.extends pq2 pq3 (sum_freq, idx1) /\
      Seq.length pq3 == Seq.length pq2 + 1 /\
      sum_freq == freq1 + freq2 /\
      // Node update
      Seq.length nd_old == n /\
      SZ.v idx1 < n /\ SZ.v idx2 < n /\
      nd_new == Seq.upd nd_old (SZ.v idx1) merged /\
      // Forest structure (explicit bounds)
      Some? (find_entry_by_idx active0 idx1) /\
      Some? (find_entry_by_idx active0 idx2) /\
      j1 == Some?.v (find_entry_by_idx active0 idx1) /\
      j2 == Some?.v (find_entry_by_idx active0 idx2) /\
      j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
      entry_idx (L.index active0 j1) == idx1 /\
      entry_idx (L.index active0 j2) == idx2)
    (ensures
      (let t1 = entry_tree (L.index active0 j1) in
       let t2 = entry_tree (L.index active0 j2) in
       let new_tree = HSpec.Internal sum_freq t1 t2 in
       let new_active = (idx1, merged, new_tree) :: list_remove_two active0 j1 j2 in
       merge_bundle freq_seq nd_new pq3 new_active n))
