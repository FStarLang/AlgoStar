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

#push-options "--z3rlimit 8"

// ========== Section 1: Opaque predicate intro/elim ==========

let pq_entry_freq_ok_intro_at (f: int) (idx: SZ.t) (active: list forest_entry) (k: nat)
  : Lemma (requires find_entry_by_idx active idx == Some k /\
                    k < L.length active /\
                    f == HSpec.freq_of (entry_tree (L.index active k)))
          (ensures pq_entry_freq_ok f idx active)
  = reveal_opaque (`%pq_entry_freq_ok) pq_entry_freq_ok

let pq_entry_freq_ok_elim (f: int) (idx: SZ.t) (active: list forest_entry)
  : Lemma (requires pq_entry_freq_ok f idx active)
          (ensures Some? (find_entry_by_idx active idx) /\
                   (let k = Some?.v (find_entry_by_idx active idx) in
                    k < L.length active /\
                    f == HSpec.freq_of (entry_tree (L.index active k))))
  = reveal_opaque (`%pq_entry_freq_ok) pq_entry_freq_ok;
    find_entry_by_idx_spec active idx

let pq_tree_freq_match_intro (pq: Seq.seq pq_entry) (active: list forest_entry)
  (pf: (j:nat) -> Lemma
    (ensures (j < Seq.length pq ==> pq_entry_freq_ok (fst (Seq.index pq j)) (snd (Seq.index pq j)) active)))
  : Lemma (ensures pq_tree_freq_match pq active)
  = Classical.forall_intro pf;
    reveal_opaque (`%pq_tree_freq_match) pq_tree_freq_match

let pq_tree_freq_match_elim (pq: Seq.seq pq_entry) (active: list forest_entry) (j: nat)
  : Lemma (requires pq_tree_freq_match pq active /\ j < Seq.length pq)
          (ensures pq_entry_freq_ok (fst (Seq.index pq j)) (snd (Seq.index pq j)) active)
  = reveal_opaque (`%pq_tree_freq_match) pq_tree_freq_match

let pq_tree_freq_match_elim_mem (pq: Seq.seq pq_entry) (active: list forest_entry) (y: pq_entry)
  : Lemma (requires pq_tree_freq_match pq active /\ Seq.mem y pq)
          (ensures pq_entry_freq_ok (fst y) (snd y) active)
  = reveal_opaque (`%pq_tree_freq_match) pq_tree_freq_match;
    FStar.Seq.Properties.mem_index y pq

let pq_no_idx_intro (pq: Seq.seq pq_entry) (idx: SZ.t)
  : Lemma (requires forall (j: nat). j < Seq.length pq ==> snd (Seq.index pq j) <> idx)
          (ensures pq_no_idx pq idx)
  = reveal_opaque (`%pq_no_idx) pq_no_idx

let pq_no_idx_elim_mem (pq: Seq.seq pq_entry) (idx: SZ.t) (y: pq_entry)
  : Lemma (requires pq_no_idx pq idx /\ Seq.mem y pq)
          (ensures snd y <> idx)
  = reveal_opaque (`%pq_no_idx) pq_no_idx;
    FStar.Seq.Properties.mem_index y pq

// ========== Section 2: PQ minimum vs forest root freqs ==========

let pq_min_le_forest_root_freqs
  (pq: Seq.seq pq_entry) (active: list forest_entry) (fmin: int) (imin: SZ.t) (k: nat)
  : Lemma (requires
      PQ.is_minimum (fmin, imin) pq /\
      pq_tree_freq_match pq active /\
      forest_has_pq_entry pq active /\
      forest_distinct_indices active /\
      pq_indices_in_forest pq active /\
      k < L.length active)
    (ensures fmin <= HSpec.freq_of (entry_tree (L.index active k)))
  = reveal_opaque (`%forest_has_pq_entry) forest_has_pq_entry;
    find_pq_idx_spec pq (entry_idx (L.index active k)) 0;
    let Some j = find_pq_idx pq (entry_idx (L.index active k)) 0 in
    pq_tree_freq_match_elim pq active j;
    pq_entry_freq_ok_elim (fst (Seq.index pq j)) (snd (Seq.index pq j)) active;
    find_entry_by_idx_unique active k (entry_idx (L.index active k))

let rec forest_root_freqs_mem (active: list forest_entry) (x: pos)
  : Lemma (requires L.mem x (forest_root_freqs active))
          (ensures exists (k: nat). k < L.length active /\ HSpec.freq_of (entry_tree (L.index active k)) == x)
          (decreases active)
  = match active with
    | e :: rest ->
        if HSpec.freq_of (entry_tree e) = x then ()
        else begin
          forest_root_freqs_mem rest x;
          assert (exists (k: nat). k < L.length rest /\ HSpec.freq_of (entry_tree (L.index rest k)) == x);
          let aux () : Lemma (exists (k: nat). k < L.length active /\ HSpec.freq_of (entry_tree (L.index active k)) == x)
            = Classical.exists_elim
                (exists (k: nat). k < L.length active /\ HSpec.freq_of (entry_tree (L.index active k)) == x)
                #_
                #(fun (k: nat) -> k < L.length rest /\ HSpec.freq_of (entry_tree (L.index rest k)) == x)
                ()
                (fun k -> assert (L.index active (k + 1) == L.index rest k))
          in
          aux ()
        end

let pq_min_le_all_root_freqs
  (pq: Seq.seq pq_entry) (active: list forest_entry) (fmin: int) (imin: SZ.t)
  : Lemma (requires
      PQ.is_minimum (fmin, imin) pq /\
      pq_tree_freq_match pq active /\
      forest_has_pq_entry pq active /\
      forest_distinct_indices active /\
      pq_indices_in_forest pq active)
    (ensures forall (x: pos). L.mem x (forest_root_freqs active) ==> fmin <= x)
  = let aux (x: pos)
      : Lemma (requires L.mem x (forest_root_freqs active)) (ensures fmin <= x)
      = forest_root_freqs_mem active x;
        Classical.exists_elim (fmin <= x)
          #_
          #(fun (k: nat) -> k < L.length active /\ HSpec.freq_of (entry_tree (L.index active k)) == x)
          ()
          (fun k -> pq_min_le_forest_root_freqs pq active fmin imin k)
    in
    Classical.forall_intro (Classical.move_requires aux)

// Helper: PQ.is_minimum + Seq.mem implies fst comparison
let pq_min_le_mem_fst (x: pq_entry) (s: Seq.seq pq_entry) (y: pq_entry)
  : Lemma (requires PQ.is_minimum x s /\ Seq.mem y s)
          (ensures fst x <= fst y)
  = FStar.Seq.Properties.mem_index y s

// Helper: PQ.extends s0 s1 x means for y <> x, count y s1 == count y s0
// This manually unfolds the quantifier in PQ.extends for a specific y
let extends_count_other (#t:eqtype) {| Pulse.Lib.TotalOrder.total_order t |}
    (s0 s1: Seq.seq t) (x y: t)
  : Lemma (requires PQ.extends s0 s1 x /\ y =!= x /\ PQ.count y s1 >= 1)
          (ensures Seq.mem y s0)
  = assert (PQ.count y s0 == PQ.count y s1);
    assert (PQ.count y s0 >= 1)

// Helper: for index i in sequence s, count (index s i) s >= 1 (i.e., it's a member)
#push-options "--fuel 1 --ifuel 0"
let seq_index_count_pos (#t:eqtype) (s: Seq.seq t) (i: nat)
  : Lemma (requires i < Seq.length s)
          (ensures PQ.count (Seq.index s i) s >= 1)
  = let x = Seq.index s i in
    FStar.Seq.Properties.lemma_count_slice s i;
    let right = Seq.slice s i (Seq.length s) in
    assert (Seq.length right > 0);
    assert (Seq.head right == x);
    // With fuel 1: count x right = 1 + count x (tail right) >= 1
    assert (FStar.Seq.Properties.count x right >= 1)
#pop-options

// Corollary: extends_mem — if y is at index j of s1 and y <> x and PQ.extends s0 s1 x, then mem y s0
let extends_mem (#t:eqtype) {| Pulse.Lib.TotalOrder.total_order t |}
    (s0 s1: Seq.seq t) (x: t) (j: nat)
  : Lemma (requires PQ.extends s0 s1 x /\ j < Seq.length s1 /\ Seq.index s1 j =!= x)
          (ensures Seq.mem (Seq.index s1 j) s0)
  = let y = Seq.index s1 j in
    seq_index_count_pos s1 j;
    extends_count_other s0 s1 x y

// Helper: trace index from list_remove_two result back to original list
// Shows that rem[k] == active[k'] for some k' not equal to j1 or j2
#push-options "--z3rlimit 30"
private
let list_remove_two_trace (#a: Type) (active: list a) (j1 j2: nat) (k: nat)
  : Lemma (requires j1 < L.length active /\ j2 < L.length active /\ j1 <> j2 /\
                    k < L.length (list_remove_two active j1 j2))
          (ensures (let rem = list_remove_two active j1 j2 in
                    let rem1 = list_remove_at active j1 in
                    let j2' : nat = if j2 < j1 then j2 else j2 - 1 in
                    let k1 : nat = if k < j2' then k else k + 1 in
                    let k' : nat = if k1 < j1 then k1 else k1 + 1 in
                    k' < L.length active /\ k' <> j1 /\ k' <> j2 /\
                    L.index rem k == L.index active k'))
  = list_remove_at_length active j1;
    let rem1 = list_remove_at active j1 in
    let j2' : nat = if j2 < j1 then j2 else j2 - 1 in
    list_remove_at_length rem1 j2';
    list_remove_at_index rem1 j2' k;
    let k1 : nat = if k < j2' then k else k + 1 in
    list_remove_at_index active j1 k1;
    let k' : nat = if k1 < j1 then k1 else k1 + 1 in
    assert (k' < L.length active);
    assert (k' <> j1);
    // k' <> j2: explicit case analysis
    if j2 < j1 then begin
      // j2' = j2, k1 skips j2 in rem1
      // k1 = if k < j2 then k else k+1, so k1 <> j2
      assert (j2' == j2);
      assert (k1 <> j2);
      // k' = if k1 < j1 then k1 else k1+1
      // case k1 < j1: k' = k1 <> j2 (since k1 <> j2)
      // case k1 >= j1: k' = k1+1 >= j1+1 > j1 > j2, so k' > j2 <> k'
      if k1 < j1 then assert (k' <> j2)
      else assert (k' == k1 + 1 /\ k1 >= j1 /\ j1 > j2)
    end else begin
      // j2 > j1, j2' = j2-1, k1 skips j2-1 in rem1
      assert (j2' == j2 - 1);
      assert (k1 <> j2 - 1);
      // k' = if k1 < j1 then k1 else k1+1
      // case k1 < j1: k' = k1 < j1 < j2
      // case k1 >= j1: k' = k1+1, and k1 <> j2-1, so k1+1 <> j2
      if k1 < j1 then assert (k' == k1 /\ k1 < j1)
      else assert (k' == k1 + 1 /\ k1 <> j2 - 1)
    end
#pop-options

#push-options "--z3rlimit 800 --fuel 1 --ifuel 1 --split_queries always --z3refresh"
let freq2_le_at_rem_pos
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
  = let rem = list_remove_two active0 j1 j2 in
    list_remove_two_trace active0 j1 j2 k;
    let rem1 = list_remove_at active0 j1 in
    list_remove_at_length active0 j1;
    list_remove_two_length active0 j1 j2;
    let j2' : nat = if j2 < j1 then j2 else j2 - 1 in
    let k1 : nat = if k < j2' then k else k + 1 in
    let k' : nat = if k1 < j1 then k1 else k1 + 1 in
    assert (L.index rem k == L.index active0 k');
    assert (k' <> j1 /\ k' <> j2);
    // PART A: find PQ entry for k' in active0
    reveal_opaque (`%forest_has_pq_entry) forest_has_pq_entry;
    find_pq_idx_spec pq0 (entry_idx (L.index active0 k')) 0;
    let Some pj = find_pq_idx pq0 (entry_idx (L.index active0 k')) 0 in
    pq_tree_freq_match_elim pq0 active0 pj;
    pq_entry_freq_ok_elim (fst (Seq.index pq0 pj)) (snd (Seq.index pq0 pj)) active0;
    find_entry_by_idx_unique active0 k' (entry_idx (L.index active0 k'));
    forest_distinct_indices_elim active0 k' j1;
    assert (snd (Seq.index pq0 pj) <> idx1);
    let min_entry : pq_entry = (freq1, idx1) in
    assert (Seq.index pq0 pj <> min_entry);
    // pq0[pj] is in pq1 since pq0[pj] <> (freq1, idx1) and PQ.extends pq1 pq0 (freq1, idx1)
    seq_index_count_pos pq0 pj;
    extends_count_other pq1 pq0 (freq1, idx1) (Seq.index pq0 pj);
    // freq2 <= fst(any member of pq1) and freq(pq0[pj]) == freq_of(tree at k')
    pq_min_le_mem_fst (freq2, idx2) pq1 (Seq.index pq0 pj)
#pop-options

#push-options "--z3rlimit 200"
let freq2_le_remaining_root_freqs
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
  = let rem = list_remove_two active0 j1 j2 in
    list_remove_two_length active0 j1 j2;
    let aux (x: pos)
      : Lemma (requires L.mem x (forest_root_freqs rem))
              (ensures freq2 <= x)
      = forest_root_freqs_mem rem x;
        Classical.exists_elim (freq2 <= x)
          #_
          #(fun (k: nat) -> k < L.length rem /\ HSpec.freq_of (entry_tree (L.index rem k)) == x)
          ()
          (fun k -> freq2_le_at_rem_pos pq0 pq1 active0 freq1 freq2 idx1 idx2 j1 j2 k)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

// ========== Section 3: Maintaining pq_tree_freq_match ==========

let pq_tree_freq_match_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry) (active: list forest_entry)
  : Lemma (requires PQ.extends s1 s0 x /\ pq_tree_freq_match s0 active)
          (ensures pq_tree_freq_match s1 active)
  = let aux (j: nat)
      : Lemma (ensures (j < Seq.length s1 ==>
               pq_entry_freq_ok (fst (Seq.index s1 j)) (snd (Seq.index s1 j)) active))
      = if j < Seq.length s1 then begin
          let y = Seq.index s1 j in
          FStar.Seq.Properties.lemma_count_slice s1 j;
          FStar.Seq.Properties.mem_index y s0;
          pq_tree_freq_match_elim_mem s0 active y
        end
    in
    pq_tree_freq_match_intro s1 active aux

// ========== Section 4: Maintaining forest_has_pq_entry ==========

#push-options "--z3rlimit 50"
let forest_has_pq_entry_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry) (active: list forest_entry)
  : Lemma (requires PQ.extends s1 s0 x /\
                    forest_has_pq_entry s0 active /\
                    pq_idx_unique s0 /\
                    (forall (k: nat). k < L.length active ==> entry_idx (L.index active k) <> snd x))
          (ensures forest_has_pq_entry s1 active)
  = reveal_opaque (`%forest_has_pq_entry) forest_has_pq_entry;
    let aux (k: nat{k < L.length active})
      : Lemma (Some? (find_pq_idx s1 (entry_idx (L.index active k)) 0))
      = let idx = entry_idx (L.index active k) in
        find_pq_idx_spec s0 idx 0;
        let Some j0 = find_pq_idx s0 idx 0 in
        assert (j0 < Seq.length s0);
        let y = Seq.index s0 j0 in
        assert (snd y == idx);
        assert (snd x <> idx);
        assert (y <> x);
        FStar.Seq.Properties.lemma_count_slice s0 j0;
        assert (FStar.Seq.Properties.count y s0 > 0);
        assert (FStar.Seq.Properties.count y s1 > 0);
        FStar.Seq.Properties.mem_index y s1;
        find_pq_idx_spec s1 idx 0
    in
    Classical.forall_intro aux
#pop-options

let pq_tree_freq_match_init_step
  (s0 s1: Seq.seq pq_entry) (f: pos) (idx: SZ.t)
  (active_old: list forest_entry) (p: hnode_ptr)
  : Lemma (requires PQ.extends s0 s1 (f, idx) /\
                    pq_tree_freq_match s0 active_old /\
                    pq_indices_in_forest s0 active_old /\
                    (forall (k: nat). k < L.length active_old ==> entry_idx (L.index active_old k) <> idx))
          (ensures pq_tree_freq_match s1 ((idx, p, HSpec.Leaf 0 f) :: active_old))
  = let new_active = (idx, p, HSpec.Leaf 0 f) :: active_old in
    let aux (j: nat)
      : Lemma (ensures (j < Seq.length s1 ==>
               pq_entry_freq_ok (fst (Seq.index s1 j)) (snd (Seq.index s1 j)) new_active))
      = if j < Seq.length s1 then begin
          let y = Seq.index s1 j in
          if y = (f, idx) then begin
            find_entry_prepend active_old idx p (HSpec.Leaf 0 f);
            pq_entry_freq_ok_intro_at f idx new_active 0
          end else begin
            extends_mem s0 s1 (f, idx) j;
            pq_tree_freq_match_elim_mem s0 active_old y;
            pq_entry_freq_ok_elim (fst y) (snd y) active_old;
            find_entry_by_idx_spec active_old (snd y);
            find_entry_prepend_other active_old (idx, p, HSpec.Leaf 0 f) (snd y);
            reveal_opaque (`%pq_entry_freq_ok) pq_entry_freq_ok
          end
        end
    in
    pq_tree_freq_match_intro s1 new_active aux

#push-options "--z3rlimit 200"
let forest_has_pq_entry_init_step
  (s0 s1: Seq.seq pq_entry) (f: pos) (idx: SZ.t)
  (active_old: list forest_entry) (p: hnode_ptr)
  : Lemma (requires PQ.extends s0 s1 (f, idx) /\
                    forest_has_pq_entry s0 active_old /\
                    pq_idx_unique s0 /\
                    (forall (k: nat). k < L.length active_old ==> entry_idx (L.index active_old k) <> idx))
          (ensures forest_has_pq_entry s1 ((idx, p, HSpec.Leaf 0 f) :: active_old))
  = reveal_opaque (`%forest_has_pq_entry) forest_has_pq_entry;
    let new_active = (idx, p, HSpec.Leaf 0 f) :: active_old in
    let aux (k: nat{k < L.length new_active})
      : Lemma (Some? (find_pq_idx s1 (entry_idx (L.index new_active k)) 0))
      = if k = 0 then begin
          FStar.Seq.Properties.mem_index (f, idx) s1;
          find_pq_idx_spec s1 idx 0
        end
        else begin
          let old_k = k - 1 in
          let old_idx = entry_idx (L.index active_old old_k) in
          find_pq_idx_spec s0 old_idx 0;
          let Some j0 = find_pq_idx s0 old_idx 0 in
          let y = Seq.index s0 j0 in
          assert (y <> (f, idx));
          FStar.Seq.Properties.lemma_count_slice s0 j0;
          FStar.Seq.Properties.mem_index y s1;
          find_pq_idx_spec s1 old_idx 0
        end
    in
    Classical.forall_intro aux
#pop-options

let forest_has_pq_entry_remove_at (pq: Seq.seq pq_entry) (active: list forest_entry) (j: nat)
  : Lemma (requires forest_has_pq_entry pq active /\ j < L.length active)
          (ensures forest_has_pq_entry pq (list_remove_at active j))
  = reveal_opaque (`%forest_has_pq_entry) forest_has_pq_entry;
    list_remove_at_length active j;
    let aux (k: nat{k < L.length (list_remove_at active j)})
      : Lemma (Some? (find_pq_idx pq (entry_idx (L.index (list_remove_at active j) k)) 0))
      = list_remove_at_index active j k;
        let k' = if k < j then k else k + 1 in
        assert (L.index (list_remove_at active j) k == L.index active k')
    in
    Classical.forall_intro aux

#push-options "--z3rlimit 200"
let forest_has_pq_entry_prepend
  (s0 s1: Seq.seq pq_entry) (f: pos) (idx: SZ.t)
  (active_old: list forest_entry) (e: forest_entry)
  : Lemma (requires PQ.extends s0 s1 (f, idx) /\
                    entry_idx e == idx /\
                    forest_has_pq_entry s0 active_old /\
                    pq_idx_unique s0 /\
                    (forall (k: nat). k < L.length active_old ==> entry_idx (L.index active_old k) <> idx))
          (ensures forest_has_pq_entry s1 (e :: active_old))
  = reveal_opaque (`%forest_has_pq_entry) forest_has_pq_entry;
    let new_active = e :: active_old in
    let aux (k: nat{k < L.length new_active})
      : Lemma (Some? (find_pq_idx s1 (entry_idx (L.index new_active k)) 0))
      = if k = 0 then begin
          FStar.Seq.Properties.mem_index (f, idx) s1;
          find_pq_idx_spec s1 idx 0
        end
        else begin
          let old_k = k - 1 in
          let old_idx = entry_idx (L.index active_old old_k) in
          find_pq_idx_spec s0 old_idx 0;
          let Some j0 = find_pq_idx s0 old_idx 0 in
          let y = Seq.index s0 j0 in
          assert (y <> (f, idx));
          FStar.Seq.Properties.lemma_count_slice s0 j0;
          FStar.Seq.Properties.mem_index y s1;
          find_pq_idx_spec s1 old_idx 0
        end
    in
    Classical.forall_intro aux
#pop-options

// ========== Section 5: Merge step helpers ==========

#push-options "--z3rlimit 200 --split_queries always --z3refresh"
let list_remove_two_preserves_entry (entries: list forest_entry) (j1 j2 k: nat)
  : Lemma (requires j1 < L.length entries /\ j2 < L.length entries /\ j1 <> j2 /\
                    k < L.length entries /\ k <> j1 /\ k <> j2 /\
                    forest_distinct_indices entries /\
                    forest_distinct_indices (list_remove_two entries j1 j2))
          (ensures (let rem = list_remove_two entries j1 j2 in
                    let idx = entry_idx (L.index entries k) in
                    match find_entry_by_idx rem idx with
                    | Some kr -> kr < L.length rem /\ L.index rem kr == L.index entries k
                    | None -> False))
  = let rem = list_remove_two entries j1 j2 in
    let idx = entry_idx (L.index entries k) in
    let inter = list_remove_at entries j1 in
    list_remove_at_length entries j1;
    assert (L.length inter == L.length entries - 1);
    list_remove_two_length entries j1 j2;
    assert (L.length rem == L.length entries - 2);
    // First removal: entries -> inter, position k becomes k_inter
    let k_inter : nat = if k < j1 then k else k - 1 in
    assert (k_inter < L.length inter);
    list_remove_at_index entries j1 k_inter;
    assert (L.index inter k_inter == L.index entries k);
    // Second removal: inter -> rem, j2 becomes j2' after first removal
    let j2' : nat = if j2 < j1 then j2 else j2 - 1 in
    assert (j2' < L.length inter);
    // k_inter <> j2': follows from k <> j2, with case analysis on j1 position
    assert (k_inter <> j2');
    let k_final : nat = if k_inter < j2' then k_inter else k_inter - 1 in
    assert (k_final < L.length rem);
    list_remove_at_index inter j2' k_final;
    assert (L.index rem k_final == L.index inter k_inter);
    assert (L.index rem k_final == L.index entries k);
    assert (entry_idx (L.index rem k_final) == idx);
    find_entry_by_idx_unique rem k_final idx
#pop-options

let pq_entry_freq_ok_remove_two
  (f: int) (idx: SZ.t) (active0: list forest_entry) (j1 j2: nat)
  : Lemma (requires pq_entry_freq_ok f idx active0 /\
                    j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
                    idx <> entry_idx (L.index active0 j1) /\
                    idx <> entry_idx (L.index active0 j2) /\
                    forest_distinct_indices active0 /\
                    forest_distinct_indices (list_remove_two active0 j1 j2))
          (ensures pq_entry_freq_ok f idx (list_remove_two active0 j1 j2))
  = reveal_opaque (`%pq_entry_freq_ok) pq_entry_freq_ok;
    find_entry_by_idx_spec active0 idx;
    let k0 = Some?.v (find_entry_by_idx active0 idx) in
    list_remove_two_preserves_entry active0 j1 j2 k0

let pq_entry_freq_ok_prepend
  (f: int) (idx: SZ.t) (entries: list forest_entry) (e: forest_entry)
  : Lemma (requires pq_entry_freq_ok f idx entries /\ idx <> entry_idx e)
          (ensures pq_entry_freq_ok f idx (e :: entries))
  = reveal_opaque (`%pq_entry_freq_ok) pq_entry_freq_ok;
    find_entry_prepend_other entries e idx

let pq_merge_step_single_mem
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
  = let rem = list_remove_two active0 j1 j2 in
    let new_entry : forest_entry = (idx1, merged, HSpec.Internal sum_freq t1 t2) in
    pq_entry_freq_ok_remove_two (fst y) (snd y) active0 j1 j2;
    pq_entry_freq_ok_prepend (fst y) (snd y) rem new_entry

#push-options "--split_queries always"
let merge_step_new_entry_freq_ok
  (rem: list forest_entry) (idx1: SZ.t) (merged: hnode_ptr) (sum_freq: pos)
  (t1 t2: HSpec.htree)
  : Lemma (requires sum_freq == HSpec.freq_of t1 + HSpec.freq_of t2)
          (ensures pq_entry_freq_ok sum_freq idx1
    ((idx1, merged, HSpec.Internal sum_freq t1 t2) :: rem))
  = let na = (idx1, merged, HSpec.Internal sum_freq t1 t2) :: rem in
    find_entry_prepend rem idx1 merged (HSpec.Internal sum_freq t1 t2);
    assert (find_entry_by_idx na idx1 == Some 0);
    assert (0 < L.length na);
    assert (L.index na 0 == (idx1, merged, HSpec.Internal sum_freq t1 t2));
    assert (entry_tree (L.index na 0) == HSpec.Internal sum_freq t1 t2);
    assert (HSpec.freq_of (HSpec.Internal sum_freq t1 t2) == HSpec.freq_of t1 + HSpec.freq_of t2);
    pq_entry_freq_ok_intro_at sum_freq idx1 na 0
#pop-options

#push-options "--z3rlimit 120"
let pq_tree_freq_match_merge_step
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
  = let rem = list_remove_two active0 j1 j2 in
    let new_entry : forest_entry = (idx1, merged, HSpec.Internal sum_freq t1 t2) in
    let new_active = new_entry :: rem in
    let aux (j: nat)
      : Lemma (ensures (j < Seq.length pq3 ==>
               pq_entry_freq_ok (fst (Seq.index pq3 j)) (snd (Seq.index pq3 j)) new_active))
      = if j < Seq.length pq3 then begin
          let y = Seq.index pq3 j in
          if y = (sum_freq, idx1) then begin
            merge_step_new_entry_freq_ok rem idx1 merged sum_freq t1 t2;
            assert (fst y == sum_freq /\ snd y == idx1)
          end else begin
            // y is in pq2 (extends preserves counts for y <> new entry)
            FStar.Seq.Properties.lemma_count_slice pq3 j;
            // Get freq_ok for y from pq2 (opaque: no quantifier in context)
            pq_tree_freq_match_elim_mem pq2 active0 y;
            // Derive snd y <> idx1 and snd y <> entry_idx(active0[j2]) via opaque elim
            pq_no_idx_elim_mem pq2 idx1 y;
            pq_no_idx_elim_mem pq2 (entry_idx (L.index active0 j2)) y;
            // Transfer through remove_two + prepend
            pq_merge_step_single_mem active0 y j1 j2 idx1 merged sum_freq t1 t2
          end
        end
    in
    pq_tree_freq_match_intro pq3 new_active aux
#pop-options

// ========== Section 6: Bundle management ==========

let init_bundle_intro_empty (freq_seq: Seq.seq int) (nd_contents: Seq.seq hnode_ptr) (n: nat)
  : Lemma (requires Seq.length nd_contents == n)
          (ensures init_bundle freq_seq nd_contents Seq.empty [] 0 n)
  = reveal_opaque (`%init_bundle) init_bundle;
    reveal_opaque (`%forest_has_pq_entry) forest_has_pq_entry;
    reveal_opaque (`%pq_idx_unique) pq_idx_unique;
    reveal_opaque (`%forest_distinct_indices) forest_distinct_indices;
    pq_tree_freq_match_intro Seq.empty [] (fun _ -> ())

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
let init_bundle_step
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
      init_bundle freq_seq nd_new pq_new ((vi, leaf, HSpec.Leaf 0 freq_val) :: active_old) (SZ.v vi + 1) (SZ.v n))
  = reveal_opaque (`%init_bundle) init_bundle;
    let new_entry : forest_entry = (vi, leaf, HSpec.Leaf 0 freq_val) in
    // valid_pq_entries, pq_freqs_positive
    valid_pq_entries_extends pq_old pq_new (freq_val, vi) (SZ.v n);
    pq_freqs_positive_extends pq_old pq_new (freq_val, vi);
    // pq_idx_unique
    pq_idx_lt_bound pq_old active_old vi;
    pq_idx_unique_extends pq_old pq_new (freq_val, vi);
    // forest_distinct_indices
    forest_idx_fresh active_old vi;
    forest_distinct_indices_prepend active_old new_entry;
    // pq_indices_in_forest
    pq_forest_prepend pq_old active_old new_entry;
    find_entry_prepend active_old vi leaf (HSpec.Leaf 0 freq_val);
    pq_forest_extends pq_old pq_new (freq_val, vi) (new_entry :: active_old);
    // pq_tree_freq_match
    pq_tree_freq_match_init_step pq_old pq_new freq_val vi active_old leaf;
    // forest_has_pq_entry
    forest_has_pq_entry_init_step pq_old pq_new freq_val vi active_old leaf;
    // node-ptr correspondence
    node_ptr_correspondence_init_step active_old vi leaf (HSpec.Leaf 0 freq_val) nd_old n;
    // leaf frequency multiset
    all_leaf_freqs_init_step active_old vi leaf freq_val freq_seq (SZ.v vi)
#pop-options

#push-options "--z3rlimit 300 --fuel 1 --ifuel 0"
let init_to_merge_bundle
  (freq_seq: Seq.seq int) (nd_contents: Seq.seq hnode_ptr)
  (pq: Seq.seq pq_entry) (active: list forest_entry) (n: nat)
  : Lemma (requires init_bundle freq_seq nd_contents pq active n n /\
                    SZ.fits n /\
                    Seq.length nd_contents == n /\
                    Seq.length freq_seq == n /\
                    L.length active == n /\ Seq.length pq == n /\ n > 0)
          (ensures merge_bundle freq_seq nd_contents pq active n)
  = reveal_opaque (`%init_bundle) init_bundle;
    reveal_opaque (`%merge_bundle) merge_bundle;
    assert (forest_total_cost active == 0);
    // forest_total_cost == 0 → root_freqs == leaf_freqs
    Classical.forall_intro (Classical.move_requires (cost_zero_root_eq_leaf_freqs active));
    // greedy_cost(root_freqs) == greedy_cost(initial_freqs) by multiset invariance
    HOpt.greedy_cost_multiset_invariant
      (forest_root_freqs active)
      (seq_to_pos_list freq_seq 0)
#pop-options

let merge_bundle_elim (freq_seq: Seq.seq int) (nd_contents: Seq.seq hnode_ptr)
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
  = reveal_opaque (`%merge_bundle) merge_bundle

let merge_bundle_intro (freq_seq: Seq.seq int) (nd_contents: Seq.seq hnode_ptr)
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
  = reveal_opaque (`%merge_bundle) merge_bundle

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1 --split_queries always"
let cost_invariant_from_merge_bundle
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
  = // Pure helpers first (before merge_bundle_elim pollutes context)
    // Multiset decomposition (pure, only needs j1 <> j2 bounds)
    forest_root_freqs_remove_two_forall active0 j1 j2;
    // Length
    forest_root_freqs_length active0;
    // Now reveal bundle for PQ-dependent properties
    merge_bundle_elim freq_seq nd_old pq0 active0 n;
    // freq1 <= all root freqs: use pq_min_le_all_root_freqs
    pq_min_le_all_root_freqs pq0 active0 freq1 idx1;
    // freq2 <= remaining root freqs: dedicated lemma
    freq2_le_remaining_root_freqs pq0 pq1 active0 freq1 freq2 idx1 idx2 j1 j2
#pop-options

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1 --split_queries always --z3refresh"
private
let merge_bundle_step_aux
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
      PQ.is_minimum (freq1, idx1) pq0 /\
      PQ.extends pq1 pq0 (freq1, idx1) /\
      PQ.is_minimum (freq2, idx2) pq1 /\
      PQ.extends pq2 pq1 (freq2, idx2) /\
      Seq.length pq1 == Seq.length pq0 - 1 /\
      Seq.length pq2 == Seq.length pq1 - 1 /\
      PQ.extends pq2 pq3 (sum_freq, idx1) /\
      Seq.length pq3 == Seq.length pq2 + 1 /\
      sum_freq == freq1 + freq2 /\
      Seq.length nd_old == n /\
      SZ.v idx1 < n /\ SZ.v idx2 < n /\
      nd_new == Seq.upd nd_old (SZ.v idx1) merged /\
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
       SZ.fits n /\
       Seq.length nd_new == n /\
       valid_pq_entries pq3 n /\
       pq_freqs_positive pq3 /\
       pq_idx_unique pq3 /\
       pq_indices_in_forest pq3 new_active /\
       pq_tree_freq_match pq3 new_active /\
       forest_has_pq_entry pq3 new_active /\
       forest_distinct_indices new_active /\
       (forall (k: nat). k < L.length new_active ==>
         SZ.v (entry_idx (L.index new_active k)) < n /\
         Seq.index nd_new (SZ.v (entry_idx (L.index new_active k))) == entry_ptr (L.index new_active k)) /\
       (forall (x: pos). L.count x (all_leaf_freqs new_active) == L.count x (seq_to_pos_list freq_seq 0)) /\
       forest_total_cost new_active + HOpt.greedy_cost (forest_root_freqs new_active) ==
         HOpt.greedy_cost (seq_to_pos_list freq_seq 0)))
  = // Extract facts from precondition
    merge_bundle_elim freq_seq nd_old pq0 active0 n;
    let t1 = entry_tree (L.index active0 j1) in
    let t2 = entry_tree (L.index active0 j2) in
    let new_tree = HSpec.Internal sum_freq t1 t2 in
    let rem = list_remove_two active0 j1 j2 in
    let new_active = (idx1, merged, new_tree) :: rem in
    // Derive freq equalities: freq1 == freq_of t1, freq2 == freq_of t2
    pq_tree_freq_match_elim_mem pq0 active0 (freq1, idx1);
    pq_entry_freq_ok_elim freq1 idx1 active0;
    pq_tree_freq_match_shrink pq0 pq1 (freq1, idx1) active0;
    pq_tree_freq_match_elim_mem pq1 active0 (freq2, idx2);
    pq_entry_freq_ok_elim freq2 idx2 active0;
    // PQ maintenance
    valid_pq_entries_shrink pq0 pq1 (freq1, idx1) n;
    pq_freqs_positive_shrink pq0 pq1 (freq1, idx1);
    pq_idx_unique_shrink pq0 pq1 (freq1, idx1);
    pq_forest_shrink pq0 pq1 (freq1, idx1) active0;
    valid_pq_entries_shrink pq1 pq2 (freq2, idx2) n;
    pq_freqs_positive_shrink pq1 pq2 (freq2, idx2);
    pq_idx_unique_shrink pq1 pq2 (freq2, idx2);
    pq_no_idx_preserved pq1 pq2 (freq2, idx2) idx1;
    pq_no_idx_intro pq2 idx1;
    pq_no_idx_intro pq2 (entry_idx (L.index active0 j2));
    pq_forest_shrink pq1 pq2 (freq2, idx2) active0;
    valid_pq_entries_extends pq2 pq3 (sum_freq, idx1) n;
    pq_freqs_positive_extends pq2 pq3 (sum_freq, idx1);
    pq_idx_unique_extends pq2 pq3 (sum_freq, idx1);
    // pq_indices_in_forest
    pq_forest_remove_two pq2 active0 j1 j2;
    pq_forest_prepend pq2 rem (idx1, merged, new_tree);
    find_entry_prepend rem idx1 merged new_tree;
    pq_forest_extends pq2 pq3 (sum_freq, idx1) new_active;
    // forest_distinct_indices
    forest_distinct_indices_after_merge active0 j1 j2 idx1 merged new_tree;
    // node-ptr correspondence
    node_ptr_correspondence_upd_nat active0 j1 j2 idx1 merged new_tree nd_old n;
    // leaf-freqs multiset
    all_leaf_freqs_merge_step_full active0 j1 j2 idx1 merged sum_freq (seq_to_pos_list freq_seq 0);
    // pq_tree_freq_match
    forest_distinct_indices_remove_two active0 j1 j2;
    pq_tree_freq_match_shrink pq0 pq1 (freq1, idx1) active0;
    pq_tree_freq_match_shrink pq1 pq2 (freq2, idx2) active0;
    pq_tree_freq_match_merge_step pq2 pq3 active0 j1 j2 idx1 freq1 freq2 merged t1 t2 sum_freq;
    // forest_has_pq_entry
    forest_has_pq_entry_remove_at pq0 active0 j1;
    assert (j1 < j2 \/ j2 < j1);
    let j2' : nat = if j2 < j1 then j2 else (assert (j2 > 0); j2 - 1) in
    list_remove_at_length active0 j1;
    forest_has_pq_entry_remove_at pq0 (list_remove_at active0 j1) j2';
    list_remove_two_no_idx active0 j1 j2 idx1;
    forest_has_pq_entry_shrink pq0 pq1 (freq1, idx1) rem;
    list_remove_two_length active0 j1 j2;
    let rem1 = list_remove_at active0 j1 in
    list_remove_at_length active0 j1;
    forest_distinct_indices_remove_at active0 j1;
    list_remove_at_index active0 j1 j2';
    list_remove_at_no_idx rem1 j2' idx2;
    forest_has_pq_entry_shrink pq1 pq2 (freq2, idx2) rem;
    forest_has_pq_entry_prepend pq2 pq3 sum_freq idx1 rem (idx1, merged, new_tree);
    // Cost invariant
    cost_invariant_from_merge_bundle freq_seq nd_old pq0 pq1 active0 n
      freq1 freq2 idx1 idx2 j1 j2;
    cost_invariant_merge_step active0 j1 j2 freq1 freq2 sum_freq idx1 merged
      t1 t2 (seq_to_pos_list freq_seq 0)
#pop-options

let merge_bundle_step
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
      PQ.is_minimum (freq1, idx1) pq0 /\
      PQ.extends pq1 pq0 (freq1, idx1) /\
      PQ.is_minimum (freq2, idx2) pq1 /\
      PQ.extends pq2 pq1 (freq2, idx2) /\
      Seq.length pq1 == Seq.length pq0 - 1 /\
      Seq.length pq2 == Seq.length pq1 - 1 /\
      PQ.extends pq2 pq3 (sum_freq, idx1) /\
      Seq.length pq3 == Seq.length pq2 + 1 /\
      sum_freq == freq1 + freq2 /\
      Seq.length nd_old == n /\
      SZ.v idx1 < n /\ SZ.v idx2 < n /\
      nd_new == Seq.upd nd_old (SZ.v idx1) merged /\
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
  = merge_bundle_step_aux freq_seq nd_old nd_new pq0 pq1 pq2 pq3 active0 n
      freq1 freq2 idx1 idx2 sum_freq merged j1 j2;
    let t1 = entry_tree (L.index active0 j1) in
    let t2 = entry_tree (L.index active0 j2) in
    let new_tree = HSpec.Internal sum_freq t1 t2 in
    let new_active = (idx1, merged, new_tree) :: list_remove_two active0 j1 j2 in
    merge_bundle_intro freq_seq nd_new pq3 new_active n

#pop-options // module-level z3rlimit 8
