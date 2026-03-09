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

#push-options "--z3rlimit 8"

// ========== Section 1: Forest-PQ structural lemmas ==========

let pq_forest_extends (s0 s1: Seq.seq pq_entry) (x: pq_entry) (forest: list forest_entry)
  : Lemma (requires PQ.extends s0 s1 x /\
                    pq_indices_in_forest s0 forest /\
                    Some? (find_entry_by_idx forest (snd x)))
          (ensures pq_indices_in_forest s1 forest)
  = let aux (j: nat{j < Seq.length s1})
      : Lemma (Some? (find_entry_by_idx forest (snd (Seq.index s1 j)))) =
      let y = Seq.index s1 j in
      if y = x then ()
      else begin
        assert (Seq.mem y s1);
        assert (PQ.count y s1 == PQ.count y s0);
        assert (Seq.mem y s0);
        FStar.Seq.Properties.mem_index y s0
      end
    in
    Classical.forall_intro aux

// pq_indices_in_forest after shrink (extract_min): remaining entries still in forest
let pq_forest_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry) (forest: list forest_entry)
  : Lemma (requires PQ.extends s1 s0 x /\ pq_indices_in_forest s0 forest)
          (ensures pq_indices_in_forest s1 forest /\
                   Some? (find_entry_by_idx forest (snd x)))
  = assert (FStar.Seq.Properties.count x s0 > 0);
    FStar.Seq.Properties.mem_index x s0;
    let aux (j: nat{j < Seq.length s1})
      : Lemma (Some? (find_entry_by_idx forest (snd (Seq.index s1 j)))) =
      let y = Seq.index s1 j in
      if y = x then (FStar.Seq.Properties.mem_index x s0)
      else begin
        assert (Seq.mem y s1);
        assert (PQ.count y s1 == PQ.count y s0);
        assert (Seq.mem y s0);
        FStar.Seq.Properties.mem_index y s0
      end
    in
    Classical.forall_intro aux

// After prepending (idx, p, ft) to forest, find_entry_by_idx for idx succeeds
let find_entry_prepend (entries: list forest_entry) (idx: SZ.t) (p: hnode_ptr) (ft: HSpec.htree)
  : Lemma (ensures Some? (find_entry_by_idx ((idx, p, ft) :: entries) idx) /\
                   find_entry_by_idx ((idx, p, ft) :: entries) idx == Some 0)
  = ()

// Prepending to forest preserves find_entry_by_idx for existing entries
let find_entry_prepend_other (entries: list forest_entry) (e: forest_entry) (idx: SZ.t)
  : Lemma (ensures Some? (find_entry_by_idx entries idx) ==>
                   Some? (find_entry_by_idx (e :: entries) idx))
  = match entries with
    | [] -> ()
    | _ :: _ -> ()

// pq_indices_in_forest is preserved by prepending to forest
let pq_forest_prepend (pq: Seq.seq pq_entry) (forest: list forest_entry) (e: forest_entry)
  : Lemma (requires pq_indices_in_forest pq forest)
          (ensures pq_indices_in_forest pq (e :: forest))
  = let aux (j: nat{j < Seq.length pq}) : Lemma (Some? (find_entry_by_idx (e :: forest) (snd (Seq.index pq j)))) =
      find_entry_prepend_other forest e (snd (Seq.index pq j))
    in
    Classical.forall_intro (Classical.move_requires aux)

// Removing entry at position j preserves find_entry_by_idx for other indices
let rec find_entry_remove_other (entries: list forest_entry) (j: nat{j < L.length entries}) (idx: SZ.t)
  : Lemma (requires entry_idx (L.index entries j) =!= idx /\
                    Some? (find_entry_by_idx entries idx))
          (ensures Some? (find_entry_by_idx (list_remove_at entries j) idx))
          (decreases entries)
  = match entries with
    | hd :: tl ->
      if j = 0 then begin
        // Removing head, idx must be in tl since head has different index
        if entry_idx hd = idx then () // impossible, but F* should see this
        else begin
          match find_entry_by_idx tl idx with
          | Some _ -> ()
          | None -> find_entry_by_idx_spec tl idx
        end
      end
      else begin
        // j > 0: removing from tail
        if entry_idx hd = idx then ()  // hd has idx, so result is hd :: remove(tl, j-1), still has hd
        else begin
          find_entry_by_idx_spec tl idx;
          find_entry_remove_other tl (j - 1) idx;
          find_entry_by_idx_spec (list_remove_at tl (j - 1)) idx
        end
      end

// pq_indices_in_forest after removing entry j (if all PQ entries have index ≠ entry_idx(entries[j]))
let pq_forest_remove (pq: Seq.seq pq_entry) (forest: list forest_entry) (j: nat{j < L.length forest})
  : Lemma (requires pq_indices_in_forest pq forest /\
                    (forall (k: nat). k < Seq.length pq ==> snd (Seq.index pq k) =!= entry_idx (L.index forest j)))
          (ensures pq_indices_in_forest pq (list_remove_at forest j))
  = let aux (k: nat{k < Seq.length pq})
      : Lemma (Some? (find_entry_by_idx (list_remove_at forest j) (snd (Seq.index pq k)))) =
      find_entry_remove_other forest j (snd (Seq.index pq k))
    in
    Classical.forall_intro aux

// pq_indices_in_forest after removing two entries (if no PQ entry has either removed index)
#push-options "--z3rlimit 15"
let pq_forest_remove_two (pq: Seq.seq pq_entry) (forest: list forest_entry)
  (j1 j2: nat)
  : Lemma (requires j1 < L.length forest /\ j2 < L.length forest /\ j1 <> j2 /\
                    pq_indices_in_forest pq forest /\
                    (forall (k: nat). k < Seq.length pq ==>
                      snd (Seq.index pq k) =!= entry_idx (L.index forest j1) /\
                      snd (Seq.index pq k) =!= entry_idx (L.index forest j2)))
          (ensures pq_indices_in_forest pq (list_remove_two forest j1 j2))
  = pq_forest_remove pq forest j1;
    list_remove_at_length forest j1;
    let rem1 = list_remove_at forest j1 in
    let j2' = if j2 < j1 then j2 else j2 - 1 in
    list_remove_at_index forest j1 j2';
    pq_forest_remove pq rem1 j2'
#pop-options

// forest_distinct_indices is preserved by list_remove_at
let forest_distinct_indices_remove_at (entries: list forest_entry) (j: nat)
  : Lemma (requires forest_distinct_indices entries /\ j < L.length entries)
          (ensures forest_distinct_indices (list_remove_at entries j))
  = reveal_opaque (`%forest_distinct_indices) forest_distinct_indices;
    let rem = list_remove_at entries j in
    list_remove_at_length entries j;
    let aux (i1 i2: nat)
      : Lemma (ensures (i1 < L.length rem /\ i2 < L.length rem /\ i1 <> i2) ==>
                       entry_idx (L.index rem i1) <> entry_idx (L.index rem i2))
      = if i1 < L.length rem && i2 < L.length rem && i1 <> i2 then begin
          list_remove_at_index entries j i1;
          list_remove_at_index entries j i2
        end
    in
    Classical.forall_intro_2 aux

// forest_distinct_indices is preserved by list_remove_two
let forest_distinct_indices_remove_two (entries: list forest_entry) (j1 j2: nat)
  : Lemma (requires forest_distinct_indices entries /\ j1 < L.length entries /\
                    j2 < L.length entries /\ j1 <> j2)
          (ensures forest_distinct_indices (list_remove_two entries j1 j2))
  = forest_distinct_indices_remove_at entries j1;
    list_remove_at_length entries j1;
    let j2' = if j2 < j1 then j2 else j2 - 1 in
    forest_distinct_indices_remove_at (list_remove_at entries j1) j2'

// Entry at position j has index idx implies no other entry in list_remove_at has that index
let list_remove_at_no_idx (entries: list forest_entry) (j: nat) (idx: SZ.t)
  : Lemma (requires forest_distinct_indices entries /\ j < L.length entries /\
                    entry_idx (L.index entries j) == idx)
          (ensures forall (k: nat). k < L.length (list_remove_at entries j) ==>
                    entry_idx (L.index (list_remove_at entries j) k) <> idx)
  = list_remove_at_length entries j;
    let aux (k: nat)
      : Lemma (ensures (k < L.length entries - 1) ==>
                       entry_idx (L.index (list_remove_at entries j) k) <> idx)
      = if k < L.length entries - 1 then begin
          list_remove_at_index entries j k;
          // list_remove_at_index gives:
          //   L.index (list_remove_at entries j) k == 
          //     if k < j then L.index entries k else L.index entries (k+1)
          if k < j then
            forest_distinct_indices_elim entries k j
          else
            forest_distinct_indices_elim entries (k + 1) j
        end
    in
    Classical.forall_intro aux

// No entry in list_remove_two has the index of the first removed entry
#push-options "--z3rlimit 30"
let list_remove_two_no_idx (entries: list forest_entry) (j1 j2: nat) (idx: SZ.t)
  : Lemma (requires forest_distinct_indices entries /\ j1 < L.length entries /\
                    j2 < L.length entries /\ j1 <> j2 /\
                    entry_idx (L.index entries j1) == idx)
          (ensures forall (k: nat). k < L.length (list_remove_two entries j1 j2) ==>
                    entry_idx (L.index (list_remove_two entries j1 j2) k) <> idx)
  = list_remove_at_no_idx entries j1 idx;
    list_remove_at_length entries j1;
    let rem1 = list_remove_at entries j1 in
    let j2' = if j2 < j1 then j2 else j2 - 1 in
    list_remove_at_length rem1 j2';
    let aux (k: nat)
      : Lemma (ensures (k < L.length (list_remove_two entries j1 j2)) ==>
                       entry_idx (L.index (list_remove_two entries j1 j2) k) <> idx)
      = if k < L.length rem1 - 1 then begin
          list_remove_at_index rem1 j2' k;
          ()
        end
    in
    Classical.forall_intro aux
#pop-options

// forest_distinct_indices is preserved by prepend if head index is fresh
#push-options "--z3rlimit 15"
let forest_distinct_indices_prepend (entries: list forest_entry) (e: forest_entry)
  : Lemma (requires forest_distinct_indices entries /\
                    (forall (k: nat). k < L.length entries ==>
                      entry_idx (L.index entries k) <> entry_idx e))
          (ensures forest_distinct_indices (e :: entries))
  = reveal_opaque (`%forest_distinct_indices) forest_distinct_indices;
    let l' = e :: entries in
    let aux (i j: nat)
      : Lemma (ensures (i < L.length l' /\ j < L.length l' /\ i <> j) ==>
                       entry_idx (L.index l' i) <> entry_idx (L.index l' j))
      = ()
    in
    Classical.forall_intro_2 aux
#pop-options

// Prove forest_distinct_indices for new_active after merge
let forest_distinct_indices_after_merge
  (active0: list forest_entry) (j1 j2: nat) (idx: SZ.t)
  (merged: hnode_ptr) (tree: HSpec.htree)
  : Lemma (requires forest_distinct_indices active0 /\
                    j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
                    entry_idx (L.index active0 j1) == idx)
          (ensures forest_distinct_indices
                    ((idx, merged, tree) :: list_remove_two active0 j1 j2))
  = forest_distinct_indices_remove_two active0 j1 j2;
    list_remove_two_no_idx active0 j1 j2 idx;
    forest_distinct_indices_prepend (list_remove_two active0 j1 j2) (idx, merged, tree)

// Node-pointer correspondence after Seq.upd at idx1
#push-options "--split_queries always --z3rlimit 100"
let node_ptr_correspondence_upd_tail
  (active0: list forest_entry) (j1 j2: nat)
  (idx1: SZ.t) (merged: hnode_ptr) (tree: HSpec.htree)
  (nd_contents: Seq.seq hnode_ptr) (n: SZ.t)
  (k: nat)
  : Lemma (requires
      forest_distinct_indices active0 /\
      j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
      entry_idx (L.index active0 j1) == idx1 /\
      SZ.v idx1 < Seq.length nd_contents /\
      Seq.length nd_contents == SZ.v n /\
      k < L.length (list_remove_two active0 j1 j2) /\
      (forall (k: nat). k < L.length active0 ==>
        SZ.v (entry_idx (L.index active0 k)) < SZ.v n /\
        Seq.index nd_contents (SZ.v (entry_idx (L.index active0 k))) == entry_ptr (L.index active0 k)))
    (ensures (
      let rem = list_remove_two active0 j1 j2 in
      let nd' = Seq.upd nd_contents (SZ.v idx1) merged in
      SZ.v (entry_idx (L.index rem k)) < SZ.v n /\
      Seq.index nd' (SZ.v (entry_idx (L.index rem k))) ==
      entry_ptr (L.index rem k)))
  = list_remove_at_length active0 j1;
    let rem1 = list_remove_at active0 j1 in
    let j2' = if j2 < j1 then j2 else j2 - 1 in
    list_remove_at_length rem1 j2';
    list_remove_at_index rem1 j2' k;
    let p1 = if k < j2' then k else k + 1 in
    list_remove_at_index active0 j1 p1;
    let orig = if p1 < j1 then p1 else p1 + 1 in
    assert (orig < L.length active0);
    assert (orig <> j1);
    forest_distinct_indices_elim active0 orig j1;
    Seq.lemma_index_upd2 nd_contents (SZ.v idx1) merged
      (SZ.v (entry_idx (L.index active0 orig)))
#pop-options

#push-options "--z3rlimit 30"
let node_ptr_correspondence_upd
  (active0: list forest_entry) (j1 j2: nat)
  (idx1: SZ.t) (merged: hnode_ptr) (tree: HSpec.htree)
  (nd_contents: Seq.seq hnode_ptr) (n: SZ.t)
  : Lemma (requires
      forest_distinct_indices active0 /\
      j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
      entry_idx (L.index active0 j1) == idx1 /\
      SZ.v idx1 < Seq.length nd_contents /\
      Seq.length nd_contents == SZ.v n /\
      (forall (k: nat). k < L.length active0 ==>
        SZ.v (entry_idx (L.index active0 k)) < SZ.v n /\
        Seq.index nd_contents (SZ.v (entry_idx (L.index active0 k))) == entry_ptr (L.index active0 k)))
    (ensures (
      let new_active = (idx1, merged, tree) :: list_remove_two active0 j1 j2 in
      let nd' = Seq.upd nd_contents (SZ.v idx1) merged in
      forall (k: nat). k < L.length new_active ==>
        SZ.v (entry_idx (L.index new_active k)) < SZ.v n /\
        Seq.index nd' (SZ.v (entry_idx (L.index new_active k))) ==
        entry_ptr (L.index new_active k)))
  = let new_active = (idx1, merged, tree) :: list_remove_two active0 j1 j2 in
    let nd' = Seq.upd nd_contents (SZ.v idx1) merged in
    list_remove_two_length active0 j1 j2;
    let aux (k: nat)
      : Lemma (ensures (k < L.length new_active) ==>
               (SZ.v (entry_idx (L.index new_active k)) < SZ.v n /\
                Seq.index nd' (SZ.v (entry_idx (L.index new_active k))) ==
                entry_ptr (L.index new_active k)))
      = if k < L.length new_active then begin
          if k = 0 then
            Seq.lemma_index_upd1 nd_contents (SZ.v idx1) merged
          else
            node_ptr_correspondence_upd_tail active0 j1 j2 idx1 merged tree nd_contents n (k - 1)
        end
    in
    Classical.forall_intro aux
#pop-options

// Wrapper for merge_bundle_step where n is nat (merge_bundle uses nat)
let node_ptr_correspondence_upd_nat
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
  = node_ptr_correspondence_upd active0 j1 j2 idx1 merged tree nd_contents (SZ.uint_to_t n)

// ========== Section 2: Init-step helpers ==========

let forest_idx_fresh (entries: list forest_entry) (bound: SZ.t)
  : Lemma (requires forall (k: nat). k < L.length entries ==> SZ.v (entry_idx (L.index entries k)) < SZ.v bound)
          (ensures forall (k: nat). k < L.length entries ==> entry_idx (L.index entries k) <> bound)
  = ()

// Node-ptr correspondence after prepending a new entry and doing Seq.upd at its index
let node_ptr_correspondence_init_step
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
  = let nd' = Seq.upd nd_old (SZ.v vi) leaf in
    Seq.lemma_index_upd1 nd_old (SZ.v vi) leaf;
    let aux (k: nat)
      : Lemma (ensures (k < L.length active_old) ==>
               (Seq.index nd' (SZ.v (entry_idx (L.index active_old k))) ==
                entry_ptr (L.index active_old k)))
      = if k < L.length active_old then
          Seq.lemma_index_upd2 nd_old (SZ.v vi) leaf
            (SZ.v (entry_idx (L.index active_old k)))
    in
    Classical.forall_intro aux

// ========== Section 3: Leaf frequency multiset tracking ==========

// Splitting all_leaf_freqs removing two positions
#push-options "--z3rlimit 15"
let all_leaf_freqs_remove_two (entries: list forest_entry) (j1 j2: nat) (x: pos)
  : Lemma (requires j1 < L.length entries /\ j2 < L.length entries /\ j1 <> j2)
          (ensures L.count x (all_leaf_freqs entries) ==
                   L.count x (HSpec.leaf_freqs (entry_tree (L.index entries j1))) +
                   L.count x (HSpec.leaf_freqs (entry_tree (L.index entries j2))) +
                   L.count x (all_leaf_freqs (list_remove_two entries j1 j2)))
  = all_leaf_freqs_remove_at entries j1 x;
    let rem1 = list_remove_at entries j1 in
    list_remove_at_length entries j1;
    let j2' = if j2 < j1 then j2 else j2 - 1 in
    all_leaf_freqs_remove_at rem1 j2' x;
    list_remove_at_index entries j1 j2';
    let orig2 = if j2' < j1 then j2' else j2' + 1 in
    assert (orig2 == j2)
#pop-options

// Merge preserves leaf frequency multiset
let all_leaf_freqs_merge_step
  (entries: list forest_entry) (j1 j2: nat) 
  (idx: SZ.t) (p: hnode_ptr) (f: pos) (x: pos)
  : Lemma (requires j1 < L.length entries /\ j2 < L.length entries /\ j1 <> j2)
          (ensures (
            let t1 = entry_tree (L.index entries j1) in
            let t2 = entry_tree (L.index entries j2) in
            let merged = HSpec.Internal f t1 t2 in
            let new_entries = (idx, p, merged) :: list_remove_two entries j1 j2 in
            L.count x (all_leaf_freqs new_entries) ==
            L.count x (all_leaf_freqs entries)))
  = let t1 = entry_tree (L.index entries j1) in
    let t2 = entry_tree (L.index entries j2) in
    let merged = HSpec.Internal f t1 t2 in
    let rem = list_remove_two entries j1 j2 in
    let new_entries = (idx, p, merged) :: rem in
    all_leaf_freqs_cons (idx, p, merged) rem x;
    assert (HSpec.leaf_freqs merged == L.append (HSpec.leaf_freqs t1) (HSpec.leaf_freqs t2));
    LP.append_count (HSpec.leaf_freqs t1) (HSpec.leaf_freqs t2) x;
    all_leaf_freqs_remove_two entries j1 j2 x

// Prepend Leaf preserves counts with extension
let all_leaf_freqs_prepend_leaf
  (entries: list forest_entry) (idx: SZ.t) (p: hnode_ptr) (f: pos) (x: pos)
  : Lemma (L.count x (all_leaf_freqs ((idx, p, HSpec.Leaf 0 f) :: entries)) ==
           L.count x (all_leaf_freqs entries) + (if x = f then 1 else 0))
  = all_leaf_freqs_cons (idx, p, HSpec.Leaf 0 f) entries x

// seq_to_pos_list extension: adding one more element
let seq_to_pos_list_snoc (s: Seq.seq int) (k: nat) (x: pos)
  : Lemma (requires k < Seq.length s /\ Seq.index s k > 0)
          (ensures (L.count x (seq_to_pos_list s k) ==
                    (if x = Seq.index s k then 1 else 0) + L.count x (seq_to_pos_list s (k + 1))))
  = ()

// When forest has exactly one entry, all_leaf_freqs = leaf_freqs of that tree
let all_leaf_freqs_singleton (e: forest_entry) (x: pos)
  : Lemma (L.count x (all_leaf_freqs [e]) == L.count x (HSpec.leaf_freqs (entry_tree e)))
  = all_leaf_freqs_cons e [] x

// Init step: prepending Leaf f to forest + consuming from seq_to_pos_list preserves multiset
let all_leaf_freqs_init_step
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
  = let aux (x: pos)
      : Lemma (L.count x (all_leaf_freqs ((idx, p, HSpec.Leaf 0 f) :: entries)) +
               L.count x (seq_to_pos_list s (k + 1)) ==
               L.count x (seq_to_pos_list s 0))
      = all_leaf_freqs_prepend_leaf entries idx p f x;
        seq_to_pos_list_snoc s k x
    in
    Classical.forall_intro aux

// Merge step: merging two trees in the forest preserves the full leaf multiset
let all_leaf_freqs_merge_step_full
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
  = let aux (x: pos)
      : Lemma (L.count x (all_leaf_freqs
                ((idx, p, HSpec.Internal f (entry_tree (L.index entries j1)) (entry_tree (L.index entries j2)))
                 :: list_remove_two entries j1 j2)) ==
               L.count x freqs)
      = all_leaf_freqs_merge_step entries j1 j2 idx p f x
    in
    Classical.forall_intro aux

// Singleton forest has same leaf multiset as the single tree
let all_leaf_freqs_singleton_full (entries: list forest_entry) (freqs: list pos)
  : Lemma (requires L.length entries == 1 /\
                    (forall (x: pos). L.count x (all_leaf_freqs entries) == L.count x freqs))
          (ensures HSpec.same_frequency_multiset (entry_tree (L.index entries 0)) freqs)
  = let aux (x: pos)
      : Lemma (L.count x (HSpec.leaf_freqs (entry_tree (L.index entries 0))) == L.count x freqs)
      = all_leaf_freqs_singleton (L.index entries 0) x
    in
    Classical.forall_intro aux

// ========== Section 4: Cost tracking lemmas ==========

// forest_total_cost of all Leaf entries is 0
let rec forest_total_cost_all_leaves (entries: list forest_entry)
  : Lemma (requires forall (k: nat). k < L.length entries ==>
                    HSpec.Leaf? (entry_tree (L.index entries k)))
          (ensures forest_total_cost entries == 0)
          (decreases entries)
  = match entries with
    | [] -> ()
    | e :: rest ->
        // head is Leaf (from precondition with k=0)
        assert (HSpec.Leaf? (entry_tree e));
        // Establish precondition for rest: shift indices by 1
        assert (forall (k: nat). k < L.length rest ==>
          L.index rest k == L.index entries (k + 1));
        forest_total_cost_all_leaves rest

// forest_root_freqs prepend Leaf — count distributes
let forest_root_freqs_prepend_leaf (idx: SZ.t) (p: hnode_ptr) (f: pos)
  (rest: list forest_entry) (x: pos)
  : Lemma (L.count x (forest_root_freqs ((idx, p, HSpec.Leaf 0 f) :: rest)) ==
           (if x = f then 1 else 0) + L.count x (forest_root_freqs rest))
  = ()

// cost == 0 implies tree is a Leaf (Internal nodes have cost >= freq_of l + freq_of r >= 2)
let cost_zero_is_leaf (t: HSpec.htree)
  : Lemma (requires HSpec.cost t == 0) (ensures HSpec.Leaf? t)
  = ()

// forest_total_cost == 0 implies all entries are leaves
let rec forest_total_cost_zero_all_leaves (entries: list forest_entry)
  : Lemma (requires forest_total_cost entries == 0)
          (ensures forall (k: nat). k < L.length entries ==> HSpec.Leaf? (entry_tree (L.index entries k)))
          (decreases entries)
  = match entries with
    | [] -> ()
    | e :: rest ->
        assert (HSpec.cost (entry_tree e) + forest_total_cost rest == 0);
        assert (HSpec.cost (entry_tree e) >= 0);
        assert (forest_total_cost rest >= 0);
        cost_zero_is_leaf (entry_tree e);
        forest_total_cost_zero_all_leaves rest

// For an all-leaf forest, root_freqs multiset == leaf_freqs multiset
let rec forest_root_freqs_eq_leaf_freqs_for_leaves
  (entries: list forest_entry) (x: pos)
  : Lemma (requires forall (k: nat). k < L.length entries ==>
                    HSpec.Leaf? (entry_tree (L.index entries k)))
          (ensures L.count x (forest_root_freqs entries) ==
                   L.count x (all_leaf_freqs entries))
          (decreases entries)
  = match entries with
    | [] -> ()
    | e :: rest ->
        assert (HSpec.Leaf? (entry_tree e));
        assert (forall (k: nat). k < L.length rest ==>
          L.index rest k == L.index entries (k + 1));
        forest_root_freqs_eq_leaf_freqs_for_leaves rest x;
        all_leaf_freqs_cons e rest x

// forest_total_cost after merge step:
// removing trees at j1, j2 (with costs c1, c2 and root freqs f1, f2)
// and prepending Internal(f1+f2, t1, t2) with cost = f1+f2+c1+c2
// gives forest_total_cost(new) = forest_total_cost(old) + f1 + f2
let rec forest_total_cost_remove_at (entries: list forest_entry) (j: nat)
  : Lemma (requires j < L.length entries)
          (ensures forest_total_cost entries ==
                   HSpec.cost (entry_tree (L.index entries j)) +
                   forest_total_cost (list_remove_at entries j))
          (decreases entries)
  = match entries with
    | e :: rest ->
        if j = 0 then ()
        else forest_total_cost_remove_at rest (j - 1)

#push-options "--z3rlimit 20"
let forest_total_cost_remove_two (entries: list forest_entry) (j1 j2: nat)
  : Lemma (requires j1 < L.length entries /\ j2 < L.length entries /\ j1 <> j2)
          (ensures forest_total_cost entries ==
                   HSpec.cost (entry_tree (L.index entries j1)) +
                   HSpec.cost (entry_tree (L.index entries j2)) +
                   forest_total_cost (list_remove_two entries j1 j2))
  = forest_total_cost_remove_at entries j1;
    let rem1 = list_remove_at entries j1 in
    list_remove_at_length entries j1;
    let j2' = if j2 < j1 then j2 else j2 - 1 in
    list_remove_at_index entries j1 j2';
    forest_total_cost_remove_at rem1 j2'
#pop-options

#push-options "--z3rlimit 20"
let forest_total_cost_merge_step
  (entries: list forest_entry) (j1 j2: nat) (f: pos) (idx: SZ.t) (p: hnode_ptr)
  (t1 t2: HSpec.htree)
  : Lemma (requires j1 < L.length entries /\ j2 < L.length entries /\ j1 <> j2 /\
                    entry_tree (L.index entries j1) == t1 /\
                    entry_tree (L.index entries j2) == t2 /\
                    f == HSpec.freq_of t1 + HSpec.freq_of t2)
          (ensures (let merged = HSpec.Internal f t1 t2 in
                    let new_active = (idx, p, merged) :: list_remove_two entries j1 j2 in
                    forest_total_cost new_active ==
                    forest_total_cost entries + HSpec.freq_of t1 + HSpec.freq_of t2))
  = forest_total_cost_remove_two entries j1 j2
#pop-options

// Total cost after merge is independent of j1/j2 order
let forest_total_cost_merge_step_any
  (entries: list forest_entry) (j1 j2: nat) (f: pos) (idx: SZ.t) (p: hnode_ptr)
  (t1 t2: HSpec.htree)
  : Lemma (requires j1 < L.length entries /\ j2 < L.length entries /\ j1 <> j2 /\
                    entry_tree (L.index entries j1) == t1 /\
                    entry_tree (L.index entries j2) == t2 /\
                    f == HSpec.freq_of t1 + HSpec.freq_of t2)
          (ensures forest_total_cost ((idx, p, HSpec.Internal f t1 t2) :: list_remove_two entries j1 j2) ==
                   forest_total_cost entries + HSpec.freq_of t1 + HSpec.freq_of t2)
  = forest_total_cost_merge_step entries j1 j2 f idx p t1 t2

// forest_root_freqs after removing at position j
let rec forest_root_freqs_remove_at (entries: list forest_entry) (j: nat) (x: pos)
  : Lemma (requires j < L.length entries)
          (ensures L.count x (forest_root_freqs entries) ==
                   (if x = HSpec.freq_of (entry_tree (L.index entries j)) then 1 else 0) +
                   L.count x (forest_root_freqs (list_remove_at entries j)))
          (decreases entries)
  = match entries with
    | e :: rest ->
        if j = 0 then ()
        else forest_root_freqs_remove_at rest (j - 1) x

let forest_root_freqs_remove_two (entries: list forest_entry) (j1 j2: nat) (x: pos)
  : Lemma (requires j1 < L.length entries /\ j2 < L.length entries /\ j1 <> j2)
          (ensures L.count x (forest_root_freqs entries) ==
                   (if x = HSpec.freq_of (entry_tree (L.index entries j1)) then 1 else 0) +
                   (if x = HSpec.freq_of (entry_tree (L.index entries j2)) then 1 else 0) +
                   L.count x (forest_root_freqs (list_remove_two entries j1 j2)))
  = forest_root_freqs_remove_at entries j1 x;
    let rem1 = list_remove_at entries j1 in
    list_remove_at_length entries j1;
    let j2' = if j2 < j1 then j2 else j2 - 1 in
    list_remove_at_index entries j1 j2';
    forest_root_freqs_remove_at rem1 j2' x

// forest_root_freqs after merge: prepend (f1+f2) to remaining
let forest_root_freqs_merge_step
  (entries: list forest_entry) (j1 j2: nat) (f: pos)
  (idx: SZ.t) (p: hnode_ptr) (t1 t2: HSpec.htree) (x: pos)
  : Lemma (requires j1 < L.length entries /\ j2 < L.length entries /\ j1 <> j2 /\
                    entry_tree (L.index entries j1) == t1 /\
                    entry_tree (L.index entries j2) == t2 /\
                    f == HSpec.freq_of t1 + HSpec.freq_of t2)
          (ensures (let merged = HSpec.Internal f t1 t2 in
                    let new_active = (idx, p, merged) :: list_remove_two entries j1 j2 in
                    L.count x (forest_root_freqs new_active) ==
                    (if x = f then 1 else 0) +
                    L.count x (forest_root_freqs (list_remove_two entries j1 j2))))
  = ()

// forest_root_freqs of single entry is a singleton list
let forest_root_freqs_singleton (entries: list forest_entry)
  : Lemma (requires L.length entries == 1)
          (ensures forest_root_freqs entries == [HSpec.freq_of (entry_tree (L.index entries 0))])
  = ()

// forest_total_cost of single entry
let forest_total_cost_singleton (entries: list forest_entry)
  : Lemma (requires L.length entries == 1)
          (ensures forest_total_cost entries == HSpec.cost (entry_tree (L.index entries 0)))
  = ()

// greedy_cost of a singleton is 0
let greedy_cost_singleton (f: pos)
  : Lemma (HOpt.greedy_cost [f] == 0)
  = HOpt.greedy_cost_singleton f

// forest_root_freqs length matches forest length
let rec forest_root_freqs_length (entries: list forest_entry)
  : Lemma (ensures L.length (forest_root_freqs entries) == L.length entries)
          (decreases entries)
  = match entries with
    | [] -> ()
    | _ :: rest -> forest_root_freqs_length rest

// Cost invariant maintenance through one merge step.
// This is a PURE arithmetic lemma — no PQ quantifiers, no forest traversal quantifiers.
// Separated to keep Z3 quantifier context clean.
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
let cost_invariant_merge_step
  (active0: list forest_entry) (j1 j2: nat)
  (freq1 freq2 sum_freq: pos) (idx1: SZ.t) (merged: hnode_ptr)
  (t1 t2: HSpec.htree) (initial_freqs: list pos)
  : Lemma (requires
      j1 < L.length active0 /\ j2 < L.length active0 /\ j1 <> j2 /\
      entry_tree (L.index active0 j1) == t1 /\
      entry_tree (L.index active0 j2) == t2 /\
      freq1 == HSpec.freq_of t1 /\ freq2 == HSpec.freq_of t2 /\
      sum_freq == freq1 + freq2 /\
      // Old cost invariant
      forest_total_cost active0 + HOpt.greedy_cost (forest_root_freqs active0) ==
        HOpt.greedy_cost initial_freqs /\
      // PQ min property: freq1 <= all root freqs
      (forall (x: pos). L.mem x (forest_root_freqs active0) ==> freq1 <= x) /\
      // Multiset decomposition of root_freqs
      (forall (x: pos). L.count x (forest_root_freqs active0) ==
        (if x = freq1 then 1 else 0) +
        (if x = freq2 then 1 else 0) +
        L.count x (forest_root_freqs (list_remove_two active0 j1 j2))) /\
      // freq2 <= remaining root freqs
      (forall (x: pos). L.mem x (forest_root_freqs (list_remove_two active0 j1 j2)) ==> freq2 <= x) /\
      L.length (forest_root_freqs active0) >= 2)
    (ensures (
      let new_tree = HSpec.Internal sum_freq t1 t2 in
      let new_active = (idx1, merged, new_tree) :: list_remove_two active0 j1 j2 in
      forest_total_cost new_active + HOpt.greedy_cost (forest_root_freqs new_active) ==
        HOpt.greedy_cost initial_freqs))
  = let rem = list_remove_two active0 j1 j2 in
    let new_tree = HSpec.Internal sum_freq t1 t2 in
    let new_active = (idx1, merged, new_tree) :: rem in
    // Step 1: forest_total_cost(new) = forest_total_cost(old) + freq1 + freq2
    forest_total_cost_merge_step active0 j1 j2 sum_freq idx1 merged t1 t2;
    // Step 2: greedy_cost(root_freqs(old)) = (freq1+freq2) + greedy_cost((freq1+freq2) :: root_freqs(rem))
    forest_root_freqs_length active0;
    HOpt.greedy_cost_unfold_with_mins
      (forest_root_freqs active0) freq1 freq2
      (forest_root_freqs rem);
    // Step 3: forest_root_freqs(new_active) = sum_freq :: forest_root_freqs(rem)
    assert (forest_root_freqs new_active == sum_freq :: forest_root_freqs rem);
    ()
#pop-options

// Helper: if freq <= all root freqs of active, then freq <= all root freqs of any sublist
let rec forest_root_freqs_remove_at_le (entries: list forest_entry) (j: nat) (fmin: int)
  : Lemma (requires j < L.length entries /\
                    (forall (x: pos). L.mem x (forest_root_freqs entries) ==> fmin <= x))
          (ensures (forall (x: pos). L.mem x (forest_root_freqs (list_remove_at entries j)) ==> fmin <= x))
          (decreases entries)
  = match entries with
    | _ :: rest -> if j = 0 then () else forest_root_freqs_remove_at_le rest (j - 1) fmin

let forest_root_freqs_remove_two_le (entries: list forest_entry) (j1 j2: nat) (fmin: int)
  : Lemma (requires j1 < L.length entries /\ j2 < L.length entries /\ j1 <> j2 /\
                    (forall (x: pos). L.mem x (forest_root_freqs entries) ==> fmin <= x))
          (ensures (forall (x: pos). L.mem x (forest_root_freqs (list_remove_two entries j1 j2)) ==> fmin <= x))
  = list_remove_at_length entries j1;
    forest_root_freqs_remove_at_le entries j1 fmin;
    let j2' = if j2 < j1 then j2 else j2 - 1 in
    forest_root_freqs_remove_at_le (list_remove_at entries j1) j2' fmin

// Universally quantified versions of the above (checked in clean SMT context)
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let forest_root_freqs_remove_two_forall (entries: list forest_entry) (j1 j2: nat)
  : Lemma (requires j1 < L.length entries /\ j2 < L.length entries /\ j1 <> j2)
          (ensures forall (x: pos). L.count x (forest_root_freqs entries) ==
                    (if x = HSpec.freq_of (entry_tree (L.index entries j1)) then 1 else 0) +
                    (if x = HSpec.freq_of (entry_tree (L.index entries j2)) then 1 else 0) +
                    L.count x (forest_root_freqs (list_remove_two entries j1 j2)))
  = introduce forall (x: pos).
      L.count x (forest_root_freqs entries) ==
      (if x = HSpec.freq_of (entry_tree (L.index entries j1)) then 1 else 0) +
      (if x = HSpec.freq_of (entry_tree (L.index entries j2)) then 1 else 0) +
      L.count x (forest_root_freqs (list_remove_two entries j1 j2))
    with forest_root_freqs_remove_two entries j1 j2 x
#pop-options

// ========== Section 5: forest_all_leaves helpers ==========

let all_leaves_prepend (active: list forest_entry) (idx: SZ.t) (p: hnode_ptr) (f: pos)
  : Lemma (requires forest_all_leaves active)
          (ensures forest_all_leaves ((idx, p, HSpec.Leaf 0 f) :: active))
  = reveal_opaque (`%forest_all_leaves) forest_all_leaves

// Eliminate all_leaves: every entry is a Leaf
let all_leaves_elim (active: list forest_entry)
  : Lemma (requires forest_all_leaves active)
          (ensures forall (k: nat). k < L.length active ==> HSpec.Leaf? (entry_tree (L.index active k)))
  = reveal_opaque (`%forest_all_leaves) forest_all_leaves

// ========== Section 6: cost_zero helper ==========

// Helper: derive root_freqs == leaf_freqs from forest_total_cost == 0
// Avoids subtyping issues from Classical.forall_intro in quantifier-rich contexts
let cost_zero_root_eq_leaf_freqs (entries: list forest_entry) (x: pos)
  : Lemma (requires forest_total_cost entries == 0)
          (ensures L.count x (forest_root_freqs entries) == L.count x (all_leaf_freqs entries))
  = forest_total_cost_zero_all_leaves entries;
    forest_root_freqs_eq_leaf_freqs_for_leaves entries x

// ========== Section 7: remaining_no_idx ==========

// no remaining forest entry has idx1 (from forest_distinct_indices + removal of j1)
#push-options "--z3rlimit 60"
let remaining_no_idx (active: list forest_entry) (j1 j2: nat) (idx1: SZ.t)
  : Lemma (requires j1 < L.length active /\ j2 < L.length active /\ j1 <> j2 /\
                    forest_distinct_indices active /\
                    entry_idx (L.index active j1) == idx1)
          (ensures (let rem = list_remove_two active j1 j2 in
                    forall (k: nat). k < L.length rem ==> entry_idx (L.index rem k) <> idx1))
  = list_remove_at_length active j1;
    let rem1 = list_remove_at active j1 in
    let j2' : nat = if j2 < j1 then j2 else j2 - 1 in
    list_remove_at_length rem1 j2';
    let rem = list_remove_at rem1 j2' in
    introduce forall (k: nat). k < L.length rem ==> entry_idx (L.index rem k) <> idx1
    with introduce _ ==> _
    with _. (
      // Step 1: trace k in rem to k1 in rem1
      list_remove_at_index rem1 j2' k;
      let k1 : nat = if k < j2' then k else k + 1 in
      // Step 2: trace k1 in rem1 to k' in active
      list_remove_at_index active j1 k1;
      let k' : nat = if k1 < j1 then k1 else k1 + 1 in
      // Step 3: k' <> j1 and both are valid => distinct indices
      forest_distinct_indices_elim active k' j1
    )
#pop-options
#pop-options
