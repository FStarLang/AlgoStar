module CLRS.Ch16.Huffman.PQLemmas
open FStar.SizeT
open CLRS.Ch16.Huffman.Defs
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot.Base
module PQ = Pulse.Lib.PriorityQueue
module Classical = FStar.Classical

#push-options "--z3rlimit 8"

let valid_pq_entries_extends (s0 s1: Seq.seq pq_entry) (x: pq_entry) (n: nat)
  : Lemma (requires PQ.extends s0 s1 x /\ valid_pq_entries s0 n /\ SZ.v (snd x) < n)
          (ensures valid_pq_entries s1 n)
  = let aux (j: nat{j < Seq.length s1}) : Lemma (SZ.v (snd (Seq.index s1 j)) < n) =
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

// For extract_min: extends s1 s0 x means s0 = s1 + x, so valid s0 ==> valid s1
let valid_pq_entries_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry) (n: nat)
  : Lemma (requires PQ.extends s1 s0 x /\ valid_pq_entries s0 n)
          (ensures valid_pq_entries s1 n /\ SZ.v (snd x) < n)
  = assert (FStar.Seq.Properties.count x s0 > 0);
    FStar.Seq.Properties.mem_index x s0;
    let aux (j: nat{j < Seq.length s1}) : Lemma (SZ.v (snd (Seq.index s1 j)) < n) =
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

let pq_freqs_positive_extends (s0 s1: Seq.seq pq_entry) (x: pq_entry)
  : Lemma (requires PQ.extends s0 s1 x /\ pq_freqs_positive s0 /\ fst x > 0)
          (ensures pq_freqs_positive s1)
  = let aux (j: nat{j < Seq.length s1}) : Lemma (fst (Seq.index s1 j) > 0) =
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

let pq_freqs_positive_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry)
  : Lemma (requires PQ.extends s1 s0 x /\ pq_freqs_positive s0)
          (ensures pq_freqs_positive s1 /\ fst x > 0)
  = assert (FStar.Seq.Properties.count x s0 > 0);
    FStar.Seq.Properties.mem_index x s0;
    let aux (j: nat{j < Seq.length s1}) : Lemma (fst (Seq.index s1 j) > 0) =
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

// After insert: pq_idx_unique extends (new entry's index is fresh)
#push-options "--z3rlimit 30"
let pq_idx_unique_extends (s0 s1: Seq.seq pq_entry) (x: pq_entry)
  : Lemma (requires PQ.extends s0 s1 x /\ pq_idx_unique s0 /\
                    (forall (j: nat). j < Seq.length s0 ==> snd (Seq.index s0 j) <> snd x))
          (ensures pq_idx_unique s1)
  = reveal_opaque (`%pq_idx_unique) pq_idx_unique;
    let aux (i j: nat)
      : Lemma (requires i < Seq.length s1 /\ j < Seq.length s1 /\ i <> j)
              (ensures snd (Seq.index s1 i) <> snd (Seq.index s1 j)) =
      let yi = Seq.index s1 i in
      let yj = Seq.index s1 j in
      if yi = x && yj = x then begin
        let aux2 (k: nat{k < Seq.length s0}) : Lemma (Seq.index s0 k <> x) =
          assert (snd (Seq.index s0 k) <> snd x)
        in
        Classical.forall_intro aux2;
        count_zero x s0;
        assert (PQ.count x s1 == 1);
        count_one_unique x s1 i j
      end
      else if yi = x then begin
        FStar.Seq.Properties.seq_mem_k s1 j;
        assert (yj =!= x);
        assert (PQ.count yj s1 == PQ.count yj s0);
        assert (Seq.mem yj s0);
        FStar.Seq.Properties.mem_index yj s0
      end
      else if yj = x then begin
        FStar.Seq.Properties.seq_mem_k s1 i;
        assert (yi =!= x);
        assert (PQ.count yi s1 == PQ.count yi s0);
        assert (Seq.mem yi s0);
        FStar.Seq.Properties.mem_index yi s0
      end
      else begin
        // Neither is x: yi <> x and yj <> x
        assert (yi =!= x);
        assert (yj =!= x);
        FStar.Seq.Properties.seq_mem_k s1 i;
        FStar.Seq.Properties.seq_mem_k s1 j;
        assert (PQ.count yi s1 == PQ.count yi s0);
        assert (PQ.count yj s1 == PQ.count yj s0);
        FStar.Seq.Properties.mem_index yi s0;
        FStar.Seq.Properties.mem_index yj s0;
        pq_idx_unique_count_le_1 s0 yi;
        if yi = yj then
          count_one_unique yi s1 i j;
        let ii = FStar.Seq.Properties.index_mem yi s0 in
        let jj = FStar.Seq.Properties.index_mem yj s0 in
        assert (ii <> jj)
      end
    in
    let aux' (i j: nat) : Lemma
      (i < Seq.length s1 /\ j < Seq.length s1 /\ i <> j ==>
       snd (Seq.index s1 i) <> snd (Seq.index s1 j))
    = if i < Seq.length s1 && j < Seq.length s1 && i <> j then aux i j
    in
    Classical.forall_intro_2 aux'
#pop-options

// After extract_min: pq_idx_unique shrinks
#push-options "--z3rlimit 30"
let pq_idx_unique_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry)
  : Lemma (requires PQ.extends s1 s0 x /\ pq_idx_unique s0)
          (ensures pq_idx_unique s1 /\
                   (forall (j: nat). j < Seq.length s1 ==> snd (Seq.index s1 j) <> snd x))
  = reveal_opaque (`%pq_idx_unique) pq_idx_unique;
    let aux (i j: nat)
      : Lemma (requires i < Seq.length s1 /\ j < Seq.length s1 /\ i <> j)
              (ensures snd (Seq.index s1 i) <> snd (Seq.index s1 j)) =
      let yi = Seq.index s1 i in
      let yj = Seq.index s1 j in
      FStar.Seq.Properties.seq_mem_k s1 i;
      FStar.Seq.Properties.seq_mem_k s1 j;
      // yi is in s0
      if yi = x then begin
        assert (PQ.count yi s0 == PQ.count yi s1 + 1);
        assert (Seq.mem yi s0)
      end else begin
        assert (yi =!= x);
        assert (PQ.count yi s0 == PQ.count yi s1);
        assert (Seq.mem yi s0)
      end;
      FStar.Seq.Properties.mem_index yi s0;
      pq_idx_unique_count_le_1 s0 yi;
      if yi = yj then
        count_one_unique yi s1 i j;
      // yj is in s0
      if yj = x then begin
        assert (PQ.count yj s0 == PQ.count yj s1 + 1);
        assert (Seq.mem yj s0)
      end else begin
        assert (yj =!= x);
        assert (PQ.count yj s0 == PQ.count yj s1);
        assert (Seq.mem yj s0)
      end;
      FStar.Seq.Properties.mem_index yj s0;
      let ii = FStar.Seq.Properties.index_mem yi s0 in
      let jj = FStar.Seq.Properties.index_mem yj s0 in
      assert (ii <> jj)
    in
    let aux' (i j: nat) : Lemma
      (i < Seq.length s1 /\ j < Seq.length s1 /\ i <> j ==>
       snd (Seq.index s1 i) <> snd (Seq.index s1 j))
    = if i < Seq.length s1 && j < Seq.length s1 && i <> j then aux i j
    in
    Classical.forall_intro_2 aux';
    // Also: no entry in s1 has index = snd x
    let aux2 (j: nat{j < Seq.length s1})
      : Lemma (snd (Seq.index s1 j) <> snd x) =
      let y = Seq.index s1 j in
      FStar.Seq.Properties.seq_mem_k s1 j;
      if snd y = snd x then begin
        // y is in s0
        if y = x then begin
          assert (PQ.count y s0 == PQ.count y s1 + 1);
          assert (Seq.mem y s0)
        end else begin
          assert (y =!= x);
          assert (PQ.count y s0 == PQ.count y s1);
          assert (Seq.mem y s0)
        end;
        FStar.Seq.Properties.mem_index y s0;
        let k = FStar.Seq.Properties.index_mem y s0 in
        assert (PQ.count x s0 > 0);
        FStar.Seq.Properties.mem_index x s0;
        let kx = FStar.Seq.Properties.index_mem x s0 in
        if k = kx then begin
          assert (y = x);
          pq_idx_unique_count_le_1 s0 x;
          assert (PQ.count x s0 == 1);
          assert (PQ.count x s1 == 0)
        end
        else begin
          assert (snd (Seq.index s0 k) = snd x);
          assert (snd (Seq.index s0 kx) = snd x);
          assert (k <> kx)
        end
      end
    in
    Classical.forall_intro aux2
#pop-options

// After shrinking (removing x), if all entries in s0 had snd <> some_idx, entries in s1 also have snd <> some_idx
let pq_no_idx_preserved (s0 s1: Seq.seq pq_entry) (x: pq_entry) (some_idx: SZ.t)
  : Lemma (requires PQ.extends s1 s0 x /\ snd x <> some_idx /\
                    (forall (j: nat). j < Seq.length s0 ==> snd (Seq.index s0 j) <> some_idx))
          (ensures (forall (j: nat). j < Seq.length s1 ==> snd (Seq.index s1 j) <> some_idx))
  = let aux (j: nat{j < Seq.length s1})
      : Lemma (snd (Seq.index s1 j) <> some_idx) =
      let y = Seq.index s1 j in
      FStar.Seq.Properties.seq_mem_k s1 j;
      if y = x then begin
        assert (PQ.count x s0 > 0);
        FStar.Seq.Properties.mem_index x s0
      end else begin
        assert (y =!= x);
        assert (PQ.count y s0 == PQ.count y s1);
        assert (Seq.mem y s0);
        FStar.Seq.Properties.mem_index y s0
      end
    in
    Classical.forall_intro aux

// If all forest entries have idx < bound, and pq_indices_in_forest, then all PQ snd < bound
let pq_idx_lt_bound (pq: Seq.seq pq_entry) (forest: list forest_entry) (bound: SZ.t)
  : Lemma (requires pq_indices_in_forest pq forest /\
                    (forall (k: nat). k < L.length forest ==> SZ.v (entry_idx (L.index forest k)) < SZ.v bound))
          (ensures forall (j: nat). j < Seq.length pq ==> snd (Seq.index pq j) <> bound)
  = let aux (j: nat{j < Seq.length pq})
      : Lemma (snd (Seq.index pq j) <> bound) =
      let idx = snd (Seq.index pq j) in
      find_entry_by_idx_spec forest idx;
      let k = Some?.v (find_entry_by_idx forest idx) in
      assert (entry_idx (L.index forest k) == idx);
      assert (SZ.v idx < SZ.v bound)
    in
    Classical.forall_intro aux

// pq_indices_in_forest subset: shrink then reduce forest
let pq_indices_in_forest_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry) (forest: list forest_entry)
  : Lemma (requires PQ.extends s1 s0 x /\ pq_indices_in_forest s0 forest)
          (ensures pq_indices_in_forest s1 forest)
  = let aux (j: nat{j < Seq.length s1})
      : Lemma (Some? (find_entry_by_idx forest (snd (Seq.index s1 j))))
      = let y = Seq.index s1 j in
        FStar.Seq.Properties.lemma_count_slice s1 j;
        FStar.Seq.Properties.mem_index y s0;
        assert (Seq.mem y s0)
    in Classical.forall_intro aux

// find_entry_by_idx with distinct indices: result is THE unique position
let find_entry_by_idx_unique (entries: list forest_entry) (k: nat) (idx: SZ.t)
  : Lemma (requires forest_distinct_indices entries /\ k < L.length entries /\
                    entry_idx (L.index entries k) == idx)
          (ensures find_entry_by_idx entries idx == Some k)
  = find_entry_by_idx_spec entries idx;
    match find_entry_by_idx entries idx with
    | Some k' ->
        if k' = k then ()
        else forest_distinct_indices_elim entries k k'
    | None -> ()

// After extract_min: the extracted index differs from all remaining entries' indices
// Combines pq_idx_unique_shrink + Seq.mem witness to derive idx1 <> idx2
let pq_extracted_idx_distinct (s0 s1: Seq.seq pq_entry) (x y: pq_entry)
  : Lemma (requires PQ.extends s1 s0 x /\ pq_idx_unique s0 /\ Seq.mem y s1)
          (ensures snd x <> snd y)
  = pq_idx_unique_shrink s0 s1 x;
    FStar.Seq.Properties.mem_index y s1

// If x is a member of pq and pq_indices_in_forest holds, then find_entry_by_idx finds x's index
let pq_in_forest_mem (pq: Seq.seq pq_entry) (forest: list forest_entry) (x: pq_entry)
  : Lemma (requires pq_indices_in_forest pq forest /\ Seq.mem x pq)
          (ensures Some? (find_entry_by_idx forest (snd x)))
  = FStar.Seq.Properties.mem_index x pq

// Combined: after two extract_mins from pq0, both extracted indices are in the forest,
// are distinct, and map to distinct forest positions
let two_extracts_forest_positions
  (pq0 pq1: Seq.seq pq_entry)
  (x y: pq_entry)
  (forest: list forest_entry)
  : Lemma (requires
      pq_idx_unique pq0 /\
      pq_indices_in_forest pq0 forest /\
      PQ.extends pq1 pq0 x /\
      Seq.mem y pq1 /\
      forest_distinct_indices forest)
    (ensures
      Some? (find_entry_by_idx forest (snd x)) /\
      Some? (find_entry_by_idx forest (snd y)) /\
      snd x <> snd y /\
      Some?.v (find_entry_by_idx forest (snd x)) <> Some?.v (find_entry_by_idx forest (snd y)))
  = // x is in pq0 (count x pq0 = count x pq1 + 1 >= 1)
    pq_in_forest_mem pq0 forest x;
    // y is in pq1 ⊂ pq0
    pq_indices_in_forest_shrink pq0 pq1 x forest;
    pq_in_forest_mem pq1 forest y;
    // idx x <> idx y
    pq_extracted_idx_distinct pq0 pq1 x y;
    // positions differ
    find_entry_positions_distinct forest (snd x) (snd y)

#pop-options
