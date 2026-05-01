module CLRS.Ch16.Huffman.PQLemmas
open FStar.SizeT
open CLRS.Ch16.Huffman.Defs
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot.Base
module PQ = Pulse.Lib.PriorityQueue

val valid_pq_entries_extends (s0 s1: Seq.seq pq_entry) (x: pq_entry) (n: nat)
  : Lemma (requires PQ.extends s0 s1 x /\ valid_pq_entries s0 n /\ SZ.v (snd x) < n)
          (ensures valid_pq_entries s1 n)

val valid_pq_entries_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry) (n: nat)
  : Lemma (requires PQ.extends s1 s0 x /\ valid_pq_entries s0 n)
          (ensures valid_pq_entries s1 n /\ SZ.v (snd x) < n)

val pq_freqs_positive_extends (s0 s1: Seq.seq pq_entry) (x: pq_entry)
  : Lemma (requires PQ.extends s0 s1 x /\ pq_freqs_positive s0 /\ fst x > 0)
          (ensures pq_freqs_positive s1)

val pq_freqs_positive_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry)
  : Lemma (requires PQ.extends s1 s0 x /\ pq_freqs_positive s0)
          (ensures pq_freqs_positive s1 /\ fst x > 0)

val pq_idx_unique_extends (s0 s1: Seq.seq pq_entry) (x: pq_entry)
  : Lemma (requires PQ.extends s0 s1 x /\ pq_idx_unique s0 /\
                    (forall (j: nat). j < Seq.length s0 ==> snd (Seq.index s0 j) <> snd x))
          (ensures pq_idx_unique s1)

val pq_idx_unique_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry)
  : Lemma (requires PQ.extends s1 s0 x /\ pq_idx_unique s0)
          (ensures pq_idx_unique s1 /\
                   (forall (j: nat). j < Seq.length s1 ==> snd (Seq.index s1 j) <> snd x))

val pq_no_idx_preserved (s0 s1: Seq.seq pq_entry) (x: pq_entry) (some_idx: SZ.t)
  : Lemma (requires PQ.extends s1 s0 x /\ snd x <> some_idx /\
                    (forall (j: nat). j < Seq.length s0 ==> snd (Seq.index s0 j) <> some_idx))
          (ensures forall (j: nat). j < Seq.length s1 ==> snd (Seq.index s1 j) <> some_idx)

val pq_idx_lt_bound (pq: Seq.seq pq_entry) (forest: list forest_entry) (bound: SZ.t)
  : Lemma (requires pq_indices_in_forest pq forest /\
                    (forall (k: nat). k < L.length forest ==> SZ.v (entry_idx (L.index forest k)) < SZ.v bound))
          (ensures forall (j: nat). j < Seq.length pq ==> snd (Seq.index pq j) <> bound)

val find_entry_by_idx_unique (entries: list forest_entry) (k: nat) (idx: SZ.t)
  : Lemma (requires forest_distinct_indices entries /\ k < L.length entries /\
                    entry_idx (L.index entries k) == idx)
          (ensures find_entry_by_idx entries idx == Some k)

val two_extracts_forest_positions
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
