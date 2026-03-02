module CLRS.Ch16.Huffman
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.Vec
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Box = Pulse.Lib.Box
module PQ = Pulse.Lib.PriorityQueue
module HSpec = CLRS.Ch16.Huffman.Spec
module HOpt = CLRS.Ch16.Huffman.Optimality

open Pulse.Lib.TotalOrder
open FStar.Order

module L = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties

// Import all definitions and lemmas from split modules
open CLRS.Ch16.Huffman.Defs
open CLRS.Ch16.Huffman.PQLemmas
open CLRS.Ch16.Huffman.ForestLemmas
open CLRS.Ch16.Huffman.PQForest

// ========== Allocate an hnode on the heap ==========

fn alloc_hnode (h: hnode)
  requires emp
  returns p: hnode_ptr
  ensures Box.pts_to p h
{
  Box.alloc h
}

// Recursive separation logic predicate: relates a heap-allocated tree to a spec tree.
let rec is_htree ([@@@mkey] p: hnode_ptr) (ft: HSpec.htree) : Tot slprop (decreases ft) =
  match ft with
  | HSpec.Leaf f ->
    p |-> ({ freq = f; left = None #(Box.box hnode); right = None #(Box.box hnode) } <: hnode)
  | HSpec.Internal f l r ->
    exists* (lp: hnode_ptr) (rp: hnode_ptr).
      (p |-> ({ freq = f; left = Some lp; right = Some rp } <: hnode)) **
      is_htree lp l **
      is_htree rp r

// ========== Forest ownership: list-based separating conjunction of is_htree ==========

let rec forest_own (entries: list forest_entry) : Tot slprop (decreases entries) =
  match entries with
  | [] -> emp
  | hd :: rest -> is_htree (entry_ptr hd) (entry_tree hd) ** forest_own rest

// ========== Forest ownership manipulation ==========

ghost
fn forest_own_put_head
  (entries: list forest_entry)
  (idx: SZ.t) (p: hnode_ptr) (ft: HSpec.htree)
  requires is_htree p ft ** forest_own entries
  ensures forest_own ((idx, p, ft) :: entries)
{
  fold (forest_own ((idx, p, ft) :: entries));
}

// Take the head element from forest_own
ghost
fn forest_own_take_head
  (hd: forest_entry) (tl: list forest_entry)
  requires forest_own (hd :: tl)
  ensures is_htree (entry_ptr hd) (entry_tree hd) ** forest_own tl
{
  unfold (forest_own (hd :: tl));
}

open Pulse.Lib.Core

// Prove: forest_own entries == is_htree(entries[j]) ** forest_own(remove entries j)
// Uses star commutativity + associativity from PulseCore
let rec forest_own_split_lemma
  (entries: list forest_entry)
  (j: nat{j < L.length entries})
  : Lemma (ensures forest_own entries ==
             is_htree (entry_ptr (L.index entries j)) (entry_tree (L.index entries j)) **
             forest_own (list_remove_at entries j))
          (decreases j)
  = match entries with
    | hd :: tl ->
      if j = 0 then ()
      else begin
        forest_own_split_lemma tl (j - 1);
        let p0 = is_htree (entry_ptr hd) (entry_tree hd) in
        let pj = is_htree (entry_ptr (L.index tl (j-1))) (entry_tree (L.index tl (j-1))) in
        let rest = forest_own (list_remove_at tl (j-1)) in
        let step1 : slprop_equiv (p0 ** (pj ** rest)) ((p0 ** pj) ** rest) =
          slprop_equiv_sym _ _ (slprop_equiv_assoc p0 pj rest) in
        let step2 : slprop_equiv ((p0 ** pj) ** rest) ((pj ** p0) ** rest) =
          slprop_equiv_cong (p0 ** pj) rest (pj ** p0) rest
            (slprop_equiv_comm p0 pj)
            (slprop_equiv_refl rest) in
        let step3 : slprop_equiv ((pj ** p0) ** rest) (pj ** (p0 ** rest)) =
          slprop_equiv_assoc pj p0 rest in
        elim_slprop_equiv (slprop_equiv_trans _ _ _
          step1
          (slprop_equiv_trans _ _ _ step2 step3))
      end

// Extract element at list position j from forest_own
ghost
fn forest_own_take_at
  (entries: list forest_entry)
  (j: nat{j < L.length entries})
  requires forest_own entries
  ensures is_htree (entry_ptr (L.index entries j)) (entry_tree (L.index entries j)) **
          forest_own (list_remove_at entries j)
{
  forest_own_split_lemma entries j;
  rewrite (forest_own entries)
       as (is_htree (entry_ptr (L.index entries j)) (entry_tree (L.index entries j)) **
           forest_own (list_remove_at entries j));
}

// Prove: forest_own entries == 
//   is_htree(entries[j1]) ** is_htree(entries[j2]) ** forest_own(remove_two entries j1 j2)
let forest_own_split_two_lemma
  (entries: list forest_entry)
  (j1 j2: nat)
  : Lemma (requires j1 < L.length entries /\ j2 < L.length entries /\ j1 <> j2)
          (ensures forest_own entries ==
            is_htree (entry_ptr (L.index entries j1)) (entry_tree (L.index entries j1)) **
            (is_htree (entry_ptr (L.index entries j2)) (entry_tree (L.index entries j2)) **
             forest_own (list_remove_two entries j1 j2)))
  = // First split at j1
    forest_own_split_lemma entries j1;
    // forest_own entries == is_htree(entries[j1]) ** forest_own(rem1)
    let rem1 = list_remove_at entries j1 in
    list_remove_at_length entries j1;
    let j2' = if j2 < j1 then j2 else j2 - 1 in
    list_remove_at_index entries j1 j2';
    // L.index rem1 j2' == L.index entries j2
    // Split rem1 at j2'
    forest_own_split_lemma rem1 j2'
    // forest_own rem1 == is_htree(rem1[j2']) ** forest_own(list_remove_at rem1 j2')
    // rem1[j2'] == entries[j2], and list_remove_at rem1 j2' == list_remove_two entries j1 j2
    // So: forest_own entries ==
    //   is_htree(entries[j1]) ** (is_htree(entries[j2]) ** forest_own(list_remove_two entries j1 j2))

// Extract two elements at list positions j1, j2 from forest_own
ghost
fn forest_own_take_two
  (entries: list forest_entry)
  (j1: nat{j1 < L.length entries})
  (j2: nat{j2 < L.length entries /\ j1 <> j2})
  requires forest_own entries
  ensures is_htree (entry_ptr (L.index entries j1)) (entry_tree (L.index entries j1)) **
          is_htree (entry_ptr (L.index entries j2)) (entry_tree (L.index entries j2)) **
          forest_own (list_remove_two entries j1 j2)
{
  forest_own_split_two_lemma entries j1 j2;
  rewrite (forest_own entries)
       as (is_htree (entry_ptr (L.index entries j1)) (entry_tree (L.index entries j1)) **
           (is_htree (entry_ptr (L.index entries j2)) (entry_tree (L.index entries j2)) **
            forest_own (list_remove_two entries j1 j2)));
}

// ========== Free pointer-based Huffman tree ==========

fn rec free_htree (p: hnode_ptr) (ft: HSpec.htree)
  requires is_htree p ft
  ensures emp
  decreases ft
{
  match ft {
    HSpec.Leaf f -> {
      unfold (is_htree p (HSpec.Leaf f));
      Box.free p;
    }
    HSpec.Internal f l r -> {
      unfold (is_htree p (HSpec.Internal f l r));
      with lp rp. _;
      let node = Box.op_Bang p;
      Box.free p;
      let lp_rt = Some?.v node.left;
      let rp_rt = Some?.v node.right;
      rewrite (is_htree lp l) as (is_htree lp_rt l);
      rewrite (is_htree rp r) as (is_htree rp_rt r);
      free_htree lp_rt l;
      free_htree rp_rt r;
    }
  }
}

// ========== Main Huffman Tree Algorithm ==========

// Local wrapper: calls merge_bundle_step with all preconditions pre-computed.
// This isolates the heavy SMT work from the Pulse VC.
#push-options "--z3rlimit 800 --fuel 1 --ifuel 1"
let merge_step_local
  (freq_seq: Seq.seq int) (nd_contents0: Seq.seq hnode_ptr) (merged: hnode_ptr)
  (pq0 pq1 pq2 pq3: Seq.seq pq_entry)
  (active0: list forest_entry) (n: nat)
  (freq1 freq2: pos) (idx1 idx2: SZ.t) (sum_freq: pos)
  (j1: nat) (j2: nat)
  : Lemma
    (requires
      merge_bundle freq_seq nd_contents0 pq0 active0 n /\
      L.length active0 >= 2 /\ Seq.length pq0 >= 2 /\
      PQ.is_minimum (freq1, idx1) pq0 /\
      PQ.extends pq1 pq0 (freq1, idx1) /\
      Seq.length pq1 == Seq.length pq0 - 1 /\
      PQ.is_minimum (freq2, idx2) pq1 /\
      PQ.extends pq2 pq1 (freq2, idx2) /\
      Seq.length pq2 == Seq.length pq1 - 1 /\
      PQ.extends pq2 pq3 (sum_freq, idx1) /\
      Seq.length pq3 == Seq.length pq2 + 1 /\
      sum_freq == freq1 + freq2 /\
      Seq.length nd_contents0 == n /\
      SZ.v idx1 < n /\ SZ.v idx2 < n /\
      Some? (find_entry_by_idx active0 idx1) /\
      Some? (find_entry_by_idx active0 idx2) /\
      j1 == Some?.v (find_entry_by_idx active0 idx1) /\
      j2 == Some?.v (find_entry_by_idx active0 idx2) /\
      j1 < L.length active0 /\ j2 < L.length active0 /\
      entry_idx (L.index active0 j1) == idx1 /\
      entry_idx (L.index active0 j2) == idx2 /\
      j1 <> j2 /\
      forest_distinct_indices active0)
    (ensures (
      let t1 = entry_tree (L.index active0 j1) in
      let t2 = entry_tree (L.index active0 j2) in
      let nd_new = Seq.upd nd_contents0 (SZ.v idx1) merged in
      let new_tree = HSpec.Internal sum_freq t1 t2 in
      let new_active = (idx1, merged, new_tree) :: list_remove_two active0 j1 j2 in
      merge_bundle freq_seq nd_new pq3 new_active n))
  = merge_bundle_elim freq_seq nd_contents0 pq0 active0 n;
    pq_idx_unique_shrink pq0 pq1 (freq1, idx1);
    FStar.Seq.Properties.mem_index (freq2, idx2) pq1;
    merge_bundle_step freq_seq nd_contents0 (Seq.upd nd_contents0 (SZ.v idx1) merged)
      pq0 pq1 pq2 pq3 active0 n
      freq1 freq2 idx1 idx2 sum_freq merged j1 j2
#pop-options

//SNIPPET_START: huffman_tree_sig
#push-options "--z3rlimit 400"
fn huffman_tree
  (freqs: A.array int)
  (#freq_seq: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires A.pts_to freqs freq_seq ** pure (
    SZ.v n == Seq.length freq_seq /\
    SZ.v n > 0 /\
    SZ.fits (2 * SZ.v n + 2) /\
    (forall (i: nat). i < Seq.length freq_seq ==> Seq.index freq_seq i > 0)
  )
  returns result: hnode_ptr
  ensures A.pts_to freqs freq_seq **
          (exists* ft. is_htree result ft **
                  pure (HSpec.cost ft == HOpt.greedy_cost (seq_to_pos_list freq_seq 0) /\
                        HSpec.same_frequency_multiset ft (seq_to_pos_list freq_seq 0) /\
                        HSpec.is_wpl_optimal ft (seq_to_pos_list freq_seq 0)))
//SNIPPET_END: huffman_tree_sig
{
  // Allocate node pointer array and PQ
  let dummy = alloc_hnode ({ freq = 0; left = (None #hnode_ptr); right = (None #hnode_ptr) } <: hnode);
  let nodes = V.alloc dummy n;
  let pq = PQ.create #pq_entry n;
  
  // Initialize: allocate leaf nodes, insert (freq, index) into PQ
  fold (forest_own (Nil #forest_entry));
  with nd0. assert (V.pts_to nodes nd0);
  init_bundle_intro_empty freq_seq nd0 (SZ.v n);

  let mut i: SZ.t = 0sz;
  while (
    !i <^ n
  )
  invariant exists* vi nd_contents pq_contents
                    (active: list forest_entry).
    R.pts_to i vi **
    V.pts_to nodes nd_contents **
    PQ.is_pqueue pq pq_contents (SZ.v n) **
    A.pts_to freqs freq_seq **
    Box.pts_to dummy ({ freq = 0; left = None #hnode_ptr; right = None #hnode_ptr } <: hnode) **
    forest_own active **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length nd_contents == SZ.v n /\
      Seq.length pq_contents == SZ.v vi /\
      L.length active == SZ.v vi /\
      SZ.fits (2 * SZ.v n + 2) /\
      Seq.length freq_seq == SZ.v n /\
      (forall (i: nat). i < Seq.length freq_seq ==> Seq.index freq_seq i > 0) /\
      init_bundle freq_seq nd_contents pq_contents active (SZ.v vi) (SZ.v n)
    )
  decreases (SZ.v n - SZ.v !i)
  {
    let vi = !i;
    let freq_val = A.op_Array_Access freqs vi;
    
    // Grab old state before mutations
    with active_old. assert (forest_own active_old);
    with nd_old. assert (V.pts_to nodes nd_old);
    
    // Allocate leaf node on the heap
    let leaf = alloc_hnode ({ freq = freq_val; left = (None #hnode_ptr); right = (None #hnode_ptr) } <: hnode);
    V.op_Array_Assignment nodes vi leaf;
    
    // Insert (freq, index) into PQ
    with pq_old. assert (PQ.is_pqueue pq pq_old (SZ.v n));
    PQ.insert pq (freq_val, vi);
    with pq_new. assert (PQ.is_pqueue pq pq_new (SZ.v n));
    extends_length pq_old pq_new (freq_val, vi);
    
    // Fold is_htree for this leaf and add to forest_own
    fold (is_htree leaf (HSpec.Leaf freq_val));
    forest_own_put_head active_old vi leaf (HSpec.Leaf freq_val);
    
    // Single bundle step maintains ALL invariants
    init_bundle_step freq_seq nd_old (Seq.upd nd_old (SZ.v vi) leaf)
                     pq_old pq_new active_old vi n (freq_val <: pos) leaf;
    
    i := vi +^ 1sz;
  };
  
  // Between init and merge: single transition lemma (no forall exposure to Pulse VC)
  with pq_init. assert (PQ.is_pqueue pq pq_init (SZ.v n));
  with active_init. assert (forest_own active_init);
  with nd_init. assert (V.pts_to nodes nd_init);
  
  init_to_merge_bundle freq_seq nd_init pq_init active_init (SZ.v n);
  
  // Main merge loop: extract two minimums, merge, insert back (n-1 times)
  let mut iter: SZ.t = 0sz;
  let n_minus_1 = n -^ 1sz;
  
  while (
    !iter <^ n_minus_1
  )
  invariant exists* viter nd_contents pq_contents
                    (active: list forest_entry).
    R.pts_to iter viter **
    V.pts_to nodes nd_contents **
    PQ.is_pqueue pq pq_contents (SZ.v n) **
    A.pts_to freqs freq_seq **
    Box.pts_to dummy ({ freq = 0; left = None #hnode_ptr; right = None #hnode_ptr } <: hnode) **
    forest_own active **
    pure (
      SZ.v viter <= SZ.v n - 1 /\
      Seq.length pq_contents == SZ.v n - SZ.v viter /\
      L.length active == SZ.v n - SZ.v viter /\
      L.length active > 0 /\
      SZ.fits (2 * Seq.length pq_contents + 2) /\
      merge_bundle freq_seq nd_contents pq_contents active (SZ.v n)
    )
  decreases (SZ.v n_minus_1 - SZ.v !iter)
  {
    // Extract properties from merge_bundle
    with pq0. assert (PQ.is_pqueue pq pq0 (SZ.v n));
    with active0. assert (forest_own active0);
    with nd_contents0. assert (V.pts_to nodes nd_contents0);
    merge_bundle_elim freq_seq nd_contents0 pq0 active0 (SZ.v n);
    
    // Two extract_mins
    let (freq1, idx1) = PQ.extract_min pq;
    with pq1. assert (PQ.is_pqueue pq pq1 (SZ.v n));
    extends_length pq1 pq0 (freq1, idx1);
    
    let (freq2, idx2) = PQ.extract_min pq;
    with pq2. assert (PQ.is_pqueue pq pq2 (SZ.v n));
    extends_length pq2 pq1 (freq2, idx2);
    
    let sum_freq = freq1 + freq2;
    
    // Help Z3: establish bounds for Vec access and freq positivity
    valid_pq_entries_shrink pq0 pq1 (freq1, idx1) (SZ.v n);
    valid_pq_entries_shrink pq1 pq2 (freq2, idx2) (SZ.v n);
    pq_freqs_positive_shrink pq0 pq1 (freq1, idx1);
    pq_freqs_positive_shrink pq1 pq2 (freq2, idx2);
    
    // Read tree pointers from nodes array
    let left_ptr = V.op_Array_Access nodes idx1;
    let right_ptr = V.op_Array_Access nodes idx2;
    
    // Ghost: find positions and establish take_two preconditions
    // (combined lemma: proves Some? for both, idx1 <> idx2, and positions distinct)
    two_extracts_forest_positions pq0 pq1 (freq1, idx1) (freq2, idx2) active0;
    find_entry_by_idx_spec active0 idx1;
    find_entry_by_idx_spec active0 idx2;
    
    // Now elim forest_distinct_indices (precondition i <> j established above)
    forest_distinct_indices_elim active0
      (Some?.v (find_entry_by_idx active0 idx1))
      (Some?.v (find_entry_by_idx active0 idx2));
    
    forest_own_take_two active0
      (Some?.v (find_entry_by_idx active0 idx1))
      (Some?.v (find_entry_by_idx active0 idx2));
    
    // Rewrite is_htree to use runtime pointers
    rewrite (is_htree (entry_ptr (L.index active0 (Some?.v (find_entry_by_idx active0 idx1))))
                      (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx1)))))
         as (is_htree left_ptr
                      (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx1)))));
    rewrite (is_htree (entry_ptr (L.index active0 (Some?.v (find_entry_by_idx active0 idx2))))
                      (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx2)))))
         as (is_htree right_ptr
                      (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx2)))));
    
    // Create merged internal node
    let merged = alloc_hnode ({ freq = sum_freq; left = Some left_ptr; right = Some right_ptr } <: hnode);
    
    // Fold is_htree for the merged node
    fold (is_htree merged (HSpec.Internal (sum_freq <: pos)
      (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx1))))
      (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx2))))));
    
    // Store merged node in nodes[idx1] and insert into PQ
    V.op_Array_Assignment nodes idx1 merged;
    PQ.insert pq (sum_freq, idx1);
    with pq3. assert (PQ.is_pqueue pq pq3 (SZ.v n));
    extends_length pq2 pq3 (sum_freq, idx1);
    
    // Ghost: put merged entry into new forest
    list_remove_two_length active0
      (Some?.v (find_entry_by_idx active0 idx1))
      (Some?.v (find_entry_by_idx active0 idx2));
    forest_own_put_head
      (list_remove_two active0
        (Some?.v (find_entry_by_idx active0 idx1))
        (Some?.v (find_entry_by_idx active0 idx2)))
      idx1 merged
      (HSpec.Internal (sum_freq <: pos)
        (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx1))))
        (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx2)))));
    
    // merge_bundle_step via local wrapper (avoids Z3 overhead from split modules)
    merge_step_local freq_seq nd_contents0 merged
      pq0 pq1 pq2 pq3 active0 (SZ.v n)
      (freq1 <: pos) (freq2 <: pos) idx1 idx2 (sum_freq <: pos)
      (Some?.v (find_entry_by_idx active0 idx1))
      (Some?.v (find_entry_by_idx active0 idx2));
    
    let viter = !iter;
    iter := viter +^ 1sz;
  };
  
  // Extract final result from PQ
  with pq_final. assert (PQ.is_pqueue pq pq_final (SZ.v n));
  with active_final. assert (forest_own active_final);
  with nd_final_pre. assert (V.pts_to nodes nd_final_pre);
  
  // Elim merge_bundle to get properties for final extraction
  merge_bundle_elim freq_seq nd_final_pre pq_final active_final (SZ.v n);
  
  let (result_freq, result_idx) = PQ.extract_min pq;
  with pq_empty. assert (PQ.is_pqueue pq pq_empty (SZ.v n));
  valid_pq_entries_shrink pq_final pq_empty (result_freq, result_idx) (SZ.v n);
  extends_length pq_empty pq_final (result_freq, result_idx);
  
  // Read tree pointer — bind nd_contents BEFORE reading (same pattern as merge loop body)
  with nd_final. assert (V.pts_to nodes nd_final);
  
  // Ghost: link result_idx to forest via find_entry_by_idx_spec
  find_entry_by_idx_spec active_final result_idx;
  
  let result = V.op_Array_Access nodes result_idx;
  
  // Ghost: take the tree from forest_own using find_entry_by_idx position
  // (same pattern as merge loop: use Some?.v (find_entry_by_idx ...) as the index)
  forest_own_take_at active_final (Some?.v (find_entry_by_idx active_final result_idx));
  
  // Rewrite is_htree to use runtime pointer (same pattern as merge loop)
  rewrite (is_htree (entry_ptr (L.index active_final (Some?.v (find_entry_by_idx active_final result_idx))))
                    (entry_tree (L.index active_final (Some?.v (find_entry_by_idx active_final result_idx)))))
       as (is_htree result
                    (entry_tree (L.index active_final (Some?.v (find_entry_by_idx active_final result_idx)))));
  
  // Since L.length active_final == 1 and Some?.v < 1, Some?.v == 0
  // Rewrite to use index 0 for cleaner postcondition matching
  rewrite (is_htree result
                    (entry_tree (L.index active_final (Some?.v (find_entry_by_idx active_final result_idx)))))
       as (is_htree result (entry_tree (L.index active_final 0)));
  
  // Dispose of empty forest_own and clean up
  // active_final has L.length == 1 (from loop exit: n - (n-1) = 1)
  // Some?.v ... == 0, so list_remove_at at 0 gives empty list
  list_remove_at_length active_final (Some?.v (find_entry_by_idx active_final result_idx));
  rewrite (forest_own (list_remove_at active_final (Some?.v (find_entry_by_idx active_final result_idx))))
       as emp;
  
  // Prove same_frequency_multiset
  all_leaf_freqs_singleton_full active_final (seq_to_pos_list freq_seq 0);
  
  // Derive cost equality from merge_bundle's cost invariant:
  //   forest_total_cost [final] + greedy_cost [freq_of final] == greedy_cost(initial)
  //   cost(final) + 0 == greedy_cost(initial)
  forest_total_cost_singleton active_final;
  forest_root_freqs_singleton active_final;
  greedy_cost_singleton (HSpec.freq_of (entry_tree (L.index active_final 0)));
  
  // Prove is_wpl_optimal via greedy_cost bridge
  seq_to_pos_list_length freq_seq 0;
  HOpt.greedy_cost_implies_optimal
    (entry_tree (L.index active_final 0))
    (seq_to_pos_list freq_seq 0);
  
  // Clean up
  PQ.free pq;
  Box.free dummy;
  V.free nodes;
  
  result
}
#pop-options
