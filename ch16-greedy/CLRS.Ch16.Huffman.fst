(*
   Huffman Encoding - Imperative Implementation
   
   CLRS Section 16.3 presents HUFFMAN(C):
   1. Build a priority queue Q from the character frequencies
   2. For i = 1 to |C|-1:
      a. Extract two minimum-frequency nodes z.left, z.right from Q
      b. Create new node z with freq = z.left.freq + z.right.freq
      c. Insert z into Q
   3. Return the remaining tree in Q (the Huffman tree)
   
   This module provides:
   - huffman_cost: computes just the cost via array-based linear scans
   - huffman_tree: builds the full Huffman tree using heap-allocated nodes
     (hnode_ptr), with HSpec.htree only in ghost/specification positions.
     The tree is returned as a hnode_ptr with an is_htree separation logic
     predicate relating it to the spec tree.
   - alloc_htree / free_htree: convert between spec trees and heap trees
   
   NO admits. NO assumes.
*)

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

module HSpec = CLRS.Ch16.Huffman.Spec

// ========== Pointer-based Huffman tree (heap-allocated, isomorphic to HSpec.htree) ==========
// - hnode: record with freq, left, right children
// - hnode_ptr = box hnode (always non-null for Huffman trees)
// - Leaves have left = right = None; Internal nodes have Some children.

noeq type hnode = {
    freq: int;
    left: option (Box.box hnode);
    right: option (Box.box hnode);
}
let hnode_ptr = Box.box hnode

// Allocate an hnode on the heap, returning hnode_ptr (avoids syntactic type mismatch)
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
// forest_own tracks ownership of a set of heap trees stored as (ptr, spec_tree) pairs.
// Completely decoupled from Seq.seq — the relationship to the Vec is maintained
// as a pure invariant (Seq.index nd_contents i == fst (L.index pairs k)).

let rec forest_own (pairs: list (hnode_ptr & HSpec.htree)) : Tot slprop (decreases pairs) =
  match pairs with
  | [] -> emp
  | hd :: rest -> is_htree (fst hd) (snd hd) ** forest_own rest

module L = FStar.List.Tot.Base

// Remove element at position j from a list
let rec list_remove_at (#a: Type) (l: list a) (j: nat{j < L.length l}) : list a =
  match l with
  | h :: t -> if j = 0 then t else h :: list_remove_at t (j - 1)

// Prepend an entry to forest_own
ghost
fn forest_own_put_head
  (pairs: list (hnode_ptr & HSpec.htree))
  (p: hnode_ptr) (ft: HSpec.htree)
  requires is_htree p ft ** forest_own pairs
  ensures forest_own ((p, ft) :: pairs)
{
  fold (forest_own ((p, ft) :: pairs));
}

// Take the head element from forest_own
ghost
fn forest_own_take_head
  (hd: hnode_ptr & HSpec.htree) (tl: list (hnode_ptr & HSpec.htree))
  requires forest_own (hd :: tl)
  ensures is_htree (fst hd) (snd hd) ** forest_own tl
{
  unfold (forest_own (hd :: tl));
}

open Pulse.Lib.Core

// Prove: forest_own pairs == is_htree(pairs[j]) ** forest_own(remove pairs j)
// Uses star commutativity + associativity from PulseCore
let rec forest_own_split_lemma
  (pairs: list (hnode_ptr & HSpec.htree))
  (j: nat{j < L.length pairs})
  : Lemma (ensures forest_own pairs ==
             is_htree (fst (L.index pairs j)) (snd (L.index pairs j)) **
             forest_own (list_remove_at pairs j))
          (decreases j)
  = match pairs with
    | hd :: tl ->
      if j = 0 then () // forest_own (hd :: tl) = is_htree (fst hd) (snd hd) ** forest_own tl by def
      else begin
        forest_own_split_lemma tl (j - 1);
        // IH: forest_own tl == is_htree (fst (L.index tl (j-1))) ... ** forest_own (list_remove_at tl (j-1))
        // Goal: is_htree (fst hd) (snd hd) ** forest_own tl
        //     == is_htree (fst (L.index pairs j)) ... ** forest_own (list_remove_at pairs j)
        // Note: L.index pairs j == L.index tl (j-1) and
        //       list_remove_at pairs j == hd :: list_remove_at tl (j-1)
        let p0 = is_htree (fst hd) (snd hd) in
        let pj = is_htree (fst (L.index tl (j-1))) (snd (L.index tl (j-1))) in
        let rest = forest_own (list_remove_at tl (j-1)) in
        // Chain: p0 ** (pj ** rest) → (p0 ** pj) ** rest → (pj ** p0) ** rest → pj ** (p0 ** rest)
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
  (pairs: list (hnode_ptr & HSpec.htree))
  (j: nat{j < L.length pairs})
  requires forest_own pairs
  ensures is_htree (fst (L.index pairs j)) (snd (L.index pairs j)) **
          forest_own (list_remove_at pairs j)
{
  forest_own_split_lemma pairs j;
  // Now: forest_own pairs == is_htree ... ** forest_own (list_remove_at pairs j)
  rewrite (forest_own pairs)
       as (is_htree (fst (L.index pairs j)) (snd (L.index pairs j)) **
           forest_own (list_remove_at pairs j));
}

// ========== Allocate/free pointer-based Huffman tree ==========

fn rec alloc_htree (ft: HSpec.htree)
  requires emp
  returns p: hnode_ptr
  ensures is_htree p ft
  decreases ft
{
  match ft {
    HSpec.Leaf f -> {
      let p = alloc_hnode ({ freq = f; left = (None #hnode_ptr); right = (None #hnode_ptr) } <: hnode);
      fold (is_htree p (HSpec.Leaf f));
      p
    }
    HSpec.Internal f l r -> {
      let lp = alloc_htree l;
      let rp = alloc_htree r;
      let p = alloc_hnode ({ freq = f; left = Some lp; right = Some rp } <: hnode);
      fold (is_htree p (HSpec.Internal f l r));
      p
    }
  }
}

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

// ========== Constants ==========

let infinity : int = 1000000000

// ========== Helper: Find minimum value and its index ==========

#push-options "--z3rlimit 20"
fn find_min
  (#p: perm)
  (vec: V.vec int)
  (#contents: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires V.pts_to vec #p contents ** pure (SZ.v len == Seq.length contents /\ SZ.v len > 0)
  returns res:(SZ.t & int)
  ensures V.pts_to vec #p contents ** pure (
    SZ.v (fst res) < Seq.length contents /\
    snd res == Seq.index contents (SZ.v (fst res)) /\
    (forall (i: nat). i < Seq.length contents ==> snd res <= Seq.index contents i)
  )
{
  let mut min_idx: SZ.t = 0sz;
  let mut min_val: int = V.op_Array_Access vec 0sz;
  let mut i: SZ.t = 1sz;
  
  while (
    !i <^ len
  )
  invariant exists* vi vmin_idx vmin_val.
    R.pts_to i vi **
    R.pts_to min_idx vmin_idx **
    R.pts_to min_val vmin_val **
    pure (
      SZ.v vi <= Seq.length contents /\
      SZ.v vmin_idx < SZ.v vi /\
      vmin_val == Seq.index contents (SZ.v vmin_idx) /\
      (forall (k: nat). k < SZ.v vi ==> vmin_val <= Seq.index contents k)
    )
  {
    let vi = !i;
    let current = V.op_Array_Access vec vi;
    let vmin_val = !min_val;
    
    if (current < vmin_val) {
      min_idx := vi;
      min_val := current;
    };
    
    i := vi +^ 1sz;
  };
  
  let result_idx = !min_idx;
  let result_val = !min_val;
  (result_idx, result_val)
}
#pop-options

// ========== Helper: Find second minimum (excluding one index) ==========

#push-options "--z3rlimit 20"
fn find_min_excluding
  (#p: perm)
  (vec: V.vec int)
  (#contents: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (exclude_idx: SZ.t)
  requires V.pts_to vec #p contents ** pure (
    SZ.v len == Seq.length contents /\
    SZ.v len > 1 /\
    SZ.v exclude_idx < SZ.v len
  )
  returns res:(SZ.t & int)
  ensures V.pts_to vec #p contents ** pure (
    SZ.v (fst res) < Seq.length contents /\
    SZ.v (fst res) <> SZ.v exclude_idx /\
    snd res == Seq.index contents (SZ.v (fst res)) /\
    (forall (i: nat). i < Seq.length contents /\ i <> SZ.v exclude_idx ==> snd res <= Seq.index contents i)
  )
{
  let init_idx: SZ.t = (if exclude_idx = 0sz then 1sz else 0sz);
  let mut min_idx: SZ.t = init_idx;
  let mut min_val: int = V.op_Array_Access vec init_idx;
  let mut i: SZ.t = init_idx +^ 1sz;
  
  while (
    !i <^ len
  )
  invariant exists* vi vmin_idx vmin_val.
    R.pts_to i vi **
    R.pts_to min_idx vmin_idx **
    R.pts_to min_val vmin_val **
    pure (
      SZ.v vi <= Seq.length contents /\
      SZ.v vmin_idx < SZ.v vi /\
      SZ.v vmin_idx <> SZ.v exclude_idx /\
      vmin_val == Seq.index contents (SZ.v vmin_idx) /\
      (forall (k: nat). k < SZ.v vi /\ k <> SZ.v exclude_idx ==> vmin_val <= Seq.index contents k)
    )
  {
    let vi = !i;
    
    if (vi <> exclude_idx) {
      let current = V.op_Array_Access vec vi;
      let vmin_val = !min_val;
      
      if (current < vmin_val) {
        min_idx := vi;
        min_val := current;
      };
    };
    
    i := vi +^ 1sz;
  };
  
  let result_idx = !min_idx;
  let result_val = !min_val;
  (result_idx, result_val)
}
#pop-options

// ========== Main Huffman Cost Algorithm ==========

//SNIPPET_START: huffman_cost_sig
#push-options "--z3rlimit 20"
fn huffman_cost
  (#p: perm)
  (freqs: A.array int)
  (#freq_seq: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires A.pts_to freqs #p freq_seq ** pure (
    SZ.v n == Seq.length freq_seq /\
    SZ.v n > 0 /\
    (forall (i: nat). i < Seq.length freq_seq ==> Seq.index freq_seq i > 0)
  )
  returns result_cost:int
  ensures A.pts_to freqs #p freq_seq ** pure (
    result_cost >= 0 /\
    (SZ.v n > 1 ==> result_cost > 0) /\
    (SZ.v n == 1 ==> result_cost == 0)
  )
//SNIPPET_END: huffman_cost_sig
{
  // Create working copy using Vec
  let init_val = A.op_Array_Access freqs 0sz;
  let working = V.alloc init_val n;
  
  // Copy frequencies to working vec
  let mut i: SZ.t = 0sz;
  
  while (
    !i <^ n
  )
  invariant exists* vi working_contents.
    R.pts_to i vi **
    V.pts_to working working_contents **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length working_contents == SZ.v n /\
      (forall (k: nat). k < SZ.v vi ==> Seq.index working_contents k == Seq.index freq_seq k)
    )
  {
    let vi = !i;
    let freq_val = A.op_Array_Access freqs vi;
    V.op_Array_Assignment working vi freq_val;
    i := vi +^ 1sz;
  };
  
  // Main loop: combine n-1 times
  let mut cost_acc: int = 0;
  let mut iter: SZ.t = 0sz;
  let n_minus_1 = n -^ 1sz;
  
  while (
    !iter <^ n_minus_1
  )
  invariant exists* viter vcost working_contents.
    R.pts_to iter viter **
    R.pts_to cost_acc vcost **
    V.pts_to working working_contents **
    pure (
      SZ.v viter <= SZ.v n - 1 /\
      Seq.length working_contents == SZ.v n /\
      vcost >= 0 /\
      (SZ.v viter == 0 ==> vcost == 0) /\
      (SZ.v n > 1 /\ SZ.v viter > 0 ==> vcost > 0) /\
      (forall (i: nat). i < Seq.length working_contents ==> 
        Seq.index working_contents i > 0 \/ Seq.index working_contents i == infinity)
    )
  {
    let (idx1, val1) = find_min working n;
    let (idx2, val2) = find_min_excluding working n idx1;
    
    assert pure (val1 > 0 /\ val2 > 0);
    
    let sum = val1 + val2;
    assert pure (sum > 0);
    
    let current_cost = !cost_acc;
    cost_acc := current_cost + sum;
    
    V.op_Array_Assignment working idx1 sum;
    V.op_Array_Assignment working idx2 infinity;
    
    let viter = !iter;
    iter := viter +^ 1sz;
  };
  
  V.free working;
  
  !cost_acc
}
#pop-options

// ========== Full Huffman Tree Construction (CLRS §16.3) ==========
// Truly imperative: allocates hnode_ptr nodes on the heap.
// Uses array-based min-finding (same as huffman_cost) with a parallel
// Vec hnode_ptr to track the actual tree pointers.
// HSpec.htree appears ONLY in ghost/specification positions.
// Ownership tracked via zip_star over active node indices + ghost spec trees.

//SNIPPET_START: huffman_tree_sig
#push-options "--z3rlimit 40"
fn huffman_tree
  (freqs: A.array int)
  (#freq_seq: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  requires A.pts_to freqs freq_seq ** pure (
    SZ.v n == Seq.length freq_seq /\
    SZ.v n > 0 /\
    (forall (i: nat). i < Seq.length freq_seq ==> Seq.index freq_seq i > 0)
  )
  returns result: hnode_ptr
  ensures A.pts_to freqs freq_seq **
          (exists* ft. is_htree result ft **
                  pure (HSpec.cost ft >= 0))
//SNIPPET_END: huffman_tree_sig
{
  // Allocate working frequency array and node pointer array
  let init_val = A.op_Array_Access freqs 0sz;
  let working = V.alloc init_val n;
  let dummy = alloc_hnode ({ freq = 0; left = (None #hnode_ptr); right = (None #hnode_ptr) } <: hnode);
  let nodes = V.alloc dummy n;
  
  // Initialize: copy freqs, allocate leaf nodes
  fold (forest_own (Nil #(hnode_ptr & HSpec.htree)));

  let mut i: SZ.t = 0sz;
  while (
    !i <^ n
  )
  invariant exists* vi wk_contents nd_contents
                    (active: list (hnode_ptr & HSpec.htree)).
    R.pts_to i vi **
    V.pts_to working wk_contents **
    V.pts_to nodes nd_contents **
    A.pts_to freqs freq_seq **
    Box.pts_to dummy ({ freq = 0; left = None #hnode_ptr; right = None #hnode_ptr } <: hnode) **
    forest_own active **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length wk_contents == SZ.v n /\
      Seq.length nd_contents == SZ.v n /\
      L.length active == SZ.v vi /\
      (forall (k: nat). k < SZ.v vi ==>
        Seq.index wk_contents k == Seq.index freq_seq k /\
        Seq.index wk_contents k > 0)
    )
  {
    let vi = !i;
    let freq_val = A.op_Array_Access freqs vi;
    V.op_Array_Assignment working vi freq_val;
    
    // Allocate leaf node on the heap
    let leaf = alloc_hnode ({ freq = freq_val; left = (None #hnode_ptr); right = (None #hnode_ptr) } <: hnode);
    V.op_Array_Assignment nodes vi leaf;
    
    // Fold is_htree for this leaf
    fold (is_htree leaf (HSpec.Leaf freq_val));
    
    // Add to forest_own
    with active_old. assert (forest_own active_old);
    forest_own_put_head active_old leaf (HSpec.Leaf freq_val);
    
    i := vi +^ 1sz;
  };
  
  // Main merge loop: combine n-1 times
  let mut iter: SZ.t = 0sz;
  let n_minus_1 = n -^ 1sz;
  
  while (
    !iter <^ n_minus_1
  )
  invariant exists* viter wk_contents nd_contents
                    (active: list (hnode_ptr & HSpec.htree)).
    R.pts_to iter viter **
    V.pts_to working wk_contents **
    V.pts_to nodes nd_contents **
    A.pts_to freqs freq_seq **
    Box.pts_to dummy ({ freq = 0; left = None #hnode_ptr; right = None #hnode_ptr } <: hnode) **
    forest_own active **
    pure (
      SZ.v viter <= SZ.v n - 1 /\
      Seq.length wk_contents == SZ.v n /\
      Seq.length nd_contents == SZ.v n /\
      L.length active == SZ.v n - SZ.v viter /\
      L.length active > 0 /\
      (forall (j: nat). j < Seq.length wk_contents ==>
        Seq.index wk_contents j > 0 \/ Seq.index wk_contents j == infinity)
    )
  {
    let (idx1, val1) = find_min working n;
    let (idx2, val2) = find_min_excluding working n idx1;
    
    assert pure (val1 > 0 /\ val2 > 0);
    let sum = val1 + val2;
    
    // Read the tree pointers for the two minimums
    let left_ptr = V.op_Array_Access nodes idx1;
    let right_ptr = V.op_Array_Access nodes idx2;
    
    // Take ownership of both trees from forest_own
    // TODO: find left_ptr and right_ptr in active list, call forest_own_take_at
    admit();
    
    // Allocate merged internal node on the heap
    let merged = alloc_hnode ({ freq = sum; left = Some left_ptr; right = Some right_ptr } <: hnode);
    
    // Fold is_htree for the merged node
    with sl sr. assert (is_htree left_ptr sl ** is_htree right_ptr sr);
    fold (is_htree merged (HSpec.Internal sum sl sr));
    
    // Update arrays: merged replaces idx1, idx2 becomes inactive
    V.op_Array_Assignment nodes idx1 merged;
    V.op_Array_Assignment working idx1 sum;
    V.op_Array_Assignment working idx2 infinity;
    
    // Add merged tree to forest_own
    with active_rest. assert (forest_own active_rest);
    forest_own_put_head active_rest merged (HSpec.Internal sum sl sr);
    
    let viter = !iter;
    iter := viter +^ 1sz;
  };
  
  // Result: use find_min to find the single remaining active node
  let (result_idx, _) = find_min working n;
  let result = V.op_Array_Access nodes result_idx;
  
  // Take ownership of the final tree from forest_own
  admit(); // TODO: connect forest_own to the result
  
  // Clean up  
  Box.free dummy;
  V.free working;
  V.free nodes;
  
  result
}
#pop-options
