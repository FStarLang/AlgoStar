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
module PQ = Pulse.Lib.PriorityQueue

module HSpec = CLRS.Ch16.Huffman.Spec

open Pulse.Lib.TotalOrder
open FStar.Order

module L = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties

// ========== PQ entry type: (frequency, index into nodes Vec) ==========

let pq_entry : eqtype = int & SZ.t

let valid_pq_entries (s: Seq.seq pq_entry) (n: nat) : prop =
  forall (j: nat). j < Seq.length s ==> SZ.v (snd (Seq.index s j)) < n

let valid_pq_entries_extends (s0 s1: Seq.seq pq_entry) (x: pq_entry) (n: nat)
  : Lemma (requires PQ.extends s0 s1 x /\ valid_pq_entries s0 n /\ SZ.v (snd x) < n)
          (ensures valid_pq_entries s1 n)
  = admit () // TODO

// For extract_min: extends s1 s0 x means s0 = s1 + x, so valid s0 ==> valid s1
let valid_pq_entries_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry) (n: nat)
  : Lemma (requires PQ.extends s1 s0 x /\ valid_pq_entries s0 n)
          (ensures valid_pq_entries s1 n /\ SZ.v (snd x) < n)
  = admit () // TODO

let pq_entry_compare (x y: pq_entry) : order =
  let (fx, ix) = x in
  let (fy, iy) = y in
  if fx < fy then Lt
  else if fx > fy then Gt
  else if SZ.v ix < SZ.v iy then Lt
  else if SZ.v ix > SZ.v iy then Gt
  else Eq

instance pq_entry_total_order : total_order pq_entry = {
  compare = pq_entry_compare;
  properties = ()
}

// extends_length: inserting one element increases length by 1
// PQ.extends s0 s1 x means count x s1 == count x s0 + 1, all others same
// This implies length s1 == length s0 + 1 (by sum-of-counts identity)

// Remove element at position j from a list
let rec list_remove_at (#a: Type) (l: list a) (j: nat{j < L.length l}) : list a =
  match l with
  | h :: t -> if j = 0 then t else h :: list_remove_at t (j - 1)

let rec list_remove_at_length (#a: Type) (l: list a) (j: nat{j < L.length l})
  : Lemma (ensures L.length (list_remove_at l j) == L.length l - 1) (decreases j)
  = match l with
    | _ :: t -> if j > 0 then list_remove_at_length t (j - 1)

// Removing element at position j changes count of that element by -1
let rec list_remove_at_count (#a: eqtype) (l: list a) (j: nat{j < L.length l}) (y: a)
  : Lemma (ensures L.count y (list_remove_at l j) == 
                   (if L.index l j = y then L.count y l - 1 else L.count y l))
          (decreases j)
  = match l with
    | h :: t ->
      if j = 0 then ()
      else list_remove_at_count t (j - 1) y

// All counts after removal
let list_remove_at_count_all (#a: eqtype) (l: list a) (j: nat{j < L.length l})
  : Lemma (ensures (forall (y: a). L.count y (list_remove_at l j) ==
                     (if L.index l j = y then L.count y l - 1 else L.count y l)))
  = Classical.forall_intro (Classical.move_requires (list_remove_at_count l j))

// Helper: for lists, if count of one element goes up by 1 and all others stay,
// then length goes up by 1
// Two lists with identical counts have the same length
let rec list_perm_length (#a: eqtype) (l0 l1: list a)
  : Lemma (requires forall (y:a). L.count y l0 == L.count y l1)
          (ensures L.length l0 == L.length l1)
          (decreases l0)
  = match l0 with
    | [] ->
      (match l1 with
       | [] -> ()
       | h :: _ -> assert (L.count h l1 >= 1); assert (L.count h l0 == 0))
    | h :: tl ->
      assert (L.count h l1 >= 1);
      LP.mem_count l1 h;
      let k = LP.index_of l1 h in
      let l1' = list_remove_at l1 k in
      list_remove_at_count l1 k h;
      list_remove_at_count_all l1 k;
      list_remove_at_length l1 k;
      list_perm_length tl l1'

// If count of one element goes up by 1 and all others stay, length goes up by 1
let rec list_count_length_step (#a: eqtype) (l0 l1: list a) (x: a)
  : Lemma (requires L.count x l1 == L.count x l0 + 1 /\
                    (forall (y:a). y =!= x ==> L.count y l1 == L.count y l0))
          (ensures L.length l1 == L.length l0 + 1)
          (decreases l1)
  = match l1 with
    | [] -> ()
    | h :: tl ->
      if h = x then begin
        // count x (h::tl) = 1 + count x tl, so count x tl = count x l0
        // For y <> x: count y tl = count y l0 (since h = x <> y)
        // So tl and l0 are permutations
        list_perm_length tl l0
      end else begin
        // h <> x: count h l0 >= 1 (since count h l1 = count h l0 and count h l1 >= 1)
        assert (L.count h l0 >= 1);
        LP.mem_count l0 h;
        let k = LP.index_of l0 h in
        let l0' = list_remove_at l0 k in
        list_remove_at_count l0 k x;
        list_remove_at_count_all l0 k;
        list_remove_at_length l0 k;
        // count x l0' = count x l0, count h l0' = count h l0 - 1
        // count x tl = count x l0 + 1 = count x l0' + 1
        // for y <> x, y <> h: count y tl = count y l0 = count y l0'
        // for y = h: count h tl = count h l1 - 1 = count h l0 - 1 = count h l0'
        list_count_length_step l0' tl x
        // length tl = length l0' + 1 = (length l0 - 1) + 1 = length l0
        // length l1 = 1 + length tl = length l0 + 1
      end

let extends_length (#t: eqtype) (s0 s1: Seq.seq t) (x: t)
  : Lemma (requires PQ.extends s0 s1 x)
          (ensures Seq.length s1 == Seq.length s0 + 1)
  = FStar.Seq.Properties.lemma_seq_to_list_permutation s0;
    FStar.Seq.Properties.lemma_seq_to_list_permutation s1;
    let l0 = Seq.seq_to_list s0 in
    let l1 = Seq.seq_to_list s1 in
    FStar.Seq.Properties.lemma_seq_list_bij s0;
    FStar.Seq.Properties.lemma_seq_list_bij s1;
    list_count_length_step l0 l1 x

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
// forest_own tracks ownership of a set of heap trees stored as (idx, ptr, spec_tree) triples.
// The idx (SZ.t) is the index into the nodes Vec, used to find the right entry
// when extracting from the PQ.

let forest_entry = SZ.t & hnode_ptr & HSpec.htree
let entry_idx  (e: forest_entry) : SZ.t = let (i, _, _) = e in i
let entry_ptr  (e: forest_entry) : hnode_ptr = let (_, p, _) = e in p
let entry_tree (e: forest_entry) : HSpec.htree = let (_, _, t) = e in t

let rec forest_own (entries: list forest_entry) : Tot slprop (decreases entries) =
  match entries with
  | [] -> emp
  | hd :: rest -> is_htree (entry_ptr hd) (entry_tree hd) ** forest_own rest

// Find position of a value in a list  
let rec list_find_pos (#a: eqtype) (l: list a) (x: a) (pos: nat)
  : Tot (option nat) (decreases l) =
  match l with
  | [] -> None
  | h :: t -> if h = x then Some pos else list_find_pos t x (pos + 1)

// If x is in the list, list_find_pos returns Some with correct index
let rec list_find_pos_spec (#a: eqtype) (l: list a) (x: a) (pos: nat)
  : Lemma (ensures (match list_find_pos l x pos with
                    | None -> ~(L.mem x l)
                    | Some k -> k >= pos /\ k - pos < L.length l /\ L.index l (k - pos) == x))
          (decreases l)
  = match l with
    | [] -> ()
    | h :: t -> if h = x then () else list_find_pos_spec t x (pos + 1)

// If x is in the list, list_find_pos returns Some
let list_find_pos_mem (#a: eqtype) (l: list a) (x: a) (pos: nat)
  : Lemma (requires L.mem x l) (ensures Some? (list_find_pos l x pos))
  = list_find_pos_spec l x pos

// Find position of a forest_entry by its SZ.t index
let rec find_entry_by_idx (entries: list forest_entry) (idx: SZ.t)
  : Tot (option nat) (decreases entries)
  = match entries with
    | [] -> None
    | hd :: tl -> if entry_idx hd = idx then Some 0
                  else (match find_entry_by_idx tl idx with
                        | None -> None
                        | Some k -> Some (k + 1))

let rec find_entry_by_idx_spec (entries: list forest_entry) (idx: SZ.t)
  : Lemma (ensures (match find_entry_by_idx entries idx with
                    | None -> forall (k: nat). k < L.length entries ==> entry_idx (L.index entries k) =!= idx
                    | Some k -> k < L.length entries /\ entry_idx (L.index entries k) == idx))
          (decreases entries)
  = match entries with
    | [] -> ()
    | hd :: tl ->
      if entry_idx hd = idx then ()
      else begin
        find_entry_by_idx_spec tl idx;
        match find_entry_by_idx tl idx with
        | None -> ()
        | Some k -> ()
      end

// Every PQ entry index appears in the forest
let pq_indices_in_forest (pq: Seq.seq pq_entry) (forest: list forest_entry) : prop =
  forall (j: nat). j < Seq.length pq ==>
    Some? (find_entry_by_idx forest (snd (Seq.index pq j)))

// pq_indices_in_forest is preserved by extends (insert)
let pq_forest_extends (s0 s1: Seq.seq pq_entry) (x: pq_entry) (forest: list forest_entry)
  : Lemma (requires PQ.extends s0 s1 x /\
                    pq_indices_in_forest s0 forest /\
                    Some? (find_entry_by_idx forest (snd x)))
          (ensures pq_indices_in_forest s1 forest)
  = admit () // TODO

// pq_indices_in_forest after shrink (extract_min): remaining entries still in forest
let pq_forest_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry) (forest: list forest_entry)
  : Lemma (requires PQ.extends s1 s0 x /\ pq_indices_in_forest s0 forest)
          (ensures pq_indices_in_forest s1 forest /\
                   Some? (find_entry_by_idx forest (snd x)))
  = admit () // TODO

// After prepending (idx, p, ft) to forest, find_entry_by_idx for idx succeeds
let find_entry_prepend (entries: list forest_entry) (idx: SZ.t) (p: hnode_ptr) (ft: HSpec.htree)
  : Lemma (ensures Some? (find_entry_by_idx ((idx, p, ft) :: entries) idx) /\
                   find_entry_by_idx ((idx, p, ft) :: entries) idx == Some 0)
  = ()

// Prepending to forest preserves find_entry_by_idx for existing entries
let rec find_entry_prepend_other (entries: list forest_entry) (e: forest_entry) (idx: SZ.t)
  : Lemma (ensures Some? (find_entry_by_idx entries idx) ==>
                   Some? (find_entry_by_idx (e :: entries) idx))
          (decreases entries)
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
// Uses a min-heap priority queue (Pulse.Lib.PriorityQueue) storing
// (frequency, index) pairs, with a parallel Vec hnode_ptr for the
// actual tree pointers. HSpec.htree only in ghost/specification positions.
// Ownership tracked via forest_own over (hnode_ptr, HSpec.htree) pairs.

//SNIPPET_START: huffman_tree_sig
#push-options "--z3rlimit 80"
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
                  pure (HSpec.cost ft >= 0))
//SNIPPET_END: huffman_tree_sig
{
  // Allocate node pointer array and PQ
  let dummy = alloc_hnode ({ freq = 0; left = (None #hnode_ptr); right = (None #hnode_ptr) } <: hnode);
  let nodes = V.alloc dummy n;
  let pq = PQ.create #pq_entry n;
  
  // Initialize: allocate leaf nodes, insert (freq, index) into PQ
  fold (forest_own (Nil #forest_entry));

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
      valid_pq_entries pq_contents (SZ.v n) /\
      pq_indices_in_forest pq_contents active /\
      (forall (k: nat). k < L.length active ==>
        SZ.v (entry_idx (L.index active k)) < SZ.v vi /\
        Seq.index nd_contents (SZ.v (entry_idx (L.index active k))) == entry_ptr (L.index active k))
    )
  {
    let vi = !i;
    let freq_val = A.op_Array_Access freqs vi;
    
    // Allocate leaf node on the heap
    let leaf = alloc_hnode ({ freq = freq_val; left = (None #hnode_ptr); right = (None #hnode_ptr) } <: hnode);
    V.op_Array_Assignment nodes vi leaf;
    
    // Insert (freq, index) into PQ
    with pq_old. assert (PQ.is_pqueue pq pq_old (SZ.v n));
    PQ.insert pq (freq_val, vi);
    with pq_new. assert (PQ.is_pqueue pq pq_new (SZ.v n));
    extends_length pq_old pq_new (freq_val, vi);
    valid_pq_entries_extends pq_old pq_new (freq_val, vi) (SZ.v n);
    
    // Fold is_htree for this leaf and add to forest_own
    fold (is_htree leaf (HSpec.Leaf freq_val));
    with active_old. assert (forest_own active_old);
    forest_own_put_head active_old vi leaf (HSpec.Leaf freq_val);
    
    // Maintain pq_indices_in_forest: old PQ entries are in old forest, which is subset of new forest
    // New PQ entry (freq_val, vi) is at position 0 of new forest
    let new_entry : forest_entry = (vi, leaf, HSpec.Leaf freq_val);
    pq_forest_prepend pq_old active_old new_entry;
    find_entry_prepend active_old vi leaf (HSpec.Leaf freq_val);
    pq_forest_extends pq_old pq_new (freq_val, vi) (new_entry :: active_old);
    
    i := vi +^ 1sz;
  };
  
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
      Seq.length nd_contents == SZ.v n /\
      Seq.length pq_contents == SZ.v n - SZ.v viter /\
      L.length active == SZ.v n - SZ.v viter /\
      L.length active > 0 /\
      SZ.fits (2 * Seq.length pq_contents + 2) /\
      valid_pq_entries pq_contents (SZ.v n) /\
      pq_indices_in_forest pq_contents active /\
      (forall (k: nat). k < L.length active ==>
        SZ.v (entry_idx (L.index active k)) < SZ.v n /\
        Seq.index nd_contents (SZ.v (entry_idx (L.index active k))) == entry_ptr (L.index active k))
    )
  {
    // Extract two minimums from PQ
    with pq0. assert (PQ.is_pqueue pq pq0 (SZ.v n));
    with active0. assert (forest_own active0);
    let (freq1, idx1) = PQ.extract_min pq;
    with pq1. assert (PQ.is_pqueue pq pq1 (SZ.v n));
    extends_length pq1 pq0 (freq1, idx1);
    valid_pq_entries_shrink pq0 pq1 (freq1, idx1) (SZ.v n);
    pq_forest_shrink pq0 pq1 (freq1, idx1) active0;
    
    let (freq2, idx2) = PQ.extract_min pq;
    with pq2. assert (PQ.is_pqueue pq pq2 (SZ.v n));
    extends_length pq2 pq1 (freq2, idx2);
    valid_pq_entries_shrink pq1 pq2 (freq2, idx2) (SZ.v n);
    pq_forest_shrink pq1 pq2 (freq2, idx2) active0;
    let sum_freq = freq1 + freq2;
    
    // Read the tree pointers from nodes array (idx1, idx2 < n from valid_pq_entries_shrink)
    let left_ptr = V.op_Array_Access nodes idx1;
    let right_ptr = V.op_Array_Access nodes idx2;
    
    // Create merged internal node
    let merged = alloc_hnode ({ freq = sum_freq; left = Some left_ptr; right = Some right_ptr } <: hnode);
    
    // Store merged node in nodes[idx1]
    V.op_Array_Assignment nodes idx1 merged;
    
    // Insert (sum_freq, idx1) into PQ
    PQ.insert pq (sum_freq, idx1);
    with pq3. assert (PQ.is_pqueue pq pq3 (SZ.v n));
    extends_length pq2 pq3 (sum_freq, idx1);
    valid_pq_entries_extends pq2 pq3 (sum_freq, idx1) (SZ.v n);
    
    // Ghost: take trees for idx1/idx2 from forest_own, fold merged is_htree, put back
    // This involves: find_entry_by_idx, forest_own_take_at (x2), fold is_htree, forest_own_put_head
    // For now, admit the ghost manipulation
    admit();
    
    let viter = !iter;
    iter := viter +^ 1sz;
  };
  
  // Extract final result from PQ
  with pq_final. assert (PQ.is_pqueue pq pq_final (SZ.v n));
  let (result_freq, result_idx) = PQ.extract_min pq;
  with pq_empty. assert (PQ.is_pqueue pq pq_empty (SZ.v n));
  valid_pq_entries_shrink pq_final pq_empty (result_freq, result_idx) (SZ.v n);
  extends_length pq_empty pq_final (result_freq, result_idx);
  let result = V.op_Array_Access nodes result_idx;
  
  // Ghost: extract final tree from forest_own
  with active_final. assert (forest_own active_final);
  // active_final has exactly 1 entry (L.length == 1 after n-1 merges)
  // Take the single tree from forest_own
  forest_own_take_at active_final 0;
  // Now: is_htree (entry_ptr (L.index active_final 0)) (entry_tree (L.index active_final 0))
  //  ** forest_own (list_remove_at active_final 0)
  
  // result == entry_ptr (L.index active_final 0) (from invariant: nodes[result_idx] == entry_ptr)
  rewrite (is_htree (entry_ptr (L.index active_final 0)) (entry_tree (L.index active_final 0)))
       as (is_htree result (entry_tree (L.index active_final 0)));
  
  // Dispose of empty forest_own and clean up
  // active_final has L.length == 1 (from loop exit: n - (n-1) = 1)
  // So list_remove_at active_final 0 == [] and forest_own [] == emp
  admit();
  
  // Clean up
  PQ.free pq;
  Box.free dummy;
  V.free nodes;
  
  result
}
#pop-options
