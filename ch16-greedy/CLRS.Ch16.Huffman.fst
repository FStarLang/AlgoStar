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

// All PQ entries have positive frequencies
let pq_freqs_positive (pq: Seq.seq pq_entry) : prop =
  forall (j: nat). j < Seq.length pq ==> fst (Seq.index pq j) > 0

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

// PQ index uniqueness: no two entries share the same snd (index) component
let pq_idx_unique (s: Seq.seq pq_entry) : prop =
  forall (i j: nat). i < Seq.length s /\ j < Seq.length s /\ i <> j ==>
    snd (Seq.index s i) <> snd (Seq.index s j)

// If no element of s equals x, count x s = 0
let rec count_zero (#a: eqtype) (x: a) (s: Seq.seq a)
  : Lemma (requires forall (k: nat). k < Seq.length s ==> Seq.index s k <> x)
          (ensures FStar.Seq.Properties.count x s = 0)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      assert (Seq.head s == Seq.index s 0);
      let tl = Seq.tail s in
      let aux (k: nat{k < Seq.length tl}) : Lemma (Seq.index tl k <> x) =
        assert (Seq.index tl k == Seq.index s (k + 1))
      in
      Classical.forall_intro aux;
      count_zero x tl
    end

// If count x s = 1, then i and j both indexing x implies i = j
let rec count_one_unique (#a: eqtype) (x: a) (s: Seq.seq a) (i j: nat)
  : Lemma (requires FStar.Seq.Properties.count x s = 1 /\
                    i < Seq.length s /\ j < Seq.length s /\
                    Seq.index s i = x /\ Seq.index s j = x)
          (ensures i = j)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else if Seq.head s = x then begin
      // count x (tail s) = 0
      assert (FStar.Seq.Properties.count x (Seq.tail s) = 0);
      // So i = 0 and j = 0
      if i > 0 then begin
        assert (Seq.index (Seq.tail s) (i - 1) == Seq.index s i);
        FStar.Seq.Properties.mem_index x (Seq.tail s)
      end;
      if j > 0 then begin
        assert (Seq.index (Seq.tail s) (j - 1) == Seq.index s j);
        FStar.Seq.Properties.mem_index x (Seq.tail s)
      end
    end
    else begin
      // head <> x, so count x (tail s) = 1
      assert (FStar.Seq.Properties.count x (Seq.tail s) = 1);
      // i > 0 and j > 0
      assert (i > 0);
      assert (j > 0);
      assert (Seq.index (Seq.tail s) (i - 1) == Seq.index s i);
      assert (Seq.index (Seq.tail s) (j - 1) == Seq.index s j);
      count_one_unique x (Seq.tail s) (i - 1) (j - 1)
    end

// pq_idx_unique implies all entries are pairwise distinct, so count <= 1 for any element
let rec pq_idx_unique_count_le_1 (s: Seq.seq pq_entry) (x: pq_entry)
  : Lemma (requires pq_idx_unique s)
          (ensures FStar.Seq.Properties.count x s <= 1)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      let hd = Seq.head s in
      let tl = Seq.tail s in
      if hd = x then begin
        // count x s = 1 + count x tl; show count x tl = 0
        let aux2 (k: nat{k < Seq.length tl}) : Lemma (Seq.index tl k <> x) =
          assert (Seq.index tl k == Seq.index s (k + 1));
          assert (snd (Seq.index s (k + 1)) <> snd (Seq.index s 0))
        in
        Classical.forall_intro aux2;
        count_zero x tl
      end
      else begin
        // hd <> x, count x s = count x tl; need pq_idx_unique tl
        assert (forall (i: nat) (j: nat). i < Seq.length tl /\ j < Seq.length tl /\ i <> j ==>
          Seq.index tl i == Seq.index s (i + 1) /\ Seq.index tl j == Seq.index s (j + 1));
        pq_idx_unique_count_le_1 tl x
      end
    end

// After insert: pq_idx_unique extends (new entry's index is fresh)
#push-options "--z3rlimit 120"
let pq_idx_unique_extends (s0 s1: Seq.seq pq_entry) (x: pq_entry)
  : Lemma (requires PQ.extends s0 s1 x /\ pq_idx_unique s0 /\
                    (forall (j: nat). j < Seq.length s0 ==> snd (Seq.index s0 j) <> snd x))
          (ensures pq_idx_unique s1)
  = let aux (i j: nat)
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
let pq_idx_unique_shrink (s0 s1: Seq.seq pq_entry) (x: pq_entry)
  : Lemma (requires PQ.extends s1 s0 x /\ pq_idx_unique s0)
          (ensures pq_idx_unique s1 /\
                   (forall (j: nat). j < Seq.length s1 ==> snd (Seq.index s1 j) <> snd x))
  = let aux (i j: nat)
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

// After shrinking (removing x), if all entries in s0 had snd <> some_idx, entries in s1 also have snd <> some_idx
let pq_no_idx_preserved (s0 s1: Seq.seq pq_entry) (x: pq_entry) (some_idx: SZ.t)
  : Lemma (requires PQ.extends s1 s0 x /\
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

// Index into list_remove_at: elements before j stay, elements after j shift down
let rec list_remove_at_index (#a: Type) (l: list a) (j: nat{j < L.length l}) (k: nat)
  : Lemma (requires k < L.length l - 1)
          (ensures L.length (list_remove_at l j) == L.length l - 1 /\
                   L.index (list_remove_at l j) k == (if k < j then L.index l k else L.index l (k + 1)))
          (decreases l)
  = list_remove_at_length l j;
    match l with
    | h :: t ->
      if j = 0 then ()
      else if k = 0 then ()
      else begin list_remove_at_length t (j - 1); list_remove_at_index t (j - 1) (k - 1) end

// Remove two elements from a list (remove j1 first, then adjust j2)
let list_remove_two (#a: Type) (l: list a) (j1 j2: nat)
  : Pure (list a) (requires j1 < L.length l /\ j2 < L.length l /\ j1 <> j2)
         (ensures fun _ -> True)
  = list_remove_at_length l j1;
    let j2' = if j2 < j1 then j2 else j2 - 1 in
    list_remove_at (list_remove_at l j1) j2'

let list_remove_two_length (#a: Type) (l: list a) (j1 j2: nat)
  : Lemma (requires j1 < L.length l /\ j2 < L.length l /\ j1 <> j2)
          (ensures L.length (list_remove_two l j1 j2) == L.length l - 2)
  = list_remove_at_length l j1;
    let j2' = if j2 < j1 then j2 else j2 - 1 in
    list_remove_at_length (list_remove_at l j1) j2'

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

// Forest distinct indices: no two entries share the same index
let forest_distinct_indices (entries: list forest_entry) : prop =
  forall (i j: nat). i < L.length entries /\ j < L.length entries /\ i <> j ==>
    entry_idx (L.index entries i) <> entry_idx (L.index entries j)

let forest_distinct_indices_elim (entries: list forest_entry) (i j: nat)
  : Lemma (requires forest_distinct_indices entries /\ i < L.length entries /\ j < L.length entries /\ i <> j)
          (ensures entry_idx (L.index entries i) <> entry_idx (L.index entries j))
  = ()

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

// pq_indices_in_forest is preserved by extends (insert)
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

// forest_distinct_indices is preserved by list_remove_at
let forest_distinct_indices_remove_at (entries: list forest_entry) (j: nat)
  : Lemma (requires forest_distinct_indices entries /\ j < L.length entries)
          (ensures forest_distinct_indices (list_remove_at entries j))
  = let rem = list_remove_at entries j in
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
          // gives: L.index (list_remove_at rem1 j2') k == 
          //        if k < j2' then L.index rem1 k else L.index rem1 (k+1)
          // All entries in rem1 have entry_idx <> idx (from list_remove_at_no_idx)
          ()
        end
    in
    Classical.forall_intro aux

// forest_distinct_indices is preserved by prepend if head index is fresh
let forest_distinct_indices_prepend (entries: list forest_entry) (e: forest_entry)
  : Lemma (requires forest_distinct_indices entries /\
                    (forall (k: nat). k < L.length entries ==>
                      entry_idx (L.index entries k) <> entry_idx e))
          (ensures forest_distinct_indices (e :: entries))
  = let l' = e :: entries in
    let aux (i j: nat)
      : Lemma (ensures (i < L.length l' /\ j < L.length l' /\ i <> j) ==>
                       entry_idx (L.index l' i) <> entry_idx (L.index l' j))
      = ()
    in
    Classical.forall_intro_2 aux

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
#push-options "--split_queries always --z3rlimit 40"
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

// Forest idx bound: all entries have SZ.v (entry_idx ...) < SZ.v bound implies entry_idx <> bound
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

// ========== Leaf frequency multiset tracking ==========

// Convert a sequence of positive ints to a list of pos, starting from index k
// Elements <= 0 are clamped to 1 (shouldn't happen with valid input)
let rec seq_to_pos_list (s: Seq.seq int) (k: nat)
  : Tot (list pos) (decreases Seq.length s - k)
  = if k >= Seq.length s then []
    else
      let v : pos = if Seq.index s k > 0 then Seq.index s k else 1 in
      v :: seq_to_pos_list s (k + 1)

let rec seq_to_pos_list_length (s: Seq.seq int) (k: nat)
  : Lemma (ensures L.length (seq_to_pos_list s k) == (if k >= Seq.length s then 0 else Seq.length s - k))
          (decreases Seq.length s - k)
  = if k >= Seq.length s then ()
    else seq_to_pos_list_length s (k + 1)

// When all elements are positive, seq_to_pos_list index k is Seq.index s k
let seq_to_pos_list_index (s: Seq.seq int) (k: nat)
  : Lemma (requires k < Seq.length s /\ Seq.index s k > 0)
          (ensures Cons? (seq_to_pos_list s k) /\
                   L.hd (seq_to_pos_list s k) == Seq.index s k /\
                   L.tl (seq_to_pos_list s k) == seq_to_pos_list s (k + 1))
  = ()

// All leaf frequencies across the forest
let rec all_leaf_freqs (entries: list forest_entry) : list pos =
  match entries with
  | [] -> []
  | e :: rest -> HSpec.leaf_freqs (entry_tree e) @ all_leaf_freqs rest

// count distributes over all_leaf_freqs cons
let all_leaf_freqs_cons (e: forest_entry) (rest: list forest_entry) (x: pos)
  : Lemma (L.count x (all_leaf_freqs (e :: rest)) ==
           L.count x (HSpec.leaf_freqs (entry_tree e)) + L.count x (all_leaf_freqs rest))
  = LP.append_count (HSpec.leaf_freqs (entry_tree e)) (all_leaf_freqs rest) x

// all_leaf_freqs of a single Leaf entry
let all_leaf_freqs_single_leaf (idx: SZ.t) (p: hnode_ptr) (f: pos) (x: pos)
  : Lemma (L.count x (all_leaf_freqs [(idx, p, HSpec.Leaf f)]) ==
           (if x = f then 1 else 0))
  = ()

// Splitting all_leaf_freqs at position j
let rec all_leaf_freqs_remove_at (entries: list forest_entry) (j: nat) (x: pos)
  : Lemma (requires j < L.length entries)
          (ensures L.count x (all_leaf_freqs entries) ==
                   L.count x (HSpec.leaf_freqs (entry_tree (L.index entries j))) +
                   L.count x (all_leaf_freqs (list_remove_at entries j)))
          (decreases j)
  = match entries with
    | e :: rest ->
      all_leaf_freqs_cons e rest x;
      if j = 0 then ()
      else begin
        list_remove_at_length entries j;
        all_leaf_freqs_remove_at rest (j - 1) x;
        all_leaf_freqs_cons e (list_remove_at rest (j - 1)) x
      end

// Splitting all_leaf_freqs removing two positions
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
    assert (HSpec.leaf_freqs merged == HSpec.leaf_freqs t1 @ HSpec.leaf_freqs t2);
    LP.append_count (HSpec.leaf_freqs t1) (HSpec.leaf_freqs t2) x;
    all_leaf_freqs_remove_two entries j1 j2 x

// Prepend Leaf preserves counts with extension
let all_leaf_freqs_prepend_leaf
  (entries: list forest_entry) (idx: SZ.t) (p: hnode_ptr) (f: pos) (x: pos)
  : Lemma (L.count x (all_leaf_freqs ((idx, p, HSpec.Leaf f) :: entries)) ==
           L.count x (all_leaf_freqs entries) + (if x = f then 1 else 0))
  = all_leaf_freqs_cons (idx, p, HSpec.Leaf f) entries x

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
                    L.count x (all_leaf_freqs ((idx, p, HSpec.Leaf f) :: entries)) +
                    L.count x (seq_to_pos_list s (k + 1)) ==
                    L.count x (seq_to_pos_list s 0)))
  = let aux (x: pos)
      : Lemma (L.count x (all_leaf_freqs ((idx, p, HSpec.Leaf f) :: entries)) +
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
                  pure (HSpec.cost ft >= 0 /\
                        HSpec.same_frequency_multiset ft (seq_to_pos_list freq_seq 0)))
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
      pq_freqs_positive pq_contents /\
      pq_idx_unique pq_contents /\
      forest_distinct_indices active /\
      pq_indices_in_forest pq_contents active /\
      (forall (k: nat). k < L.length active ==>
        SZ.v (entry_idx (L.index active k)) < SZ.v vi /\
        Seq.index nd_contents (SZ.v (entry_idx (L.index active k))) == entry_ptr (L.index active k)) /\
      (forall (x: pos). L.count x (all_leaf_freqs active) + L.count x (seq_to_pos_list freq_seq (SZ.v vi)) ==
                         L.count x (seq_to_pos_list freq_seq 0))
    )
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
    valid_pq_entries_extends pq_old pq_new (freq_val, vi) (SZ.v n);
    pq_freqs_positive_extends pq_old pq_new (freq_val, vi);
    
    // Maintain pq_idx_unique: all existing entries have idx < vi, so vi is fresh
    pq_idx_lt_bound pq_old active_old vi;
    pq_idx_unique_extends pq_old pq_new (freq_val, vi);
    
    // Fold is_htree for this leaf and add to forest_own
    fold (is_htree leaf (HSpec.Leaf freq_val));
    forest_own_put_head active_old vi leaf (HSpec.Leaf freq_val);
    
    // Maintain forest_distinct_indices: all existing entries have idx < vi, so vi is fresh
    forest_idx_fresh active_old vi;
    forest_distinct_indices_prepend active_old (vi, leaf, HSpec.Leaf freq_val);
    
    // Maintain pq_indices_in_forest: old PQ entries are in old forest, which is subset of new forest
    // New PQ entry (freq_val, vi) is at position 0 of new forest
    let new_entry : forest_entry = (vi, leaf, HSpec.Leaf freq_val);
    pq_forest_prepend pq_old active_old new_entry;
    find_entry_prepend active_old vi leaf (HSpec.Leaf freq_val);
    pq_forest_extends pq_old pq_new (freq_val, vi) (new_entry :: active_old);
    
    // Maintain node-ptr correspondence through Seq.upd
    node_ptr_correspondence_init_step active_old vi leaf (HSpec.Leaf freq_val) nd_old n;
    
    // Maintain leaf frequency multiset invariant
    all_leaf_freqs_init_step active_old vi leaf freq_val freq_seq (SZ.v vi);
    
    i := vi +^ 1sz;
  };
  
  // Between init and merge: pq_idx_unique and forest_distinct_indices are now in init loop invariant
  with pq_init. assert (PQ.is_pqueue pq pq_init (SZ.v n));
  with active_init. assert (forest_own active_init);
  
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
      pq_freqs_positive pq_contents /\
      pq_idx_unique pq_contents /\
      pq_indices_in_forest pq_contents active /\
      forest_distinct_indices active /\
      (forall (k: nat). k < L.length active ==>
        SZ.v (entry_idx (L.index active k)) < SZ.v n /\
        Seq.index nd_contents (SZ.v (entry_idx (L.index active k))) == entry_ptr (L.index active k)) /\
      (forall (x: pos). L.count x (all_leaf_freqs active) == L.count x (seq_to_pos_list freq_seq 0))
    )
  {
    // Extract two minimums from PQ
    with pq0. assert (PQ.is_pqueue pq pq0 (SZ.v n));
    with active0. assert (forest_own active0);
    let (freq1, idx1) = PQ.extract_min pq;
    with pq1. assert (PQ.is_pqueue pq pq1 (SZ.v n));
    extends_length pq1 pq0 (freq1, idx1);
    valid_pq_entries_shrink pq0 pq1 (freq1, idx1) (SZ.v n);
    pq_freqs_positive_shrink pq0 pq1 (freq1, idx1);
    pq_idx_unique_shrink pq0 pq1 (freq1, idx1);
    pq_forest_shrink pq0 pq1 (freq1, idx1) active0;
    
    let (freq2, idx2) = PQ.extract_min pq;
    with pq2. assert (PQ.is_pqueue pq pq2 (SZ.v n));
    extends_length pq2 pq1 (freq2, idx2);
    valid_pq_entries_shrink pq1 pq2 (freq2, idx2) (SZ.v n);
    pq_freqs_positive_shrink pq1 pq2 (freq2, idx2);
    pq_idx_unique_shrink pq1 pq2 (freq2, idx2);
    pq_no_idx_preserved pq1 pq2 (freq2, idx2) idx1;
    pq_forest_shrink pq1 pq2 (freq2, idx2) active0;
    let sum_freq = freq1 + freq2;
    
    // Read the tree pointers from nodes array
    with nd_contents0. assert (V.pts_to nodes nd_contents0);
    let left_ptr = V.op_Array_Access nodes idx1;
    let right_ptr = V.op_Array_Access nodes idx2;
    
    // Ghost: find positions of idx1 and idx2 in forest and take both trees
    find_entry_by_idx_spec active0 idx1;
    find_entry_by_idx_spec active0 idx2;
    // idx1 <> idx2: pq_idx_unique_shrink pq0 pq1 gives forall j. snd(pq1[j]) <> idx1
    // (freq2, idx2) was in pq1 (from extends), so idx2 <> idx1
    FStar.Seq.Properties.mem_index (freq2, idx2) pq1;
    // k1 <> k2 follows: entry_idx(active0[k1])=idx1 and entry_idx(active0[k2])=idx2, so k1=k2 => idx1=idx2
    forest_own_take_two active0
      (Some?.v (find_entry_by_idx active0 idx1))
      (Some?.v (find_entry_by_idx active0 idx2));
    
    // Rewrite is_htree to use runtime pointers (from loop invariant: nodes[idx] == entry_ptr)
    rewrite (is_htree (entry_ptr (L.index active0 (Some?.v (find_entry_by_idx active0 idx1))))
                      (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx1)))))
         as (is_htree left_ptr
                      (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx1)))));
    rewrite (is_htree (entry_ptr (L.index active0 (Some?.v (find_entry_by_idx active0 idx2))))
                      (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx2)))))
         as (is_htree right_ptr
                      (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx2)))));
    
    // Create merged internal node (freq1 > 0, freq2 > 0 from pq_freqs_positive_shrink)
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
    valid_pq_entries_extends pq2 pq3 (sum_freq, idx1) (SZ.v n);
    pq_freqs_positive_extends pq2 pq3 (sum_freq, idx1);
    pq_idx_unique_extends pq2 pq3 (sum_freq, idx1);
    
    // Ghost: put merged entry into new forest
    forest_own_put_head
      (list_remove_two active0
        (Some?.v (find_entry_by_idx active0 idx1))
        (Some?.v (find_entry_by_idx active0 idx2)))
      idx1 merged
      (HSpec.Internal (sum_freq <: pos)
        (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx1))))
        (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx2)))));
    
    // Maintain remaining invariants
    list_remove_two_length active0
      (Some?.v (find_entry_by_idx active0 idx1))
      (Some?.v (find_entry_by_idx active0 idx2));
    
    // pq_indices_in_forest: Use pq_forest_remove_two (pq2 entries have idx <> idx1 and <> idx2)
    // then prepend (idx1, merged, ...) and use pq_forest_extends
    pq_forest_remove_two pq2 active0
      (Some?.v (find_entry_by_idx active0 idx1))
      (Some?.v (find_entry_by_idx active0 idx2));
    pq_forest_prepend pq2
      (list_remove_two active0
        (Some?.v (find_entry_by_idx active0 idx1))
        (Some?.v (find_entry_by_idx active0 idx2)))
      (idx1, merged,
        HSpec.Internal (sum_freq <: pos)
          (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx1))))
          (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx2)))));
    find_entry_prepend
      (list_remove_two active0
        (Some?.v (find_entry_by_idx active0 idx1))
        (Some?.v (find_entry_by_idx active0 idx2)))
      idx1 merged
      (HSpec.Internal (sum_freq <: pos)
        (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx1))))
        (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx2)))));
    pq_forest_extends pq2 pq3 (sum_freq, idx1)
      ((idx1, merged,
        HSpec.Internal (sum_freq <: pos)
          (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx1))))
          (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx2)))))
       :: list_remove_two active0
            (Some?.v (find_entry_by_idx active0 idx1))
            (Some?.v (find_entry_by_idx active0 idx2)));
    
    // Node-pointer correspondence and forest_distinct_indices for new_active
    forest_distinct_indices_after_merge active0
      (Some?.v (find_entry_by_idx active0 idx1))
      (Some?.v (find_entry_by_idx active0 idx2))
      idx1 merged
      (HSpec.Internal (sum_freq <: pos)
        (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx1))))
        (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx2)))));
    node_ptr_correspondence_upd active0
      (Some?.v (find_entry_by_idx active0 idx1))
      (Some?.v (find_entry_by_idx active0 idx2))
      idx1 merged
      (HSpec.Internal (sum_freq <: pos)
        (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx1))))
        (entry_tree (L.index active0 (Some?.v (find_entry_by_idx active0 idx2)))))
      nd_contents0 n;
    
    // Maintain leaf frequency multiset through merge
    all_leaf_freqs_merge_step_full active0
      (Some?.v (find_entry_by_idx active0 idx1))
      (Some?.v (find_entry_by_idx active0 idx2))
      idx1 merged (sum_freq <: pos)
      (seq_to_pos_list freq_seq 0);
    
    let viter = !iter;
    iter := viter +^ 1sz;
  };
  
  // Extract final result from PQ
  with pq_final. assert (PQ.is_pqueue pq pq_final (SZ.v n));
  with active_final. assert (forest_own active_final);
  
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
  
  // Clean up
  PQ.free pq;
  Box.free dummy;
  V.free nodes;
  
  result
}
#pop-options
