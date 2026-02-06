module CLRS.Ch10.LinkedList
#lang-pulse
open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module B = Pulse.Lib.Box
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot
open Pulse.Lib.Vec

// Lemma: empty list correspondence
let lemma_empty_list_inv (#t:eqtype) (arr_seq: Seq.seq t) (cap: nat)
  : Lemma (requires Seq.length arr_seq == cap)
          (ensures forall (i:nat). i < 0 ==> Seq.index arr_seq i == L.index ([] #t) i)
  = ()

// Lemma: appending element preserves correspondence  
let rec lemma_index_append (#t:eqtype) (contents: list t) (x: t) (i: nat)
  : Lemma
    (requires i < L.length contents + 1)
    (ensures (
      L.append_length contents [x];
      L.index (L.append contents [x]) i == 
             (if i < L.length contents then L.index contents i else x)))
    (decreases i)
  = L.append_length contents [x];
    match contents with
    | [] -> ()
    | hd :: tl -> if i = 0 then () else lemma_index_append tl x (i - 1)

let lemma_append_single (#t:eqtype) (contents: list t) (x: t) (arr_seq: Seq.seq t) (new_arr: Seq.seq t)
  : Lemma
    (requires 
      L.length contents < Seq.length arr_seq /\
      Seq.length new_arr == Seq.length arr_seq /\
      (forall (i:nat). i < L.length contents ==> Seq.index arr_seq i == L.index contents i) /\
      new_arr == Seq.upd arr_seq (L.length contents) x)
    (ensures (
      L.append_length contents [x];
      forall (i:nat). i < L.length contents + 1 ==> 
        Seq.index new_arr i == L.index (L.append contents [x]) i))
  = L.append_length contents [x];
    let prove_for_i (i: nat{i < L.length contents + 1}) : Lemma 
      (ensures (L.append_length contents [x]; Seq.index new_arr i == L.index (L.append contents [x]) i)) =
      lemma_index_append contents x i
    in
    FStar.Classical.forall_intro prove_for_i

// Lemma: if key not at any index, it's not in list
let rec lemma_not_in_list (#t:eqtype) (lst: list t) (key: t) (arr_seq: Seq.seq t)
  : Lemma
    (requires 
      L.length lst <= Seq.length arr_seq /\
      (forall (i:nat). i < L.length lst ==> Seq.index arr_seq i == L.index lst i) /\
      (forall (i:nat). i < L.length lst ==> Seq.index arr_seq i =!= key))
    (ensures ~(L.mem key lst))
    (decreases L.length lst)
  = match lst with
    | [] -> ()
    | hd :: tl ->
      assert (Seq.index arr_seq 0 == hd);
      assert (hd =!= key);
      if L.length tl > 0 then
        lemma_not_in_list tl key (Seq.slice arr_seq 1 (Seq.length arr_seq))
      else ()

fn create_list (t:eqtype) (default_val: t) (capacity: SZ.t)
  requires emp ** pure (SZ.v capacity > 0)
  returns lst: linked_list t
  ensures list_inv lst (hide []) ** 
          pure (reveal lst.capacity == SZ.v capacity)
{
  let arr = V.alloc default_val capacity;
  with arr_seq. assert (V.pts_to arr arr_seq);
  let size_ref = B.alloc 0sz;
  
  let lst : linked_list t = {
    data = arr;
    size = size_ref;
    capacity = hide (SZ.v capacity);
  };
  
  rewrite (V.pts_to arr arr_seq) as (V.pts_to lst.data arr_seq);
  rewrite (B.pts_to size_ref 0sz) as (B.pts_to lst.size 0sz);
  
  lemma_empty_list_inv #t arr_seq (SZ.v capacity);
  fold (list_inv lst (hide []));
  lst
}

fn list_search (#t:eqtype) (lst: linked_list t) (#contents: erased (list t)) (key: t)
  requires list_inv lst contents
  returns result: option SZ.t
  ensures list_inv lst contents **
          pure (
            match result with
            | None -> ~(L.mem key (reveal contents))
            | Some idx -> 
                SZ.v idx < L.length (reveal contents) /\
                L.index (reveal contents) (SZ.v idx) == key
          )
{
  unfold (list_inv lst contents);
  with arr_seq size_v. _;
  
  let size_val = B.(!lst.size);
  let mut i : SZ.t = 0sz;
  let mut found = false;
  let mut result_idx : SZ.t = 0sz;
  
  while (
    let vi = !i;
    let vf = !found;
    SZ.lt vi size_val && not vf
  )
  invariant exists* vi vf vr.
    R.pts_to i vi **
    R.pts_to found vf **
    R.pts_to result_idx vr **
    V.pts_to lst.data arr_seq **
    B.pts_to lst.size size_val **
    pure (
      SZ.v vi <= SZ.v size_val /\
      SZ.v size_val == L.length (reveal contents) /\
      (vf ==> (SZ.v vr < L.length (reveal contents) /\ L.index (reveal contents) (SZ.v vr) == key)) /\
      (~vf ==> (forall (j:nat). j < SZ.v vi ==> Seq.index arr_seq j =!= key))
    )
  {
    let vi = !i;
    let elem = lst.data.(vi);
    
    if (elem = key) {
      result_idx := vi;
      found := true;
    } else {
      i := SZ.add vi 1sz;
    };
  };
  
  let vf = !found;
  let vr = !result_idx;
  
  fold (list_inv lst contents);
  
  if vf {
    Some vr
  } else {
    // Prove key not in list
    lemma_not_in_list (reveal contents) key arr_seq;
    None #SZ.t
  }
}

fn list_insert (#t:eqtype) (lst: linked_list t) (#contents: erased (list t)) (x: t)
  requires list_inv lst contents **
           pure (L.length (reveal contents) < reveal lst.capacity /\
                 SZ.fits (L.length (reveal contents) + 1))
  returns unit
  ensures list_inv lst (hide (L.append (reveal contents) [x]))
{
  unfold (list_inv lst contents);
  with arr_seq size_v. _;
  
  let size_val = B.(!lst.size);
  
  // Write element at end
  lst.data.(size_val) <- x;
  with new_arr. assert (V.pts_to lst.data new_arr);
  
  // Update size
  let new_size = SZ.add size_val 1sz;
  with _old_size. assert (B.pts_to lst.size _old_size);
  B.op_Colon_Equals lst.size new_size;
  
  // Prove new invariant
  lemma_append_single (reveal contents) x arr_seq new_arr;
  L.append_length (reveal contents) [x];
  
  fold (list_inv lst (hide (L.append (reveal contents) [x])))
}
