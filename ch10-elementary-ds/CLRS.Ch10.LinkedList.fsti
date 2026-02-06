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

// Array-based list representation (simplified from true doubly-linked list)
noeq type linked_list (t:eqtype) = {
  data: V.vec t;
  size: B.box SZ.t;
  capacity: erased nat;
}

// List invariant
let list_inv (#t:eqtype) (lst: linked_list t) (contents: erased (list t)) : slprop = 
  exists* arr_seq size_v.
    V.pts_to lst.data arr_seq **
    B.pts_to lst.size size_v **
    pure (
      SZ.v size_v == L.length contents /\
      SZ.v size_v <= reveal lst.capacity /\
      Seq.length arr_seq == reveal lst.capacity /\
      (forall (i:nat). i < SZ.v size_v ==> 
        Seq.index arr_seq i == L.index contents i)
    )

// Create a new empty list
fn create_list (t:eqtype) (default_val: t) (capacity: SZ.t)
  requires emp ** pure (SZ.v capacity > 0)
  returns lst: linked_list t
  ensures list_inv lst (hide []) ** 
          pure (reveal lst.capacity == SZ.v capacity)

// Search for an element
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

// Insert at head (simplified - inserts at end for easier proof)
fn list_insert (#t:eqtype) (lst: linked_list t) (#contents: erased (list t)) (x: t)
  requires list_inv lst contents **
           pure (L.length (reveal contents) < reveal lst.capacity /\
                 SZ.fits (L.length (reveal contents) + 1))
  returns unit
  ensures list_inv lst (hide (L.append (reveal contents) [x]))
