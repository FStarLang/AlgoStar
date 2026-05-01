(*
   CLRS Chapter 23: Prim's Algorithm — Shared Definitions
   
   Pure definitions shared between Prim.Impl, Prim.KeyInv, etc.
   No Pulse dependency.
*)
module CLRS.Ch23.Prim.Defs

open FStar.SizeT
module SZ = FStar.SizeT
module Seq = FStar.Seq

open CLRS.Ch23.MST.Spec

/// Implementation infinity constant
let infinity : SZ.t = 65535sz

/// All real edge weights must be strictly less than infinity
let valid_weights (weights_seq: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length weights_seq == n * n /\
  (forall (i: nat). i < n * n ==>
    SZ.v (Seq.index weights_seq i) = 0 \/
    (SZ.v (Seq.index weights_seq i) > 0 /\ SZ.v (Seq.index weights_seq i) < SZ.v infinity))

/// All keys bounded by infinity
let all_keys_bounded (s: Seq.seq SZ.t) : prop =
  forall (i:nat). i < Seq.length s ==> SZ.v (Seq.index s i) <= SZ.v infinity

/// All parent values are valid vertex indices
let parent_valid (parent_seq: Seq.seq SZ.t) (n: nat) : prop =
  forall (v:nat). v < Seq.length parent_seq ==> SZ.v (Seq.index parent_seq v) < n

/// Symmetric weight matrix (undirected graph)
let symmetric_weights (weights_seq: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length weights_seq == n * n /\
  (forall (u v: nat). u < n /\ v < n ==>
    SZ.v (Seq.index weights_seq (u * n + v)) = SZ.v (Seq.index weights_seq (v * n + u)))

/// No zero-weight off-diagonal entries
let no_zero_edges (weights_seq: Seq.seq SZ.t) (n: nat) : prop =
  Seq.length weights_seq == n * n /\
  (forall (u v: nat). u < n /\ v < n /\ u * n + v < n * n /\
    SZ.v (Seq.index weights_seq (u * n + v)) = 0 ==> u = v)

/// For non-source vertices with finite key, key equals the edge weight to the parent.
let key_parent_consistent
    (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat) : prop =
  forall (v:nat). (v < n /\ v <> source /\
    v < Seq.length key_seq /\
    v < Seq.length parent_seq /\
    SZ.v (Seq.index key_seq v) < SZ.v infinity /\
    SZ.v (Seq.index parent_seq v) < n /\
    SZ.v (Seq.index parent_seq v) * n + v < Seq.length weights_seq) ==>
    SZ.v (Seq.index key_seq v) == SZ.v (Seq.index weights_seq (SZ.v (Seq.index parent_seq v) * n + v))

/// Predicate for correctness of Prim's output
let prim_correct 
    (key_seq parent_seq weights_seq: Seq.seq SZ.t) (n source: nat) : prop 
  = Seq.length key_seq == n /\
    Seq.length parent_seq == n /\
    source < n /\
    Seq.length weights_seq == n * n /\
    SZ.v (Seq.index key_seq source) == 0 /\
    all_keys_bounded key_seq /\
    SZ.v (Seq.index parent_seq source) == source /\
    parent_valid parent_seq n /\
    key_parent_consistent key_seq parent_seq weights_seq n source
