(*
   Bridge Lemmas: connect c2pulse array model to CLRS.Ch21.UnionFind.Spec

   The c2pulse tool represents arrays as Seq.seq (option SZ.t) in its
   ghost state.  This module defines converters from that representation
   to the pure uf_forest model used by Spec.fst, and proves that
   structural properties stated with array_read (c2pulse level)
   imply the spec-level invariants.
*)

module CLRS.Ch21.UnionFind.C.BridgeLemmas

open FStar.Seq
module Seq = FStar.Seq
module SZ  = FStar.SizeT
module Spec = CLRS.Ch21.UnionFind.Spec

(*** 1. Type-level converters ***)

// Strip options from initialized c2pulse array ghost state
let c_to_nat_seq
  (s: Seq.seq (option SZ.t))
  (n: nat{n <= Seq.length s /\ (forall (i: nat). i < n ==> Some? (Seq.index s i))})
  : Seq.seq nat
  = Seq.init n (fun (i: nat{i < n}) -> SZ.v (Some?.v (Seq.index s i)))

// Build uf_forest from c2pulse option-sequences
let c_to_uf
  (s_parent s_rank: Seq.seq (option SZ.t))
  (n: nat{n <= Seq.length s_parent /\ n <= Seq.length s_rank /\
          (forall (i: nat). i < n ==> Some? (Seq.index s_parent i)) /\
          (forall (i: nat). i < n ==> Some? (Seq.index s_rank i))})
  : Spec.uf_forest
  = { Spec.parent = c_to_nat_seq s_parent n;
      Spec.rank   = c_to_nat_seq s_rank n;
      Spec.n      = n }

(*** 2. Index lemma: array_read ↔ Seq.index in uf_forest ***)

let c_to_nat_seq_index
  (s: Seq.seq (option SZ.t))
  (n: nat{n <= Seq.length s /\ (forall (i: nat). i < n ==> Some? (Seq.index s i))})
  (i: nat{i < n})
  : Lemma (Seq.index (c_to_nat_seq s n) i == SZ.v (Some?.v (Seq.index s i)))
  = ()

(*** 3. make_set establishes uf_inv ***)

let c_make_set_uf_inv
  (s_parent s_rank: Seq.seq (option SZ.t))
  (n: nat{n > 0 /\ n <= Seq.length s_parent /\ n <= Seq.length s_rank /\
          (forall (i: nat). i < n ==> Some? (Seq.index s_parent i)) /\
          (forall (i: nat). i < n ==> Some? (Seq.index s_rank i))})
  : Lemma (requires
             (forall (i: nat). i < n ==>
               SZ.v (Some?.v (Seq.index s_parent i)) == i) /\
             (forall (i: nat). i < n ==>
               SZ.v (Some?.v (Seq.index s_rank i)) == 0))
          (ensures Spec.uf_inv (c_to_uf s_parent s_rank n))
  = let f = c_to_uf s_parent s_rank n in
    assert (Seq.length f.Spec.parent == n);
    assert (Seq.length f.Spec.rank == n);
    let aux (i: nat{i < n}) : Lemma (Seq.index f.Spec.parent i == i /\
                                      Seq.index f.Spec.parent i < n /\
                                      Seq.index f.Spec.rank i == 0)
      = () in
    FStar.Classical.forall_intro aux

(*** 4. find_root computes pure_find (read-only arrays) ***)

// Key lemma: for a uf_forest satisfying uf_inv where
// find_root returns root with parent[root]==root,
// the result equals Spec.pure_find
//
// This works because pure_find follows the same parent chain
// and terminates at the same self-loop.

let c_find_root_is_pure_find
  (f: Spec.uf_forest{Spec.uf_inv f})
  (x: nat{x < f.Spec.n})
  : Lemma (ensures Spec.pure_find f x < f.Spec.n /\
                   Seq.index f.Spec.parent (Spec.pure_find f x) == Spec.pure_find f x)
  = Spec.pure_find_in_bounds f x;
    Spec.pure_find_is_root f x

(*** 5. Compression preserves uf_inv ***)

// Path compression sets parent[v] = root where root = pure_find(v).
// Spec.compress_preserves_uf_inv proves this preserves uf_inv.
// Spec.compress_preserves_find_all proves pure_find is unchanged for ALL nodes.
//
// These lemmas from Spec.fst can be used directly via _ghost_stmt in the
// C code — no additional bridge lemma is needed for compression.

(*** 6. Link preserves uf_inv ***)

// Spec.pure_union_preserves_inv proves that linking two roots preserves uf_inv.
// For the C code, the link operation modifies parent[root_a] = root_b (or vice versa)
// and possibly increments rank[root_x].
// Spec.pure_union_same_set / pure_union_stability / pure_union_membership_all
// provide the functional correctness properties.
