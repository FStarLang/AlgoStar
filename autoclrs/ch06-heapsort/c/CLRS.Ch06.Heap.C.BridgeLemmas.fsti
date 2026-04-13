(*
   Heapsort Bridge Lemmas — connecting c2pulse postconditions to F* specs.

   The c2pulse translation proves heap properties using quantified
   comparisons on Int32.t values in Seq.seq (option Int32.t). The
   hand-written F* specs (CLRS.Ch06.Heap.Spec/Lemmas) work over
   Seq.seq int.

   This module bridges the gap:
     1. extract_ints: lifts option Int32.t sequences to int sequences
     2. root_ge_element_bridge: root dominates all elements (inductive,
        can't be derived by SMT from heap_down_at alone)

   Quantifiers over SizeT.t match c2pulse invariants exactly.

   NO admits.
*)
module CLRS.Ch06.Heap.C.BridgeLemmas

open CLRS.Ch06.Heap.Spec
module Seq  = FStar.Seq
module SeqP = FStar.Seq.Properties
module I32  = FStar.Int32
module SZ   = FStar.SizeT

/// Predicate: every element in the prefix is Some
let all_some (s: Seq.seq (option I32.t)) (n: nat) : prop =
  n <= Seq.length s /\
  (forall (i: nat). i < n ==> Some? (Seq.index s i))

/// Extract int values from an initialized option Int32.t sequence
val extract_ints (s: Seq.seq (option I32.t)) (n: nat{all_some s n})
  : Tot (r: Seq.seq int{Seq.length r == n /\
    (forall (i: nat). i < n ==> Seq.index r i == I32.v (Some?.v (Seq.index s i)))})

/// Permutation over option Int32.t sequences (c2pulse representation).

val option_perm_refl (s: Seq.seq (option I32.t))
  : Lemma (SeqP.permutation (option I32.t) s s)

val option_perm_trans (s1 s2 s3: Seq.seq (option I32.t))
  : Lemma
    (requires SeqP.permutation (option I32.t) s1 s2 /\
              SeqP.permutation (option I32.t) s2 s3)
    (ensures SeqP.permutation (option I32.t) s1 s3)

/// After a c2pulse swap (two array_writes), the result equals SeqP.swap.
val swap_option_seq_eq (s: Seq.seq (option I32.t))
  (i j: nat{i < Seq.length s /\ j < Seq.length s /\ i <> j})
  : Lemma
    (Seq.equal
      (Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i))
      (SeqP.swap s i j))

/// Swapping two elements preserves permutation.
val swap_option_perm (s: Seq.seq (option I32.t))
  (i j: nat{i < Seq.length s /\ j < Seq.length s})
  : Lemma (SeqP.permutation (option I32.t) s
    (Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i)))

/// Root of a max-heap dominates all elements.
/// This is an inductive fact (root_ge_element) that SMT cannot derive
/// from individual heap_down_at facts alone.
///
/// Preconditions use SizeT.t quantifiers to match c2pulse invariants.
/// The all_some/initialized condition uses nat (matching array_initialized
/// from Pulse.Lib.C.Array, which is included in array_pts_to).
val root_ge_element_bridge
  (va: Seq.seq (option I32.t)) (n: SZ.t)
  : Lemma
    (requires
      SZ.v n > 0 /\ SZ.v n <= Seq.length va /\
      (forall (i: nat). i < Seq.length va ==> Some? (Seq.index va i)) /\
      (forall (k: SZ.t). SZ.v k < SZ.v n ==>
        (op_Multiply 2 (SZ.v k) + 1 >= SZ.v n \/
          I32.v (Some?.v (Seq.index va (op_Multiply 2 (SZ.v k) + 1))) <=
          I32.v (Some?.v (Seq.index va (SZ.v k)))) /\
        (op_Multiply 2 (SZ.v k) + 2 >= SZ.v n \/
          I32.v (Some?.v (Seq.index va (op_Multiply 2 (SZ.v k) + 2))) <=
          I32.v (Some?.v (Seq.index va (SZ.v k))))))
    (ensures
      forall (k: SZ.t). SZ.v k < SZ.v n ==>
        I32.v (Some?.v (Seq.index va (SZ.v k))) <=
        I32.v (Some?.v (Seq.index va 0)))
