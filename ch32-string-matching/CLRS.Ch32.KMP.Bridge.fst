(*
   KMP Bridge: Connecting Pulse pi_correct to Spec pi_max

   The Pulse implementation (CLRS.Ch32.KMP) proves [pi_correct]:
     pi[q] is a valid prefix-suffix at each position.

   The completeness specification (CLRS.Ch32.KMP.Spec) requires [pi_max]:
     pi[q] is the LONGEST prefix-suffix at each position.

   This module bridges the gap via [pi_optimal_extension], the key
   algorithmic invariant from the CLRS prefix function computation.

   Proof chain:
     pi_correct /\ pi_optimal_extension ==> pi_max_sz ==> Spec.pi_max

   The [pi_optimal_extension] property captures the invariant that would
   need to be added to the Pulse compute_prefix_function loop invariant
   for a complete end-to-end verified chain. It says: for each q > 0,
   if k is a prefix-suffix of pattern[0..q-2] and pattern[k] == pattern[q],
   then k+1 <= pi[q]. This holds because the inner while loop iterates
   through the failure chain from pi[q-1] and picks the longest extending match.

   NO admits. NO assumes.
*)
module CLRS.Ch32.KMP.Bridge

open FStar.Seq
open CLRS.Ch32.KMP

module SZ = FStar.SizeT
module Spec = CLRS.Ch32.KMP.Spec

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

// ========== Definitions ==========

/// [pi_max_sz]: pi[q] is the LONGEST prefix-suffix at each position.
/// Uses [seq SZ.t] for the pi array, matching the Pulse output type.
let pi_max_sz (#a: eqtype) (pattern: seq a) (pi: seq SZ.t) : prop =
  length pi == length pattern /\
  length pattern > 0 /\
  (forall (q: nat). q < length pattern ==>
    is_prefix_suffix pattern q (SZ.v (index pi q))) /\
  (forall (q: nat). q < length pattern ==>
    (forall (k: nat). is_prefix_suffix pattern q k ==> k <= SZ.v (index pi q)))

/// [pi_optimal_extension]: The algorithmic invariant from COMPUTE-PREFIX-FUNCTION.
///
/// For q > 0: if k is a prefix-suffix of pattern[0..q-2] and pattern[k]
/// matches pattern[q], then k+1 <= pi[q]. This captures the fact that
/// the inner while loop iterates through the failure chain from pi[q-1]
/// and picks the longest extending match.
let pi_optimal_extension (#a: eqtype) (pattern: seq a) (pi: seq SZ.t) : prop =
  length pi == length pattern /\
  length pattern > 0 /\
  (forall (q: nat). 0 < q /\ q < length pattern ==>
    (forall (k: nat). k < length pattern /\
      is_prefix_suffix pattern (q - 1) k /\
      index pattern k == index pattern q ==>
      k + 1 <= SZ.v (index pi q)))

// ========== Core Proof ==========

/// Decomposition: a nonzero prefix-suffix of pattern[0..q] (q > 0) decomposes
/// into a prefix-suffix of pattern[0..q-1] plus a character match at position q.
///
///   If pattern[0..k-1] = pattern[q-k+1..q] with k > 0, q > 0, then:
///     (a) pattern[0..k-2] = pattern[q-k+1..q-1]  (k-1 is PS of q-1)
///     (b) pattern[k-1] = pattern[q]                (extending character)
let ps_decompose (#a: eqtype) (pattern: seq a)
    (q: nat{q < length pattern /\ q > 0}) (k: nat)
  : Lemma (requires is_prefix_suffix pattern q k /\ k > 0)
          (ensures is_prefix_suffix pattern (q - 1) (k - 1) /\
                   index pattern (k - 1) == index pattern q)
  = // Key arithmetic identity: the index offsets align
    assert ((q - 1) - (k - 1) + 1 == q - k + 1)

/// Maximality at a single position: any prefix-suffix k of pattern[0..q]
/// satisfies k <= pi[q], assuming pi_correct and pi_optimal_extension.
///
/// Proof:
///   - k = 0: trivial (SZ.v >= 0)
///   - q = 0: k <= q = 0 contradicts k > 0
///   - q > 0, k > 0: by ps_decompose, k-1 is PS of q-1 and pattern[k-1] = pattern[q];
///     by pi_optimal_extension, (k-1)+1 = k <= pi[q]
let maximality_at (#a: eqtype) (pattern: seq a) (pi: seq SZ.t)
    (q: nat{q < length pattern}) (k: nat)
  : Lemma
    (requires pi_correct pattern pi /\
             pi_optimal_extension pattern pi /\
             is_prefix_suffix pattern q k)
    (ensures k <= SZ.v (index pi q))
  = if k = 0 then ()
    else if q = 0 then ()
    else ps_decompose pattern q k

/// Main bridge theorem:
///   pi_correct (from Pulse) + pi_optimal_extension (algorithmic invariant)
///   ==> pi_max_sz (maximality needed by Spec).
let pi_correct_implies_pi_max_sz (#a: eqtype) (pattern: seq a) (pi: seq SZ.t)
  : Lemma
    (requires pi_correct pattern pi /\ pi_optimal_extension pattern pi)
    (ensures pi_max_sz pattern pi)
  = let aux (q: (q:nat{q < length pattern}))
      : Lemma (forall (k: nat). is_prefix_suffix pattern q k ==> k <= SZ.v (index pi q))
      = let inner (k: nat)
          : Lemma (requires is_prefix_suffix pattern q k)
                  (ensures k <= SZ.v (index pi q))
          = maximality_at pattern pi q k
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires inner)
    in
    FStar.Classical.forall_intro aux

// ========== Conversion to int sequences ==========

/// Convert a [seq SZ.t] to [seq int] by applying [SZ.v] pointwise.
let sz_seq_to_int (pi: seq SZ.t) : seq int =
  init #int (length pi) (fun i -> SZ.v (index pi i))

/// Indexing the converted sequence yields the same as SZ.v on the original.
let sz_seq_to_int_index (pi: seq SZ.t) (i: nat{i < length pi})
  : Lemma (index (sz_seq_to_int pi) i == SZ.v (index pi i))
  = ()

/// Convert [pi_max_sz] (SZ.t) to Spec's [pi_max] (int).
/// Specialized to int patterns, matching CLRS.Ch32.KMP.Spec.
let pi_max_sz_to_spec_pi_max (pattern: seq int) (pi_sz: seq SZ.t)
  : Lemma
    (requires pi_max_sz #int pattern pi_sz)
    (ensures Spec.pi_max pattern (sz_seq_to_int pi_sz))
  = let pi_int = sz_seq_to_int pi_sz in
    let aux_nonneg (q: (q:nat{q < length pattern}))
      : Lemma (index pi_int q >= 0)
      = sz_seq_to_int_index pi_sz q
    in
    let aux_valid (q: (q:nat{q < length pattern}))
      : Lemma (is_prefix_suffix #int pattern q (index pi_int q))
      = sz_seq_to_int_index pi_sz q
    in
    let aux_max (q: (q:nat{q < length pattern}))
      : Lemma (forall (k: nat).
                is_prefix_suffix #int pattern q k ==> k <= index pi_int q)
      = sz_seq_to_int_index pi_sz q
    in
    FStar.Classical.forall_intro aux_nonneg;
    FStar.Classical.forall_intro aux_valid;
    FStar.Classical.forall_intro aux_max

/// End-to-end bridge:
///   pi_correct /\ pi_optimal_extension ==> Spec.pi_max
let bridge (pattern: seq int) (pi_sz: seq SZ.t)
  : Lemma
    (requires pi_correct #int pattern pi_sz /\ pi_optimal_extension #int pattern pi_sz)
    (ensures Spec.pi_max pattern (sz_seq_to_int pi_sz))
  = pi_correct_implies_pi_max_sz #int pattern pi_sz;
    pi_max_sz_to_spec_pi_max pattern pi_sz
