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
open CLRS.Ch32.KMP.PureDefs

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

// ========== Incremental proof helpers for Pulse compute_prefix_function ==========

/// Partial maximality: pi is maximal at positions 0..bound-1
let pi_max_sz_up_to (#a: eqtype) (pattern: seq a) (pi: seq SZ.t) (bound: nat) : prop =
  bound <= length pattern /\
  length pi >= length pattern /\
  length pattern > 0 /\
  (forall (q: nat). q < bound ==>
    is_prefix_suffix pattern q (SZ.v (index pi q))) /\
  (forall (q: nat) (k: nat). q < bound /\ is_prefix_suffix pattern q k ==> k <= SZ.v (index pi q))

/// Inner loop invariant: all PS values above current k have been checked
/// and found to mismatch pattern[q].
let all_ps_above_mismatch (#a: eqtype) (pattern: seq a)
    (q: nat{q > 0 /\ q < length pattern}) (k_cur: nat) : prop =
  forall (j: nat). j > k_cur /\ is_prefix_suffix pattern (q - 1) j /\ j < length pattern ==>
    index pattern j <> index pattern q

/// Base case: pi[0] = 0 is trivially maximal (only PS of position 0 is k=0)
let maximality_base (#a: eqtype) (pattern: seq a) (pi: seq SZ.t)
  : Lemma
    (requires length pattern > 0 /\ length pi >= length pattern /\
             SZ.v (index pi 0) == 0 /\
             is_prefix_suffix pattern 0 (SZ.v (index pi 0)))
    (ensures pi_max_sz_up_to pattern pi 1)
  = ()

/// Inner loop init: when k = pi[q-1] and pi_max_sz_up_to(q), the mismatch
/// invariant holds vacuously (no PS > pi[q-1] exists by maximality).
let inner_maximality_init (#a: eqtype) (pattern: seq a) (pi: seq SZ.t)
    (q: nat{0 < q /\ q < length pattern}) (k_init: nat)
  : Lemma
    (requires pi_max_sz_up_to pattern pi q /\
             k_init == SZ.v (index pi (q - 1)))
    (ensures all_ps_above_mismatch pattern q k_init)
  = ()

/// Generic ps_nesting: if both j and k are PS of pattern[0..q], and j < k,
/// then j is also a PS of pattern[0..k-1].
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let ps_nesting_gen (#a: eqtype) (pattern: seq a)
    (q: nat{q < length pattern}) (k j: nat)
  : Lemma
    (requires is_prefix_suffix pattern q k /\
             is_prefix_suffix pattern q j /\
             j < k)
    (ensures k > 0 /\ k - 1 < length pattern /\
            is_prefix_suffix pattern (k - 1) j)
  = assert (k > 0 /\ k - 1 < length pattern);
    let aux (i: nat{i < j})
      : Lemma (index pattern i == index pattern (k - j + i)) =
      assert (k - j + i < k);
      assert (q - k + 1 + (k - j + i) == q - j + 1 + i)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// Inner loop step: when k > 0, pattern[k] != pattern[q], and k' = pi[k-1],
/// the mismatch invariant extends from k to k'.
/// Uses ps_nesting_gen: any PS j of pattern[0..q-1] with k' < j < k
/// is also a PS of pattern[0..k-1], hence j <= pi[k-1] = k', contradiction.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let inner_maximality_step (#a: eqtype) (pattern: seq a) (pi: seq SZ.t)
    (q: nat{0 < q /\ q < length pattern}) (k: nat) (k_new: nat)
  : Lemma
    (requires pi_max_sz_up_to pattern pi q /\
             k > 0 /\ k <= q - 1 /\ k < length pattern /\
             is_prefix_suffix pattern (q - 1) k /\
             index pattern k <> index pattern q /\
             all_ps_above_mismatch pattern q k /\
             k_new == SZ.v (index pi (k - 1)) /\
             is_prefix_suffix pattern (k - 1) k_new)
    (ensures all_ps_above_mismatch pattern q k_new)
  = let aux (j: nat{j > k_new /\ is_prefix_suffix pattern (q - 1) j /\ j < length pattern})
      : Lemma (index pattern j <> index pattern q)
      = if j > k then ()
        else if j = k then ()
        else begin
          // k_new < j < k, both j and k are PS of pattern[0..q-1]
          ps_nesting_gen pattern (q - 1) k j;
          // j is PS of pattern[0..k-1], and pi_max_up_to covers k-1 < q
          assert (k - 1 < q);
          assert (is_prefix_suffix pattern (k - 1) j);
          assert (j <= SZ.v (index pi (k - 1)))
        end
    in
    FStar.Classical.forall_intro aux
#pop-options

/// Helper: instantiate all_ps_above_mismatch at a specific j
let apply_mismatch (#a: eqtype) (pattern: seq a)
    (q: nat{q > 0 /\ q < length pattern}) (k_cur: nat) (j: nat)
  : Lemma
    (requires all_ps_above_mismatch pattern q k_cur /\
             j > k_cur /\ is_prefix_suffix pattern (q - 1) j /\ j < length pattern)
    (ensures index pattern j <> index pattern q)
  = ()

/// maximality_at_q: proves any PS j of pattern[0..q] satisfies j <= pi_q.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let maximality_at_q (#a: eqtype) (pattern: seq a) (pi_new: seq SZ.t)
    (q: nat{0 < q /\ q < length pattern /\ q < length pi_new})
    (k_final: nat) (chars_match: bool) (j: nat)
  : Lemma
    (requires is_prefix_suffix pattern (q - 1) k_final /\
             k_final < length pattern /\
             all_ps_above_mismatch pattern q k_final /\
             (chars_match ==> index pattern k_final == index pattern q) /\
             (not chars_match ==> (k_final == 0 /\ index pattern k_final <> index pattern q)) /\
             SZ.v (index pi_new q) == (if chars_match then k_final + 1 else k_final) /\
             is_prefix_suffix pattern q j)
    (ensures j <= SZ.v (index pi_new q))
  = if j = 0 then ()
    else begin
      ps_decompose pattern q j;
      let jm1 = j - 1 in
      if jm1 > k_final then begin
        apply_mismatch pattern q k_final jm1;
        assert False
      end else begin
        if chars_match then
          assert (j <= k_final + 1)
        else begin
          assert (jm1 == 0);
          assert (index pattern 0 <> index pattern q);
          assert (index pattern jm1 == index pattern q);
          assert False
        end
      end
    end
#pop-options

/// After inner loop + extend: maximality extends from positions 0..q-1 to 0..q.
/// Preconditions are FLAT (no pi_max_sz_up_to) so Z3 doesn't get stuck
/// in quantifier loops from nested foralls in the definition.
/// Callers should unfold pi_max_sz_up_to before calling.

/// Fold explicit flat conjuncts into pi_max_sz_up_to.
/// Z3 can match the precondition components to the definition directly.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let fold_pi_max_up_to (#a: eqtype) (pattern: seq a) (pi: seq SZ.t) (bound: nat)
  : Lemma
    (requires bound <= length pattern /\
             length pi >= length pattern /\
             length pattern > 0 /\
             (forall (q: nat). q < bound ==>
               is_prefix_suffix pattern q (SZ.v (index pi q))) /\
             (forall (q: nat) (k: nat). q < bound /\ is_prefix_suffix pattern q k ==>
               k <= SZ.v (index pi q)))
    (ensures pi_max_sz_up_to pattern pi bound)
  = ()
#pop-options

/// Top-level helper: validity at any q' < q+1 from separate facts.
/// Must be top-level to avoid inner function subtyping issues.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let valid_at_combined (#a: eqtype) (pattern: seq a) (pi: seq SZ.t)
    (q: nat{0 < q /\ q < length pattern}) (q': nat{q' < length pattern})
  : Lemma
    (requires length pi >= length pattern /\
             (forall (r: nat). r < q ==>
               is_prefix_suffix pattern r (SZ.v (index pi r))) /\
             is_prefix_suffix pattern q (SZ.v (index pi q)) /\
             q' < q + 1)
    (ensures is_prefix_suffix pattern q' (SZ.v (index pi q')))
  = if q' < q then ()
    else ()
#pop-options

/// Top-level helper: maximality at any q' < q+1 from separate flat foralls.
/// Explicit case split avoids Z3 trigger matching issues.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let max_at_combined (#a: eqtype) (pattern: seq a) (pi: seq SZ.t)
    (q: nat{0 < q /\ q < length pattern}) (q': nat{q' < length pattern}) (k: nat)
  : Lemma
    (requires length pi >= length pattern /\
             (forall (r: nat) (m: nat). r < q /\ is_prefix_suffix pattern r m ==>
               m <= SZ.v (index pi r)) /\
             (forall (j: nat). is_prefix_suffix pattern q j ==> j <= SZ.v (index pi q)) /\
             q' < q + 1 /\ is_prefix_suffix pattern q' k)
    (ensures k <= SZ.v (index pi q'))
  = if q' < q then ()
    else ()
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let extend_maximality (#a: eqtype) (pattern: seq a) (pi_new: seq SZ.t)
    (q: nat{0 < q /\ q < length pattern}) (k_final: nat) (chars_match: bool)
  : Lemma
    (requires length pi_new >= length pattern /\
             length pattern > 0 /\
             (forall (r: nat). r < q ==>
               is_prefix_suffix pattern r (SZ.v (index pi_new r))) /\
             (forall (r: nat) (m: nat). r < q /\ is_prefix_suffix pattern r m ==>
               m <= SZ.v (index pi_new r)) /\
             is_prefix_suffix pattern (q - 1) k_final /\
             k_final < length pattern /\
             all_ps_above_mismatch pattern q k_final /\
             (chars_match ==> index pattern k_final == index pattern q) /\
             (not chars_match ==> (k_final == 0 /\ index pattern k_final <> index pattern q)) /\
             SZ.v (index pi_new q) == (if chars_match then k_final + 1 else k_final) /\
             is_prefix_suffix pattern q (SZ.v (index pi_new q)))
    (ensures pi_max_sz_up_to pattern pi_new (q + 1))
  = // Step 1: prove maximality at position q
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires
        (maximality_at_q pattern pi_new q k_final chars_match));
    // Step 2: build combined validity forall for q+1
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires
        (valid_at_combined pattern pi_new q));
    // Step 3: build combined maximality forall for q+1
    FStar.Classical.forall_intro_2
      (FStar.Classical.move_requires_2
        (max_at_combined pattern pi_new q));
    // Step 4: fold into pi_max_sz_up_to
    fold_pi_max_up_to pattern pi_new (q + 1)
#pop-options

/// pi_max_sz_up_to at full length implies pi_max_sz
let up_to_full (#a: eqtype) (pattern: seq a) (pi: seq SZ.t)
  : Lemma
    (requires pi_max_sz_up_to pattern pi (length pattern) /\
             length pi == length pattern)
    (ensures pi_max_sz pattern pi)
  = ()

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
