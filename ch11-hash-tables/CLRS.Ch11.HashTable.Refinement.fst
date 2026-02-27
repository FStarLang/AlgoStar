module CLRS.Ch11.HashTable.Refinement

(**
   Refinement bridge between the pure Spec model and the Pulse implementation.

   Proves:
   1. Linear probing covers all positions (surjectivity)
   2. key_in_table <==> array_has_key (membership equivalence)
   3. probes_not_key for all probes <==> ~(array_has_key)
   4. Array-to-model correspondence with the Spec's mem
*)

open FStar.Classical
open CLRS.Ch11.HashTable
open FStar.Mul

module Spec = CLRS.Ch11.HashTable.Spec
module Seq = FStar.Seq

(** Simple array membership: key exists at some index *)
let array_has_key (s: Seq.seq int) (k: nat) : prop =
  exists (i: nat). i < Seq.length s /\ Seq.index s i == k


(** ================================================================
    Lemma 1: Linear probing covers all positions
    ================================================================

    For any target position j in {0..size-1}, there exists a probe
    p in {0..size-1} such that hash_probe_nat key p size == j.
    This is because (key % size + p) % size is a permutation of
    {0..size-1} as p ranges over {0..size-1}.
*)
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let lemma_linear_probe_surjective
  (key: int{key >= 0}) (size: nat{size > 0}) (j: nat{j < size})
  : Lemma (exists (p: nat). p < size /\ hash_probe_nat key p size == j)
  = let h = key % size in
    // Witness: p = (j + size - h) % size
    // Since h < size and j >= 0, we have j + size > h, avoiding underflow
    let p = (j + size - h) % size in
    // Proof chain:
    //   hash_probe_nat key p size
    // = (h + p) % size                               [def]
    // = (h + (j + size - h) % size) % size            [def of p]
    // = (h + (j + size - h)) % size                   [lemma_mod_add_distr]
    // = (j + size) % size                             [algebra: h cancels]
    // = j % size                                      [lemma_mod_plus j 1 size]
    // = j                                             [modulo_lemma: j < size]
    FStar.Math.Lemmas.lemma_mod_add_distr h (j + size - h) size;
    assert (h + (j + size - h) == j + size);
    FStar.Math.Lemmas.lemma_mod_plus j 1 size;
    FStar.Math.Lemmas.modulo_lemma j size;
    assert (hash_probe_nat key p size == j)
#pop-options


(** ================================================================
    Lemma 2: key_in_table <==> array_has_key
    ================================================================

    When table size equals the sequence length, finding a key via
    linear probing (key_in_table) is equivalent to the key being
    present at some array index (array_has_key).
*)

(** Helper: if key is at index i, then key_in_table holds *)
let lemma_index_implies_key_in_table
  (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: int{key >= 0}) (i: nat)
  : Lemma
    (requires i < Seq.length s /\ Seq.index s i == key)
    (ensures key_in_table s size key)
  = // By surjectivity, there exists probe p with hash_probe_nat key p size == i
    lemma_linear_probe_surjective key size i
    // Z3 chains: exists p. hash_probe_nat key p size == i
    // Combined with Seq.index s i == key:
    //   Seq.index s (hash_probe_nat key p size) == key
    // This witnesses key_in_table

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let lemma_key_in_table_iff_array_has_key
  (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: int{key >= 0})
  : Lemma (key_in_table s size key <==> array_has_key s key)
  = // Inject "index i with key => key_in_table" into Z3 for all i
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (lemma_index_implies_key_in_table s size key))
    // Forward (key_in_table ==> array_has_key): the probe gives a valid index
    // Backward (array_has_key ==> key_in_table): by the injected universal
#pop-options


(** ================================================================
    Lemma 3: probes_not_key <==> ~(array_has_key)
    ================================================================

    All probes missing the key is equivalent to the key not being
    in the array.
*)
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let lemma_probes_not_key_full_iff
  (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: int{key >= 0})
  : Lemma (probes_not_key s size key size <==> ~(array_has_key s key))
  = // Establish key_in_table <==> array_has_key
    lemma_key_in_table_iff_array_has_key s size key;
    // The existing SMTPat gives: probes_not_key size ==> ~(key_in_table)
    // Combined: probes_not_key ==> ~(array_has_key)  [forward direction]
    //
    // For reverse: ~(array_has_key) ==> probes_not_key
    // ~(array_has_key) means forall i. i < size ==> s[i] =!= key
    // For any probe p < size, hash_probe_nat key p size < size, so
    //   s[hash_probe_nat key p size] =!= key, which is probes_not_key.
    // Inject surjectivity for Z3 to connect the dots:
    let aux (j: nat) : Lemma (requires j < size)
                              (ensures exists (p: nat). p < size /\ hash_probe_nat key p size == j)
      = lemma_linear_probe_surjective key size j
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options


(** ================================================================
    Array-to-model correspondence
    ================================================================

    Extract non-negative entries from the array as an association
    list model, and prove that membership in the model corresponds
    to array membership.
*)

(** Build model from first i entries of the array *)
let rec array_to_model_aux (s: Seq.seq int) (i: nat{i <= Seq.length s})
  : Tot Spec.ht_model (decreases i)
  = if i = 0 then Spec.ht_empty
    else
      let v = Seq.index s (i - 1) in
      let rest = array_to_model_aux s (i - 1) in
      if v >= 0 then Spec.ht_insert rest v v  // key-only: use key as value
      else rest

(** Full array to model *)
let array_to_model (s: Seq.seq int) : Spec.ht_model =
  array_to_model_aux s (Seq.length s)

(** Membership in the model corresponds to positive-key array presence *)
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec lemma_array_to_model_mem
  (s: Seq.seq int) (i: nat{i <= Seq.length s}) (k: nat)
  : Lemma
    (ensures Spec.mem (array_to_model_aux s i) k <==>
             (exists (j: nat). j < i /\ Seq.index s j == k))
    (decreases i)
  = if i = 0 then ()
    else (
      lemma_array_to_model_mem s (i - 1) k
      // IH: mem (array_to_model_aux s (i-1)) k <==> exists j. j < i-1 /\ s[j] == k
      // Z3 unfolds array_to_model_aux once and mem once to connect:
      //   Case v >= 0, v = k: mem is true, witness j = i-1
      //   Case v >= 0, v <> k: mem rest k, s[i-1] =!= k rules out j = i-1
      //   Case v < 0: mem rest k, s[i-1] < 0 <= k rules out j = i-1
    )
#pop-options

(** Full correspondence: mem in the model <==> array_has_key *)
let lemma_array_to_model_mem_full
  (s: Seq.seq int) (k: nat)
  : Lemma (Spec.mem (array_to_model s) k <==> array_has_key s k)
  = lemma_array_to_model_mem s (Seq.length s) k
