module CLRS.Ch11.HashTable.Lemmas

(**
   Refinement bridge between the pure Spec model and the Pulse implementation.

   Proves:
   1. Linear probing covers all positions (surjectivity)
   2. key_in_table <==> array_has_key (membership equivalence)
   3. probes_not_key for all probes <==> ~(array_has_key)
   4. Array-to-model correspondence with the Spec's mem
*)

open FStar.Classical

module Impl = CLRS.Ch11.HashTable.Impl
module Spec = CLRS.Ch11.HashTable.Spec
module Seq = FStar.Seq

(** Simple array membership: key exists at some index *)
let array_has_key (s: Seq.seq int) (k: nat) : prop =
  exists (i: nat). i < Seq.length s /\ Seq.index s i == k

(** ================================================================
    Array-to-model definitions
    ================================================================ *)

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


(** ================================================================
    Lemma 1: Linear probing covers all positions
    ================================================================

    For any target position j in {0..size-1}, there exists a probe
    p in {0..size-1} such that hash_probe_nat key p size == j.
    This is because (key % size + p) % size is a permutation of
    {0..size-1} as p ranges over {0..size-1}.
*)
#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"
let lemma_linear_probe_surjective
  (key: int{key >= 0}) (size: nat{size > 0}) (j: nat{j < size})
  : Lemma (exists (p: nat). p < size /\ Impl.hash_probe_nat key p size == j)
  = let h = key % size in
    let p = (j + size - h) % size in
    FStar.Math.Lemmas.lemma_mod_add_distr h (j + size - h) size;
    assert (h + (j + size - h) == j + size);
    FStar.Math.Lemmas.lemma_mod_plus j 1 size;
    FStar.Math.Lemmas.modulo_lemma j size;
    assert (Impl.hash_probe_nat key p size == j)
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
    (ensures Impl.key_in_table s size key)
  = lemma_linear_probe_surjective key size i

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"
let lemma_key_in_table_iff_array_has_key
  (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: int{key >= 0})
  : Lemma (Impl.key_in_table s size key <==> array_has_key s key)
  = FStar.Classical.forall_intro
      (FStar.Classical.move_requires (lemma_index_implies_key_in_table s size key))
#pop-options


(** ================================================================
    Lemma 3: probes_not_key <==> ~(array_has_key)
    ================================================================

    All probes missing the key is equivalent to the key not being
    in the array.
*)
#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"
let lemma_probes_not_key_full_iff
  (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: int{key >= 0})
  : Lemma (Impl.probes_not_key s size key size <==> ~(array_has_key s key))
  = lemma_key_in_table_iff_array_has_key s size key;
    let aux (j: nat) : Lemma (requires j < size)
                              (ensures exists (p: nat). p < size /\ Impl.hash_probe_nat key p size == j)
      = lemma_linear_probe_surjective key size j
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options


(** ================================================================
    Array-to-model correspondence lemmas
    ================================================================ *)

(** Membership in the model corresponds to positive-key array presence *)
#push-options "--z3rlimit 5 --fuel 2 --ifuel 1"
let rec lemma_array_to_model_mem
  (s: Seq.seq int) (i: nat{i <= Seq.length s}) (k: nat)
  : Lemma
    (ensures Spec.mem (array_to_model_aux s i) k <==>
             (exists (j: nat). j < i /\ Seq.index s j == k))
    (decreases i)
  = if i = 0 then ()
    else (
      lemma_array_to_model_mem s (i - 1) k
    )
#pop-options

(** Full correspondence: mem in the model <==> array_has_key *)
let lemma_array_to_model_mem_full
  (s: Seq.seq int) (k: nat)
  : Lemma (Spec.mem (array_to_model s) k <==> array_has_key s k)
  = lemma_array_to_model_mem s (Seq.length s) k


(** ================================================================
    Lemma 5: Delete + unique_key guarantees key absence
    ================================================================

    If the key appeared at most once (unique_key) and delete changed that
    slot from key to -2, then the key is completely absent.
*)
#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"
let lemma_delete_unique_guarantees_absence
  (s s': Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s})
  (key: int{key >= 0})
  (idx: nat{idx < Seq.length s /\ Seq.length s' == Seq.length s})
  : Lemma
    (requires
      Impl.unique_key s key /\
      Seq.index s idx == key /\
      Seq.index s' idx == -2 /\
      Impl.seq_modified_at s s' idx)
    (ensures ~(Impl.key_in_table s' size key))
  = // Show: for all j in 0..len-1, s'[j] != key
    // - j == idx: s'[idx] = -2 != key (key >= 0)
    // - j != idx: s'[j] = s[j]. If s[j] == key, then unique_key + s[idx] == key gives j == idx.
    //   Contradiction. So s'[j] != key.
    // Hence ~(array_has_key s' key), and by the equivalence, ~(key_in_table s' size key).
    lemma_key_in_table_iff_array_has_key s' size key;
    introduce forall (j: nat). j < Seq.length s' ==> Seq.index s' j =!= key
    with introduce _ ==> _
    with _. (
      if j = idx then ()
      else ()
    )
#pop-options


(** ================================================================
    Lemma 6: Fresh insert gives unique key
    ================================================================

    If the key was absent from the table and was freshly inserted at
    exactly one position, then the key is unique in the new table.
*)
#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"
let lemma_insert_fresh_unique_key
  (s s': Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s})
  (key: int{key >= 0})
  (idx: nat{idx < Seq.length s /\ Seq.length s' == Seq.length s})
  : Lemma
    (requires
      ~(Impl.key_in_table s size key) /\
      Seq.index s' idx == key /\
      Impl.seq_modified_at s s' idx)
    (ensures Impl.unique_key s' key)
  = // ~(key_in_table s size key) ==> ~(array_has_key s key) ==> forall j. s[j] != key
    lemma_key_in_table_iff_array_has_key s size key;
    // Show: for i, j with s'[i] == key and s'[j] == key, i == j
    // s'[j] == key. If j != idx, then s'[j] = s[j]. But s[j] != key. Contradiction.
    // So j == idx. Similarly i == idx. Hence i == j.
    introduce forall (i j: nat).
      i < Seq.length s' /\ j < Seq.length s' /\
      Seq.index s' i == key /\ Seq.index s' j == key ==> i == j
    with introduce _ ==> _
    with _. (
      assert (i == idx);
      assert (j == idx)
    )
#pop-options


(** ================================================================
    Lemma 7 & 8: Spec model connections
    ================================================================

    Bridge between Impl.key_in_table and Spec.mem via array_has_key.
*)

let lemma_key_in_table_spec_mem
  (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: nat)
  : Lemma
    (requires Impl.key_in_table s size key)
    (ensures Spec.mem (array_to_model s) key)
  = lemma_key_in_table_iff_array_has_key s size key;
    lemma_array_to_model_mem_full s key

let lemma_key_absent_spec_not_mem
  (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: nat)
  : Lemma
    (requires ~(Impl.key_in_table s size key))
    (ensures ~(Spec.mem (array_to_model s) key))
  = lemma_key_in_table_iff_array_has_key s size key;
    lemma_array_to_model_mem_full s key
