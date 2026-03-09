# Hash Table with Open Addressing (CLRS §11.4)

## Top-Level Signatures

Here are the top-level signatures proven about the hash table operations in
`CLRS.Ch11.HashTable.Impl.fsti`:

### `hash_insert`

```fstar
fn hash_insert
  (table: A.array int)
  (#s: erased (Seq.seq int))
  (size: SZ.t)
  (key: int{key >= 0 /\ SZ.fits key})
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to table s **
    GR.pts_to ctr c0 **
    pure (SZ.v size > 0 /\ Seq.length s == SZ.v size /\
          valid_ht s (SZ.v size))
  returns result: bool
  ensures exists* s' cf.
    A.pts_to table s' **
    GR.pts_to ctr cf **
    pure (
      Seq.length s' == SZ.v size /\
      Seq.length s' == Seq.length s /\
      valid_ht s' (SZ.v size) /\
      (if result
       then (key_in_table s' (SZ.v size) key /\
             key_findable s' (SZ.v size) key /\
             (exists (idx: nat). idx < SZ.v size /\
               (Seq.index s idx == -1 \/ Seq.index s idx == -2) /\
               Seq.index s' idx == key /\
               seq_modified_at s s' idx))
       else s' == s) /\
      cf >= reveal c0 /\ cf - reveal c0 <= SZ.v size
    )
```

### `hash_search`

```fstar
fn hash_search
  (table: A.array int)
  (#s: erased (Seq.seq int))
  (size: SZ.t)
  (key: int{key >= 0 /\ SZ.fits key})
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to table s **
    GR.pts_to ctr c0 **
    pure (SZ.v size > 0 /\ Seq.length s == SZ.v size /\
          valid_ht s (SZ.v size))
  returns result: SZ.t
  ensures exists* cf.
    A.pts_to table s **
    GR.pts_to ctr cf **
    pure (
      SZ.v result <= SZ.v size /\
      SZ.v size > 0 /\
      Seq.length s == SZ.v size /\
      key >= 0 /\
      (SZ.v result < SZ.v size ==> (
        SZ.v result < Seq.length s /\
        Seq.index s (SZ.v result) == key
      )) /\
      (SZ.v result == SZ.v size ==> ~(key_in_table s (SZ.v size) key)) /\
      cf >= reveal c0 /\ cf - reveal c0 <= SZ.v size
    )
```

### `hash_delete`

```fstar
fn hash_delete
  (table: A.array int)
  (#s: erased (Seq.seq int))
  (size: SZ.t)
  (key: int{key >= 0 /\ SZ.fits key})
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to table s **
    GR.pts_to ctr c0 **
    pure (SZ.v size > 0 /\ Seq.length s == SZ.v size /\
          valid_ht s (SZ.v size))
  returns result: bool
  ensures exists* s' cf.
    A.pts_to table s' **
    GR.pts_to ctr cf **
    pure (
      Seq.length s' == SZ.v size /\
      Seq.length s' == Seq.length s /\
      valid_ht s' (SZ.v size) /\
      cf >= reveal c0 /\ cf - reveal c0 <= SZ.v size /\
      (if result
       then (exists (idx: nat).
               idx < Seq.length s /\
               Seq.index s idx == key /\
               Seq.index s' idx == -2 /\
               seq_modified_at s s' idx)
       else Seq.equal s' s)
    )
```

### Parameters

* `table` is a mutable array of `int` used as the hash table. Sentinel values
  encode slot state: `-1` = empty, `-2` = deleted, `>= 0` = valid key. The
  ghost variable `s` captures the initial contents.

* `size` is the table capacity, of type `SZ.t` (machine-sized).

* `key` is the key to insert/search/delete. Restricted to non-negative integers
  that fit in `SZ.t`.

* `ctr` is a **ghost counter** for counting probe operations. The initial value
  is `c0`. Ghost values are erased at runtime.

### Preconditions

* `SZ.v size > 0`: The table must have at least one slot.

* `Seq.length s == SZ.v size`: The logical sequence matches the size parameter.

* `valid_ht s (SZ.v size)`: The table satisfies the structural invariant (see
  below).

### Postconditions

**Insert** (`hash_insert`):
* `valid_ht s' (SZ.v size)` — Invariant preserved.
* On success (`result = true`):
  - `key_in_table s' (SZ.v size) key` — Key is present in the table.
  - `key_findable s' (SZ.v size) key` — Key is reachable by `hash_search`.
  - Exactly one slot changed: an empty (`-1`) or deleted (`-2`) slot now holds `key`.
* On failure (`result = false`): `s' == s` — Table is full, unchanged.
* `cf - reveal c0 <= SZ.v size` — At most `size` probes.

**Search** (`hash_search`):
* On found (`result < size`): `Seq.index s result == key` — The returned index
  contains the key.
* On not found (`result == size`): `~(key_in_table s (SZ.v size) key)` — Key is
  truly absent.
* `cf - reveal c0 <= SZ.v size` — At most `size` probes.

**Delete** (`hash_delete`):
* `valid_ht s' (SZ.v size)` — Invariant preserved.
* On success: Exactly one slot that held `key` is now `-2` (DELETED).
* On failure: `Seq.equal s' s` — Key not found, table unchanged.
* `cf - reveal c0 <= SZ.v size` — At most `size` probes.

## Auxiliary Definitions

### `valid_ht` (from `CLRS.Ch11.HashTable.Impl`)

```fstar
let valid_ht (s: Seq.seq int) (size: nat) : prop =
  size > 0 /\ size == Seq.length s /\
  (forall (k: int) (probe: nat). {:pattern (Seq.index s (hash_probe_nat k probe size))}
    k >= 0 /\ probe < size /\ Seq.index s (hash_probe_nat k probe size) == k ==>
    (forall (p: nat). {:pattern (hash_probe_nat k p size)}
      p < probe ==> Seq.index s (hash_probe_nat k p size) =!= -1))
```

This captures the CLRS correctness argument for open addressing: if a key `k`
is found at probe position `probe`, then no empty slot (`-1`) appears at any
earlier probe position. This ensures `hash_search` can stop upon encountering an
empty slot. INSERT fills NIL/DELETED slots with keys; DELETE turns key slots
into DELETED (`-2`), never back to NIL. This is the heart of the correctness
argument.

### `hash_probe_nat` (from `CLRS.Ch11.HashTable.Impl`)

```fstar
let hash_probe_nat (key: int{key >= 0}) (probe: nat) (size: nat{size > 0}) : nat =
  (key % size + probe) % size
```

Division-method hash with linear probing: `h(k, i) = (k % m + i) % m`.

### `key_in_table` (from `CLRS.Ch11.HashTable.Impl`)

```fstar
let key_in_table (s: Seq.seq int) (size: nat{size > 0}) (key: int{key >= 0}) : prop =
  exists (probe: nat). probe < size /\ probe < Seq.length s /\
    hash_probe_nat key probe size < Seq.length s /\
    Seq.index s (hash_probe_nat key probe size) == key
```

Key is at some position in the probe sequence.

### `key_findable` (from `CLRS.Ch11.HashTable.Impl`)

```fstar
let key_findable (s: Seq.seq int) (size: nat{size > 0 /\ size == Seq.length s}) (key: int{key >= 0}) : prop =
  exists (probe: nat). probe < size /\
    hash_probe_nat key probe size < Seq.length s /\
    Seq.index s (hash_probe_nat key probe size) == key /\
    (forall (p: nat). {:pattern (hash_probe_nat key p size)}
      p < probe ==> Seq.index s (hash_probe_nat key p size) =!= -1)
```

Stronger than `key_in_table`: the key is not only present but reachable by
`hash_search` (no empty slot blocks the probe sequence before the key).

### `seq_modified_at` (from `CLRS.Ch11.HashTable.Impl`)

```fstar
let seq_modified_at (s s': Seq.seq int) (idx: nat{idx < Seq.length s /\ Seq.length s' == Seq.length s}) : prop =
  forall (j: nat). j < Seq.length s /\ j =!= idx ==> Seq.index s j == Seq.index s' j
```

Frame condition: only position `idx` may differ between the old and new table.

## What Is Proven

**Functional correctness of all three operations:**

* **Insert** proves the key is present AND findable after insertion, that exactly
  one empty/deleted slot was consumed, and all other slots are unchanged.

* **Search** proves sound and complete membership: found ↔ key present in
  table (via the `valid_ht` invariant and the `key_in_table` predicate).

* **Delete** proves that exactly one occurrence is marked DELETED and all other
  slots are unchanged.

* **Invariant preservation:** All three operations preserve `valid_ht`, ensuring
  continued correctness of future operations.

**Complexity:** Each operation performs at most `size` probes (worst case: full
linear scan). This is proven by threading a ghost tick counter through the Pulse
implementation.

**Refinement bridge** (`CLRS.Ch11.HashTable.Lemmas`): Four lemmas connect the
imperative implementation to the pure specification:

1. `lemma_linear_probe_surjective`: Linear probing covers all array positions.
2. `lemma_key_in_table_iff_array_has_key`: `key_in_table` ↔ simple array membership.
3. `lemma_probes_not_key_full_iff`: Full probe miss ↔ key absent from array.
4. `lemma_array_to_model_mem_full`: Spec model membership ↔ array membership.

**Zero admits, zero assumes.** All proof obligations are mechanically discharged
by F\* and Z3.

## Specification Gaps and Limitations

1. **Keys are non-negative integers only.** The implementation uses sentinel
   values `-1` (empty) and `-2` (deleted), so valid keys must satisfy
   `key >= 0`. Real hash tables use a separate occupancy bitmap or option types.

2. **No key-value pairs.** The table stores keys only (keys serve as their own
   values). CLRS hash tables store key-value pairs; extending this would require
   pairing each key with a satellite value.

3. **Linear probing only.** The probe function is `(k % m + i) % m`. CLRS also
   covers quadratic probing and double hashing (§11.4). The `valid_ht` invariant
   is specific to linear probing's surjectivity property.

4. **No load factor / rehashing.** Insert returns `false` when the table is full
   but does not resize. CLRS discusses dynamic tables in §17.4; this
   implementation covers only the fixed-size case.

5. **Worst-case O(n), not amortized O(1).** The proven complexity bound is
   `cf - c0 ≤ size` (linear scan). CLRS's amortized O(1) bounds under load
   factor assumptions (Theorem 11.6, 11.8) are not proven.

6. **No connection to pure Spec model in postconditions.** The Spec module
   (`CLRS.Ch11.HashTable.Spec`) defines an association-list model with algebraic
   laws (insert-then-search, delete-then-search, etc.), and the Lemmas module
   proves a refinement bridge. However, the Pulse operation postconditions do
   not directly refer to the Spec model — they state correctness in terms of
   array-level predicates (`key_in_table`, `key_findable`). The connection is
   proven separately in the Lemmas module.

7. **Delete does not guarantee key absence.** The delete postcondition says one
   slot changed from `key` to `-2`. If the table contained duplicate
   occurrences of `key` (which INSERT does not prevent when called on an
   already-present key), delete removes only one.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Probes (insert) | O(n) = size | ✅ Ghost counter | Upper bound only |
| Probes (search) | O(n) = size | ✅ Ghost counter | Upper bound only |
| Probes (delete) | O(n) = size | ✅ Ghost counter | Upper bound only |

The complexity is **fully linked** to the imperative implementation: the ghost
counter `ctr` is incremented once per probe (array access + comparison) inside
each operation's while loop, and the postconditions directly constrain
`cf - c0 ≤ size`.

## Proof Structure

Each operation follows the same pattern:

1. A `while` loop iterates over probe positions `i = 0, 1, ..., size-1`.
2. The loop invariant tracks: current probe index, operation-specific state
   (found/inserted/deleted), table contents, and the ghost tick counter
   (`vc - c0 == vi`, exactly `vi` probes so far).
3. Key supporting lemmas in the implementation:
   * `lemma_hash_probe_consistent`: Machine-sized `hash_probe` agrees with
     `hash_probe_nat`.
   * `lemma_valid_ht_create`: Fresh tables satisfy `valid_ht`.
   * `lemma_valid_ht_insert`: Inserting at the first empty/deleted probe
     position preserves `valid_ht`.
   * `lemma_valid_ht_delete`: Replacing a key with `-2` preserves `valid_ht`.
   * `lemma_valid_ht_search_not_found`: Under `valid_ht`, an empty slot in
     the probe sequence proves the key is absent.

## Files

| File | Role |
|------|------|
| `CLRS.Ch11.HashTable.Impl.fsti` | Public interface (signatures + predicates) |
| `CLRS.Ch11.HashTable.Impl.fst` | Pulse implementation |
| `CLRS.Ch11.HashTable.Spec.fst` | Pure association-list model + algebraic laws |
| `CLRS.Ch11.HashTable.Lemmas.fsti` | Refinement bridge signatures |
| `CLRS.Ch11.HashTable.Lemmas.fst` | Refinement bridge proofs |
| `CLRS.Ch11.HashTable.Test.fst` | Test harness |
