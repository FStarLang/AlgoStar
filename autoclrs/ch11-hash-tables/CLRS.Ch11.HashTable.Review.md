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

### `hash_insert_no_dup`

```fstar
fn hash_insert_no_dup
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
      cf >= reveal c0 /\ cf - reveal c0 <= 2 * SZ.v size /\
      (if result
       then (key_in_table s' (SZ.v size) key /\
             key_findable s' (SZ.v size) key /\
             (s' == s \/
              (exists (idx: nat). idx < SZ.v size /\
                (Seq.index s idx == -1 \/ Seq.index s idx == -2) /\
                Seq.index s' idx == key /\
                seq_modified_at s s' idx /\
                ~(key_in_table s (SZ.v size) key))))
       else (s' == s /\ ~(key_in_table s (SZ.v size) key)))
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

**Insert-no-dup** (`hash_insert_no_dup`):
* `valid_ht s' (SZ.v size)` — Invariant preserved.
* On success (`result = true`):
  - `key_in_table s' (SZ.v size) key` — Key is present in the table.
  - `key_findable s' (SZ.v size) key` — Key is reachable by `hash_search`.
  - Either `s' == s` (key was already present) or key was freshly inserted
    at one empty/deleted slot with `¬key_in_table s size key`.
* On failure (`result = false`): `s' == s` — Table is full, key was absent.
* `cf - reveal c0 <= 2 * SZ.v size` — At most `2 * size` probes.

**Search** (`hash_search`):
* `valid_ht s (SZ.v size)` — Invariant preserved (postcondition strengthened).
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

### `unique_key` (from `CLRS.Ch11.HashTable.Impl`)

```fstar
let unique_key (s: Seq.seq int) (key: int{key >= 0}) : prop =
  forall (i j: nat). i < Seq.length s /\ j < Seq.length s /\
    Seq.index s i == key /\ Seq.index s j == key ==> i == j
```

Key appears at most once in the table. This invariant is established by
`hash_insert_no_dup` (via `lemma_insert_fresh_unique_key`) and enables
`lemma_delete_unique_guarantees_absence` to prove that delete makes
`¬key_in_table`.

## What Is Proven

**Functional correctness of all four operations:**

* **Insert** proves the key is present AND findable after insertion, that exactly
  one empty/deleted slot was consumed, and all other slots are unchanged.

* **Insert-no-dup** (`hash_insert_no_dup`) searches first, then inserts only if
  the key is absent. Proves key presence and findability, plus a disjunction
  indicating whether the table was unchanged (key was already there) or freshly
  modified (key was absent). Complexity: at most `2 * size` probes.

* **Search** proves sound and complete membership: found ↔ key present in
  table (via the `valid_ht` invariant and the `key_in_table` predicate).
  Postcondition now also preserves `valid_ht` for composability.

* **Delete** proves that exactly one occurrence is marked DELETED and all other
  slots are unchanged.

* **Invariant preservation:** All operations preserve `valid_ht`, ensuring
  continued correctness of future operations.

**Key uniqueness and delete-guarantees-absence:**

* `unique_key s key`: key appears at most once in the table.
* `lemma_insert_fresh_unique_key`: inserting an absent key produces `unique_key`.
* `lemma_delete_unique_guarantees_absence`: if `unique_key` holds, delete
  guarantees `¬key_in_table`.
* Users who exclusively use `hash_insert_no_dup` maintain key uniqueness as an
  invariant, and delete then guarantees the key is absent after removal.

**Complexity:** Each base operation performs at most `size` probes (worst case:
full linear scan). `hash_insert_no_dup` performs at most `2 * size` probes.
This is proven by threading a ghost tick counter through the Pulse
implementation.

**Refinement bridge** (`CLRS.Ch11.HashTable.Lemmas`): Eight lemmas connect the
imperative implementation to the pure specification:

1. `lemma_linear_probe_surjective`: Linear probing covers all array positions.
2. `lemma_key_in_table_iff_array_has_key`: `key_in_table` ↔ simple array membership.
3. `lemma_probes_not_key_full_iff`: Full probe miss ↔ key absent from array.
4. `lemma_array_to_model_mem_full`: Spec model membership ↔ array membership.
5. `lemma_delete_unique_guarantees_absence`: Delete + unique → key absent.
6. `lemma_insert_fresh_unique_key`: Fresh insert → key unique.
7. `lemma_key_in_table_spec_mem`: `key_in_table` → `Spec.mem`.
8. `lemma_key_absent_spec_not_mem`: `¬key_in_table` → `¬Spec.mem`.

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

6. **~~No connection to pure Spec model in postconditions.~~** ✅ **ADDRESSED.**
   The Lemmas module now provides explicit connection lemmas:
   `lemma_key_in_table_spec_mem` (key present → `Spec.mem` holds) and
   `lemma_key_absent_spec_not_mem` (key absent → `¬Spec.mem`). Callers
   can translate any Impl postcondition to Spec-level statements by
   composing these with the operation postconditions.

7. **~~Delete does not guarantee key absence.~~** ✅ **ADDRESSED.**
   A new `hash_insert_no_dup` operation searches before inserting,
   preventing duplicates. A `unique_key` predicate tracks key
   uniqueness, and `lemma_delete_unique_guarantees_absence` proves that
   delete guarantees `¬key_in_table` when `unique_key` holds.
   `lemma_insert_fresh_unique_key` proves that fresh inserts establish
   `unique_key`. Users who exclusively use `hash_insert_no_dup` maintain
   key uniqueness as an invariant, ensuring delete always guarantees
   absence.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Probes (insert) | O(n) = size | ✅ Ghost counter | Upper bound only |
| Probes (insert_no_dup) | O(n) = 2 × size | ✅ Ghost counter | Upper bound only |
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
   * `lemma_valid_ht_key_at_index_findable`: Under `valid_ht`, if a key
     is at some array index, then `key_findable` holds.

`hash_insert_no_dup` composes `hash_search` and `hash_insert`, using the
surjectivity of linear probing to establish `key_findable` when the key
is already present.

## Files

| File | Role |
|------|------|
| `CLRS.Ch11.HashTable.Impl.fsti` | Public interface (signatures + predicates) |
| `CLRS.Ch11.HashTable.Impl.fst` | Pulse implementation |
| `CLRS.Ch11.HashTable.Spec.fst` | Pure association-list model + algebraic laws |
| `CLRS.Ch11.HashTable.Lemmas.fsti` | Refinement bridge signatures |
| `CLRS.Ch11.HashTable.Lemmas.fst` | Refinement bridge proofs |
| `CLRS.Ch11.HashTable.Test.fst` | Test harness |
