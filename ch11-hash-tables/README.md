# CLRS Chapter 11: Hash Tables

## Verification Status

**ZERO ADMITS.** Every module in this chapter is fully verified with no
`admit()`, `assume()`, or `sorry` calls.

## Overview

This directory contains a verified Pulse implementation of a hash table with
open addressing and linear probing, following CLRS §11.4. The formalization has
three layers:

1. **Pure specification** (`Spec.fst`): association-list model with algebraic
   frame lemmas (insert/search/delete).
2. **Imperative Pulse implementation** (`Impl.fst`): fixed-size array with
   sentinel values, linear probing, and full separation-logic proofs.
3. **Refinement bridge** (`Lemmas.fst`): proves the link between the array
   representation and the abstract model (probe surjectivity, membership
   equivalence).

All three operations — `hash_insert`, `hash_search`, `hash_delete` — have
verified functional correctness and O(n) worst-case complexity bounds via ghost
tick counters.

## Algorithm Summary

| Property | Value |
|---|---|
| CLRS Section | §11.4 Open Addressing |
| Data structure | Fixed-size `array int` |
| Collision resolution | Linear probing: `h(k, i) = (k % m + i) % m` |
| Sentinels | `-1` = empty, `-2` = deleted, `≥ 0` = valid key |
| Worst-case complexity | O(n) per operation (n = table capacity) |
| Admits | **0** |

## Specification (`CLRS.Ch11.HashTable.Spec`)

The pure model is an association list `list (nat & int)`:

- `ht_insert`: prepends a binding, shadowing any existing one.
- `ht_search`: returns the first matching value.
- `ht_delete`: removes *all* bindings for a key (idempotent).

Algebraic frame lemmas proved by induction:

| Lemma | Statement |
|---|---|
| `lemma_insert_search_same` | `ht_search (ht_insert m k v) k == Some v` |
| `lemma_insert_search_other` | `k1 ≠ k2 ⟹ ht_search (ht_insert m k1 v) k2 == ht_search m k2` |
| `lemma_delete_search_same` | `ht_search (ht_delete m k) k == None` |
| `lemma_delete_search_other` | `k1 ≠ k2 ⟹ ht_search (ht_delete m k1) k2 == ht_search m k2` |
| `lemma_delete_commutes` | Delete on different keys commutes |
| `lemma_delete_idempotent` | Double delete is a no-op |

## Correctness Theorems (`CLRS.Ch11.HashTable.Impl.fsti`)

### `hash_insert`

```fstar
fn hash_insert (table: A.array int) (#s: erased (Seq.seq int))
  (size: SZ.t) (key: int{key >= 0 /\ SZ.fits key})
  (ctr: GR.ref nat) (#c0: erased nat)
  requires A.pts_to table s ** GR.pts_to ctr c0 **
           pure (SZ.v size > 0 /\ Seq.length s == SZ.v size /\ valid_ht s (SZ.v size))
  returns result: bool
  ensures exists* s' cf.
    A.pts_to table s' ** GR.pts_to ctr cf **
    pure (
      Seq.length s' == SZ.v size /\ valid_ht s' (SZ.v size) /\
      (if result then (key_in_table s' (SZ.v size) key /\
                       key_findable s' (SZ.v size) key /\
                       (exists (idx: nat). ... seq_modified_at s s' idx))
       else s' == s) /\
      cf - reveal c0 <= SZ.v size  (* O(n) complexity *)
    )
```

**Postcondition breakdown:**

- `valid_ht s' (SZ.v size)`: the table invariant is preserved. This is the
  CLRS argument that INSERT never creates NIL slots after valid keys.
- `key_in_table s'`: existential — there exists a probe `p < size` where
  `s'[h(key, p)] == key`.
- `key_findable s'`: stronger — no empty slot (`-1`) before the key in the
  probe sequence, so `hash_search` will find it.
- `seq_modified_at s s' idx`: exactly one slot changed (from empty/deleted to key).
- `s' == s` on failure: table is unchanged when full.
- `cf - c0 ≤ size`: at most `size` probes (O(n) worst case).

### `hash_search`

```fstar
fn hash_search (table: A.array int) (#s: erased (Seq.seq int))
  (size: SZ.t) (key: int{key >= 0 /\ SZ.fits key})
  (ctr: GR.ref nat) (#c0: erased nat)
  ...
  returns result: SZ.t
  ensures exists* cf.
    A.pts_to table s **    (* read-only: array unchanged *)
    GR.pts_to ctr cf **
    pure (
      (SZ.v result < SZ.v size ==> Seq.index s (SZ.v result) == key) /\
      (SZ.v result == SZ.v size ==> ~(key_in_table s (SZ.v size) key)) /\
      cf - reveal c0 <= SZ.v size
    )
```

**Postcondition breakdown:**

- **Found** (`result < size`): the array at index `result` contains `key`.
- **Not found** (`result == size`): `key` does not appear anywhere in the table
  (negation of `key_in_table`). This is the **strongest possible** not-found
  guarantee.
- Array returned *unchanged* (same ghost sequence `s`).

### `hash_delete`

```fstar
fn hash_delete (table: A.array int) (#s: erased (Seq.seq int))
  (size: SZ.t) (key: int{key >= 0 /\ SZ.fits key})
  (ctr: GR.ref nat) (#c0: erased nat)
  ...
  returns result: bool
  ensures exists* s' cf.
    A.pts_to table s' ** GR.pts_to ctr cf **
    pure (
      valid_ht s' (SZ.v size) /\
      (if result then (exists (idx: nat). Seq.index s idx == key /\
                       Seq.index s' idx == -2 /\ seq_modified_at s s' idx)
       else Seq.equal s' s) /\
      cf - reveal c0 <= SZ.v size
    )
```

**Postcondition breakdown:**

- **Found** (`result = true`): exactly one slot changed from `key` to `-2`
  (deleted sentinel).
- **Not found** (`result = false`): table unchanged.
- `valid_ht` preserved: delete never introduces `-1` (NIL) in a position that
  would break a probe chain.

### Strongest Guarantees

The postconditions are the strongest functional guarantees for open-addressing
hash tables:

- **Insert** proves both `key_in_table` (key exists) *and* `key_findable` (key
  is reachable by search), plus exact single-slot modification.
- **Search** proves complete absence (`¬key_in_table`) on not-found, not just
  "reached an empty slot."
- **Delete** proves the CLRS lazy-deletion invariant: only the target slot
  changes, and only to the deleted sentinel.

### `valid_ht` — Table Invariant

```fstar
let valid_ht (s: Seq.seq int) (size: nat) : prop =
  size > 0 /\ size == Seq.length s /\
  (forall (k: int) (probe: nat).
    k >= 0 /\ probe < size /\ Seq.index s (hash_probe_nat k probe size) == k ==>
    (forall (p: nat). p < probe ==> Seq.index s (hash_probe_nat k p size) =!= -1))
```

This captures the core CLRS invariant: for every key at probe position `probe`,
no earlier probe position contains NIL (`-1`). Without this, search could
prematurely stop at a NIL slot and miss a key that was placed further along.

## Complexity

All three operations have O(n) worst-case bounds proved via ghost tick counters:

| Operation | Bound | How proved |
|---|---|---|
| `hash_insert` | `cf - c0 ≤ size` | One tick per probe, loop exits at `size` |
| `hash_search` | `cf - c0 ≤ size` | One tick per probe, loop exits at `size` |
| `hash_delete` | `cf - c0 ≤ size` | One tick per probe, loop exits at `size` |

The counter `ctr: GR.ref nat` is a ghost reference — fully erased at runtime.
The loop invariant maintains `vc - c0 == vi` (exact tick-per-probe equality),
and `vi ≤ size` at exit gives the O(n) bound.

**Gap:** Under uniform hashing (CLRS §11.4), expected probes are O(1/(1−α))
where α is the load factor. The average-case bound requires a probabilistic
model not formalized here.

## Limitations

- **Only linear probing.** No chaining, quadratic probing, or double hashing.
- **O(n) worst case.** No load-factor analysis or amortized bounds.
- **Integer keys only.** Keys must be non-negative integers (due to sentinel
  encoding). No generic key type or user-supplied hash function.
- **Fixed-size table.** No dynamic resizing.
- **No spec-to-impl refinement for values.** The pure spec models key-value
  pairs, but the imperative implementation stores only keys (no associated
  values).

## Refinement Bridge (`CLRS.Ch11.HashTable.Lemmas`)

The Lemmas module proves that the array representation correctly implements the
abstract model:

| Lemma | Statement |
|---|---|
| `lemma_linear_probe_surjective` | Every position `j` is hit by some probe `p` |
| `lemma_key_in_table_iff_array_has_key` | `key_in_table ⟺ ∃ i. s[i] == key` |
| `lemma_probes_not_key_full_iff` | All probes miss ⟺ key not in array |
| `lemma_array_to_model_mem_full` | `Spec.mem (array_to_model s) k ⟺ array_has_key s k` |

## File Inventory

| File | Role | Lines | Admits |
|---|---|---|---|
| `CLRS.Ch11.HashTable.Spec.fst` | Pure association-list spec + frame lemmas | ~214 | 0 |
| `CLRS.Ch11.HashTable.Impl.fsti` | Public interface: types, predicates, signatures | ~213 | 0 |
| `CLRS.Ch11.HashTable.Impl.fst` | Pulse implementation of insert/search/delete | ~440 | 0 |
| `CLRS.Ch11.HashTable.Lemmas.fsti` | Refinement bridge interface | ~45 | 0 |
| `CLRS.Ch11.HashTable.Lemmas.fst` | Refinement bridge proofs | — | 0 |
| `CLRS.Ch11.HashTable.Test.fst` | Test: create, insert, search, free | — | 0 |

## Building and Verification

```bash
cd ch11-hash-tables
make          # Verify all modules
```

The Makefile includes `$(PULSE_ROOT)/mk/test.mk` for the standard Pulse build
infrastructure.

## References

- CLRS 3rd Edition, Chapter 11: Hash Tables, §11.4 Open Addressing
- Linear Probing: simplest open-addressing scheme
