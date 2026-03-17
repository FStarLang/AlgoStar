# Hash Table Spec Validation — ImplTest.md

## Overview

`CLRS.Ch11.HashTable.ImplTest.fst` validates the specifications in
`CLRS.Ch11.HashTable.Impl.fsti` using the methodology from
[Goues et al. (2024)](https://arxiv.org/abs/2406.09757): each test
exercises a small, concrete instance of the API and proves that the
postcondition is precise enough to determine the expected output.

**Status**: All 7 tests verified. **Zero admits. Zero assumes.**

## Test Catalog

| # | Test | What is proven |
|---|------|----------------|
| 1 | `test_search_empty` | Search on empty table returns exactly `size` (not found). Postcondition of `hash_search` is precise: from `SZ.v r < size ==> Seq.index s r == key` and `Seq.create n (-1)` having only `-1` elements, Z3 derives `SZ.v r == size`. |
| 2 | `test_insert_then_search` | After successful insert, search finds the key (`SZ.v r < size`). Postcondition is precise: `key_in_table` from insert contradicts the `~key_in_table` in the not-found branch of search. |
| 3 | `test_insert_search_absent` | After inserting key 0, searching for key 1 returns `size` (not found). Postcondition is precise: `seq_modified_at` constrains the table so that only key 0 and `-1` values exist; Z3 derives that no slot contains key 1. |
| 4 | `test_delete_then_search` | After insert + delete, search returns `size` (not found). Z3 reasons through the composition of insert and delete postconditions. |
| 5 | `test_insert_no_dup_existing` | After plain insert of key 0, `hash_insert_no_dup` with the same key returns `true`. **This is proven from the postcondition alone**: the else branch of `insert_no_dup` asserts `~(key_in_table s 3 0)`, contradicting `key_in_table` from the first insert. So `b2 == true` is forced. |
| 6 | `test_insert_no_dup_fresh` | `hash_insert_no_dup` on empty table: if it succeeds, the `~(key_in_table s size key)` clause in the postcondition correctly identifies it as a fresh insert. |
| 7 | `test_create_free` | Basic lifecycle: create a table and immediately free it. Proves preconditions of both `hash_table_create` and `hash_table_free` are satisfiable. |

## Auxiliary Lemmas

Two pure helper lemmas were needed:

- **`lemma_create_index`**: `Seq.index (Seq.create n v) i == v` for `i < n`.
  Trivial but gives Z3 an explicit trigger for reasoning about fresh tables.

- **`lemma_create_no_key`**: `~(key_in_table (Seq.create n (-1)) n key)` for
  any `key >= 0`. Proves that a fresh table contains no valid keys.

## Spec Findings

### ✅ Postcondition Precision (Verified)

1. **`hash_search` not-found is exact**: When no slot contains the key, the
   postcondition `SZ.v r < size ==> Seq.index s r == key` forces
   `SZ.v r == size`. This is sufficient to determine the exact return value.

2. **`hash_search` found is exact**: When `key_in_table` holds, the
   postcondition forces `SZ.v r < size` and `Seq.index s r == key`. We can
   assert the key was found and read back the correct value.

3. **`hash_insert_no_dup` distinguishes fresh from existing**: The disjunction
   `s' == s \/ (freshly inserted /\ ~key_in_table s size key)` lets callers
   determine whether the table was modified. Test 5 proves this is strong
   enough to force `b2 == true` when the key is already present.

4. **`seq_modified_at` preserves absent-key reasoning**: After insert, the
   combination of `seq_modified_at` and knowledge of the original table
   contents is precise enough to prove other keys remain absent (Test 3).

5. **Delete + Insert compose correctly**: After insert then delete, no slot
   contains the key. The search postcondition correctly derives not-found
   (Test 4).

### ⚠️ Spec Weakness: Insert Does Not Guarantee Success

**Issue**: The postcondition of `hash_insert` (and `hash_insert_no_dup`) does
not guarantee success when empty slots are available. The postcondition is:

```
if result
then (key_in_table s' size key /\ ...)
else s' == s
```

The `else` branch (`s' == s`, table unchanged) is always consistent — it does
not lead to a contradiction even when the table has available slots. This means
we **cannot prove** that inserting into an empty table returns `true`.

**Impact**: Tests 2–6 must branch on the insert result. The `true` branch is
where the interesting assertions live; the `false` branch is vacuously handled.
This pattern works but is less ergonomic than a guaranteed-success insert.

**Attempted fix**: We attempted to strengthen the postcondition to include
`forall (j: nat). j < size ==> Seq.index s j =!= -1 /\ Seq.index s j =!= -2`
in the false branch (meaning: if insert fails, the table is truly full). The
implementation proof requires surjectivity of linear probing (converting from
"all probes checked" to "all slots occupied"). While the standalone surjectivity
lemma verifies, embedding it in the Pulse function body proved difficult due to
Z3's inability to handle multi-step quantifier instantiation (the loop invariant
quantifies over probe indices, and the postcondition quantifies over slot
indices). The `Complexity.count_available` function provides an alternative
mechanism for callers to reason about slot availability.

### ✅ No Other Spec Issues Found

All other postconditions are precise enough for concrete test instances:

- Search correctly reports found vs. not-found
- Delete correctly marks the slot and preserves `valid_ht`
- `insert_no_dup` correctly distinguishes fresh vs. existing
- `seq_modified_at` is strong enough for reasoning about other keys
- `valid_ht` is correctly maintained across all operations

## Verification Details

- **F\* version**: 2025.12.15~dev
- **Max z3rlimit used**: 120 (in `test_delete_then_search` and
  `test_insert_no_dup_existing`)
- **Fuel/ifuel**: 2/1 throughout
- **Total verification time**: ~15 seconds
