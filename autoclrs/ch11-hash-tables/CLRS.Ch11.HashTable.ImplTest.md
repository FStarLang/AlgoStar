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
| 2 | `test_insert_then_search` | **Insert on empty table MUST succeed** (`b == true` forced by postcondition). The false branch's probe-sequence constraint contradicts the fresh table (probe 0 hits an empty slot). After insert, search finds the key (`SZ.v r < size`). |
| 3 | `test_insert_search_absent` | **Insert on empty table succeeds.** After inserting key 0, searching for key 1 returns `size` (not found). `seq_modified_at` constrains the table so only key 0 and `-1` values exist. |
| 4 | `test_delete_then_search` | **Insert succeeds. Delete after insert MUST succeed** (`b2 == true` forced). Insert establishes `key_in_table`; delete's false branch asserts `~key_in_table`, a contradiction. After insert + delete, search returns `size` (not found). |
| 5 | `test_insert_no_dup_existing` | **Insert succeeds.** After plain insert of key 0, `hash_insert_no_dup` with the same key returns `true`. The else branch of `insert_no_dup` asserts `~(key_in_table s 3 0)`, contradicting `key_in_table` from the first insert. So `b2 == true` is forced. |
| 6 | `test_insert_no_dup_fresh` | **`hash_insert_no_dup` on empty table MUST succeed** (same contradiction as hash_insert). The `~(key_in_table s size key)` clause correctly identifies it as a fresh insert. |
| 7 | `test_create_free` | Basic lifecycle: create a table and immediately free it. Proves preconditions of both `hash_table_create` and `hash_table_free` are satisfiable. |

## Auxiliary Lemmas

Three pure helper lemmas were needed:

- **`lemma_create_index`**: `Seq.index (Seq.create n v) i == v` for `i < n`.
  Trivial but gives Z3 an explicit trigger for reasoning about fresh tables.

- **`lemma_create_no_key`**: `~(key_in_table (Seq.create n (-1)) n key)` for
  any `key >= 0`. Proves that a fresh table contains no valid keys.

- **`trigger_insert_empty`**: Generates the term `hash_probe_nat key 0 n` in
  the Z3 context and proves `Seq.index (Seq.create n (-1)) (hash_probe_nat key 0 n) == -1`.
  This triggers the pattern in the insert postcondition's false-branch universal
  quantifier, letting Z3 derive the contradiction that forces `result == true`.

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

### ✅ Insert Guarantees Success on Non-Full Tables (FIXED)

**Previous issue**: The postcondition of `hash_insert` did not guarantee
success when empty slots were available. Tests had to branch on the insert
result, with the `false` branch handled vacuously.

**Fix**: The false branch now includes a probe-sequence constraint:
```
else (s' == s /\
      (forall (q: nat). {:pattern (hash_probe_nat key q (SZ.v size))}
        q < SZ.v size ==>
          Seq.index s (hash_probe_nat key q (SZ.v size)) =!= -1 /\
          Seq.index s (hash_probe_nat key q (SZ.v size)) =!= -2))
```

This says: if insert fails, every position in the probe sequence is occupied
(not empty and not deleted). For a concrete empty table, probe 0 hits an
empty slot (value `-1`), making the false branch contradictory. Z3 derives
`result == true`.

**Impact**: Tests 2–6 no longer need `if b { ... } else { ... }` branching.
They directly assert `b == true` (or `b1 == true`), eliminating boilerplate
and proving that the spec is precise enough to determine insert success on
non-full tables.

### ✅ Delete Guarantees Key Absence on Failure (FIXED)

**Previous issue**: The false branch of `hash_delete` said only
`Seq.equal s' s` — it didn't state the key was absent.

**Fix**: The false branch now includes `~(key_in_table s (SZ.v size) key)`:
```
else (Seq.equal s' s /\ ~(key_in_table s (SZ.v size) key))
```

**Impact**: Test 4 now proves `b2 == true` (delete must succeed after insert).
Previously, the delete-failed branch could not be eliminated because the spec
didn't connect delete failure to key absence.

### ✅ Delete Simplified via hash_search

The `hash_delete` implementation was restructured to call `hash_search`
internally, followed by a single slot write if found. This naturally provides
`~(key_in_table s size key)` from `hash_search`'s not-found postcondition,
simplifying both the implementation and the proof.

## Verification Details

- **F\* version**: 2025.12.15~dev
- **Max z3rlimit used**: 120 (in `test_delete_then_search` and
  `test_insert_no_dup_existing`)
- **Fuel/ifuel**: 2/1 throughout
- **Total verification time**: ~20 seconds

## Concrete Execution (C Extraction)

The verified Pulse code is extracted to C via KaRaMeL and compiled
to a native executable.

### Extraction Pipeline

1. **F\* → KaRaMeL IR**: Per-module `fstar.exe --codegen krml --extract_module`
   produces separate `.krml` files for `Impl` and `ImplTest` modules.
2. **KaRaMeL IR → C**: `krml -bundle ...` generates
   `CLRS_Ch11_HashTable_ImplTest.c/.h` with both the Impl functions (as
   `static`) and the ImplTest functions (as public `bool`-returning).
   Ghost/erased parameters (`#s`, `ctr`, `#c0`) are fully erased.
3. **Compilation**: `cc` links the extracted test code, runtime stubs
   (`fstar_support.c`, `prims.c`), and a `main.c` driver that checks
   each test function's `bool` return value.

### Test Output

```
=== CLRS Ch11 Hash Table — Concrete Execution ===
test_search_empty                ... PASS
test_insert_then_search          ... PASS
test_insert_search_absent        ... PASS
test_delete_then_search          ... PASS
test_insert_no_dup_existing      ... PASS
test_insert_no_dup_fresh         ... PASS
test_create_free                 ... PASS
All 7 tests passed.
```

### Build & Run

```bash
make test     # extract, compile, and run
make extract  # extract to C only
```

### Notes

- All 7 test functions return `bool` with postcondition `pure (r == true)`.
  Each test computes a concrete boolean result by comparing runtime values
  and returns it. The `main.c` driver checks return values and fails fast
  on any mismatch.
- `krml_checked_int_t` (≡ `int32_t`) represents F\*'s mathematical `int` at
  runtime. The `fstar_support.c` file provides runtime stubs for
  `FStar_SizeT_v` and `FStar_SizeT_uint_to_t` conversions.
