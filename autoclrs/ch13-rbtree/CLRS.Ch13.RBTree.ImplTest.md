# CLRS.Ch13.RBTree.ImplTest — Spec Validation Report

**File:** `CLRS.Ch13.RBTree.ImplTest.fst`  
**Target API:** `CLRS.Ch13.RBTree.Impl.fsti` (Okasaki-style Red-Black Tree)  
**Status:** ✅ Fully verified — zero admits, zero assumes  
**Build:** `make` produces `CLRS.Ch13.RBTree.ImplTest.fst.checked` with no errors  

---

## What the Test Does

The test validates the `Impl.fsti` API on a concrete 3-element instance: insert
keys 3, 1, 2 into an empty tree, then search and delete.

### Pure Spec Validation (outside Pulse)

Normalizes the pure spec (`CLRS.Ch13.RBTree.Spec`) on concrete inputs using
`assert_norm` to verify:

| Property | Assertion | Result |
|----------|-----------|--------|
| Tree shape after insert 3 | `S.insert Leaf 3 == Node Black Leaf 3 Leaf` | ✅ |
| Tree shape after insert 1 | `S.insert (insert Leaf 3) 1 == Node Black (Node Red Leaf 1 Leaf) 3 Leaf` | ✅ |
| Tree shape after insert 2 | Balanced: `Node Black (Node Black Leaf 1 Leaf) 2 (Node Black Leaf 3 Leaf)` | ✅ |
| RB invariant holds | `is_rbtree` true on all intermediate trees | ✅ |
| BST invariant holds | `is_bst` true on all intermediate trees | ✅ |
| Search existing keys | `search t3 1/2/3` returns `Some 1/2/3` | ✅ |
| Search missing keys | `search t3 0/4` returns `None` | ✅ |
| Membership | `mem 1/2/3 t3 = true`, `mem 0/4 t3 = false` | ✅ |
| Delete correctness | After deleting 1: `mem 1 = false`, `mem 2/3 = true` | ✅ |
| Delete preserves RB/BST | `is_rbtree t4 = true`, `is_bst t4 = true` | ✅ |
| Duplicate insert identity | `insert t3 2 == t3` | ✅ |
| Delete non-existing key | `delete t3 99` preserves all keys | ✅ |

### Pulse API Test (`test_rbtree_insert_search_delete`)

Exercises the full Pulse separation-logic API in sequence:

1. **`rb_new()`** — creates empty tree with `valid_rbtree y S.Leaf`
2. **`rb_insert_v tree 3`** — inserts 3; postcondition gives `valid_rbtree y (S.insert S.Leaf 3)`, `S.mem 3 ... = true`, and `S.search ... 3 == Some 3`
3. **`rb_insert_v tree 1`** — inserts 1 into tree with 3
4. **`rb_insert_v tree 2`** — inserts 2; triggers Okasaki rotation (RL case). Postcondition directly establishes `S.search 'ft 2 == Some 2`
5. **`rb_search_v tree 2`** — returns `r2`; asserts `r2 == Some 2` **directly from insert postcondition** (no helper lemma needed)
6. **`rb_search_v tree 4`** — returns `r4`; asserts `r4 == None` via membership chain (`insert_mem` × 3) + search postcondition
7. **`rb_delete_v tree 1`** — deletes key 1; postcondition gives `S.mem 1 ... = false` and `S.search ... 1 == None`
8. **`rb_search_v tree 1`** — asserts `r1_after == None` **directly from delete postcondition** (no helper lemma needed)
9. **`rb_search_v tree 3`** — asserts `r3_after == Some 3` via membership chain (`insert_mem` × 3 + `delete_mem`) + search postcondition
10. **`free_valid_rbtree tree`** — frees all memory

---

## Spec Strengthening (2026-03-17)

### Problem Identified

The original `Impl.fsti` postconditions had a gap: `rb_search_v` returned
`result == S.search 'ft k`, and `rb_insert_v`/`rb_delete_v` returned
membership facts (`S.mem k ... = true/false`), but there was **no lemma
connecting `search` and `mem`** in the Lemmas module. This forced the test
to rely on concrete `assert_norm` helper lemmas for every search assertion.

### Changes Made

1. **Added `search_mem` and `search_not_mem` lemmas to `Lemmas.fsti`/`Lemmas.fst`:**
   - `search_mem`: `is_bst t /\ mem k t ==> search t k == Some k`
   - `search_not_mem`: `~(mem k t) ==> search t k == None`
   - `search_correct`: Combined form requiring only `is_bst t`

2. **Strengthened `rb_search_v` postcondition:**
   - Added: `(S.mem k 'ft ==> result == Some k) /\ (~(S.mem k 'ft) ==> result == None)`
   - Clients can now determine the search result from membership alone

3. **Strengthened `rb_insert_v` postcondition:**
   - Added: `S.search (S.insert 'ft k) k == Some k`
   - After inserting k, searching for k is guaranteed to return Some k

4. **Strengthened `rb_delete_v` postcondition:**
   - Added: `S.search (S.delete 'ft k) k == None`
   - After deleting k, searching for k is guaranteed to return None

5. **Same strengthening applied to complexity-aware API** (`rb_search_log`, `rb_insert_log`, `rb_delete_log`)

### Impact on Test

| Test Case | Before | After |
|-----------|--------|-------|
| Search for inserted key 2 | Required `assert_norm` helper | **Direct from postcondition** ✅ |
| Search for non-existing key 4 | Required `assert_norm` helper | Uses `insert_mem` chain + postcondition ✅ |
| Search for deleted key 1 | Required `assert_norm` helper | **Direct from postcondition** ✅ |
| Search for remaining key 3 | Required `assert_norm` helper | Uses `delete_mem` chain + postcondition ✅ |

The key improvement: for same-key operations (insert-then-search, delete-then-search),
the postconditions are now **self-sufficient** — no normalization or helper lemmas needed.

---

## Spec Quality Assessment

### Preconditions
- **`rb_new`**: trivially satisfiable (`emp`)
- **`rb_insert_v`**: requires `valid_rbtree tree 'ft`, satisfied after any
  prior insert or new call
- **`rb_search_v`**: `preserves valid_rbtree tree 'ft`, no extra requirements
- **`rb_delete_v`**: requires `valid_rbtree tree 'ft`, same as insert
- **`free_valid_rbtree`**: requires `valid_rbtree tree 'ft`, same as above

All preconditions are satisfiable in natural usage. **No issues found.**

### Postconditions
- **`rb_insert_v`**: Returns `valid_rbtree y (S.insert 'ft k)` and
  `S.mem k (S.insert 'ft k) = true` and `S.search (S.insert 'ft k) k == Some k`.
  The tree shape is completely determined by `S.insert`, and the search
  connection is directly established. **Fully precise.**
- **`rb_search_v`**: Returns `result == S.search 'ft k` with explicit
  membership implications. **Fully precise.**
- **`rb_delete_v`**: Returns `valid_rbtree y (S.delete 'ft k)` and
  `S.mem k (S.delete 'ft k) = false` and `S.search (S.delete 'ft k) k == None`.
  **Fully precise.**

### Verdict

The strengthened `Impl.fsti` specification is **complete and precise**:
- All preconditions are satisfiable
- All postconditions uniquely determine the output for any concrete input
- The search↔membership connection is directly exposed in postconditions
- Same-key insert/search and delete/search patterns require zero helper lemmas

---

## C Extraction and Concrete Execution (2026-03-22)

### Pipeline

The verified Pulse implementation is extracted to C and executed:

1. **F* → KReMLin (.krml):** `--codegen krml` extracts `Impl.fst`, `ImplTest.fst`, and
   `Main.fst` (plus `Spec.fst` for runtime types like `color` and `balance_case`).
2. **KReMLin → C:** `krml` with `-bundle 'CLRS.Ch13.RBTree.Main=CLRS.Ch13.RBTree.*'`
   bundles all chapter modules into a single C translation unit. A second bundle
   `-bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'` drops library/spec-only modules.
3. **C → executable:** `gcc` compiles the extracted C with karamel's `compat.h`
   (maps F\* mathematical integers to `int32_t`) and `prims.c` runtime.
4. **Run:** `test_main.c` calls `CLRS_Ch13_RBTree_Main_main()` which exercises the
   full test: create → insert 3,1,2 → search → delete 1 → search → free.

### Key Design Decisions

| Challenge | Solution |
|-----------|----------|
| Pulse `fn` exports marked `private` in .krml | Created `Main.fst` wrapper (no .fsti → function is public) |
| Spec `rbtree` inductive is recursive by value (invalid C struct) | Created `ImplTest.fsti` to hide pure spec test values `t0`–`t5` |
| Mathematical integers (`int`) in `rb_node.key` | `-add-include '"krml/internal/compat.h"'` maps to `int32_t` |
| `Prims_op_LessThan` etc. needed at link time | Link with `krmllib/dist/generic/prims.c` |
| Spec `color`/`balance_case` types needed at runtime | Include `Spec.krml` in bundle for `classify_runtime()` |

### Build Targets

```
make extract-c   # Extract to _output/CLRS_Ch13_RBTree_Main.c
make test-c      # Extract, compile, and run the test
```

### Result

```
$ make test-c
KRML            CLRS_Ch13_RBTree_Main
CC              test_rbtree
RUN             test_rbtree
RBTree test: starting
RBTree test: passed
```

**Status:** ✅ All operations (new, insert, search, delete, free) execute correctly
in C. The extracted code matches the verified Pulse implementation with zero
runtime errors. Memory is properly allocated (via `KRML_HOST_MALLOC`) and freed
(`KRML_HOST_FREE`).
