# Union-Find — Spec Validation Test

**File:** `CLRS.Ch21.UnionFind.ImplTest.fst`

## Test Instance

| Parameter | Value |
|-----------|-------|
| `n`       | `3` (elements: {0, 1, 2}) |
| Operations | `make_set(3)`, `find_set(0..2)`, `union(0,1)`, `find_set(0..2)`, `union(1,2)`, `find_set(0..2)` |

## What Is Proven

### 1. Precondition satisfiability

`make_set` precondition (`n > 0`, array lengths ≥ `n`, sequence lengths match
array lengths) is established structurally via `A.pts_to_len` and the vector
allocation sizes.

`find_set` preconditions (`is_forest`, `x < n`, `uf_inv`) are chained from
`make_set` and prior `find_set` postconditions.

`union` preconditions (`is_forest`, `x < n`, `y < n`, `uf_inv`,
`rank[i] < n` for all `i`) are satisfied because all ranks are initially 0
and `0 < 3`.

### 2. Postcondition precision — fresh forest

After `make_set`, the test proves that `find_set(i)` returns `i` for each
`i ∈ {0, 1, 2}`. This is established by the pure helper lemma
`fresh_forest_find`, which shows:

> If `uf_inv` holds and all ranks are 0, then `pure_find(forest, x) == x`.

**Proof sketch:** `rank_invariant` says non-root `x` has `rank[x] < rank[parent[x]]`.
With all ranks 0, this gives `0 < 0`, contradiction. So every element is a root,
and `pure_find_root` gives `pure_find(x) == x`.

The postcondition of `find_set` gives `root == pure_find(original_forest, x)`,
which equals `x` by the lemma. The test asserts `SZ.v r0 == 0`, `SZ.v r1 == 1`,
`SZ.v r2 == 2` — all verified by Z3.

### 3. Postcondition precision — union merge

After `union(0, 1)`, the test calls `find_set(0)` and `find_set(1)` and
asserts `SZ.v r0' == SZ.v r1'`. This follows from:

- Union postcondition: `pure_find(new, 0) == pure_find(new, 1)`
- `find_set` postcondition: `root == pure_find(forest, x)` and all
  `pure_find` values are preserved across path compression

### 4. Postcondition precision — union stability

After `union(0, 1)`, the test calls `find_set(2)` and asserts `SZ.v r2' == 2`.
This follows from:

- Union stability: for `z` with `pure_find(old, z) ≠ pure_find(old, 0)` and
  `pure_find(old, z) ≠ pure_find(old, 1)`, then `pure_find(new, z) == pure_find(old, z)`
- Element 2 satisfies both conditions (`pure_find(old, 2) == 2 ≠ 0` and `2 ≠ 1`)
- So `pure_find(new, 2) == pure_find(old, 2) == 2`

### 5. Chained union — transitivity via rank bounds

After `union(0, 1)`, the test calls `union(1, 2)` and then proves all three
elements end up in the same equivalence class: `find(0) == find(1) == find(2)`.

**Rank bound chaining:** The second `union` call requires the precondition
`rank[i] < n` for all `i`. This is proven using the rank bound postcondition
added to `union`:

- `rank[i] <= rank_old[i] + 1` (rank increases by at most 1)
- `rank_old[i] == 0` (from make_set, ranks unchanged by find_set)
- Therefore `rank[i] <= 1 < 3 = n` ✓

**Transitivity via membership:** After `union(1, 2)`:

- **Merge:** `find(new, 1) == find(new, 2)` — direct from merge clause.
- **Membership:** Element 0 was in element 1's class after the first union
  (`pure_find(old, 0) == pure_find(old, 1)`). By the membership clause,
  `find(new, 0) == find(new, 1)`.
- **Transitivity:** `find(0) == find(1) == find(2)` — all three in one class.

This test validates:
1. The rank bound postcondition enables chaining multiple `union` calls.
2. The membership clause enables reasoning about elements that were already
   merged by prior unions.
3. Together, they enable multi-step union-find reasoning on concrete instances.

### 6. No admits, no assumes

The test is fully verified by F* and Z3 with no admits or assumes.

## Specification Improvements Made

### Union rank bound clauses (NEW)

**Problem:** The original `union` postcondition said nothing about output ranks.
This prevented chaining multiple `union` calls because the caller could not
re-establish the `rank[i] < n` precondition for the next union.

**Fix:** Added two rank bound clauses to `union`'s postcondition in `Impl.fsti`:

```fstar
// Rank monotonicity: output ranks >= input ranks
(forall (i: nat). i < SZ.v n /\ i < Seq.length sr /\ i < Seq.length srank ==>
  SZ.v (Seq.index sr i) >= SZ.v (Seq.index srank i)) /\
// Rank bound: output ranks increase by at most 1
(forall (i: nat). i < SZ.v n /\ i < Seq.length sr /\ i < Seq.length srank ==>
  SZ.v (Seq.index sr i) <= SZ.v (Seq.index srank i) + 1)
```

The proof in `Impl.fst` is automatic: in each case of the union (same root,
different rank, equal rank), the rank changes are straightforward:
- Same root or different rank: no rank changes.
- Equal rank: exactly one rank increases by 1; all others unchanged.

### Union membership clause (prior improvement)

**Problem:** The original `union` postcondition only guaranteed merge and stability.
It said nothing about elements *already in* `x`'s or `y`'s class.

**Fix:** Added a membership clause to both the pure spec (`Spec.fst`) and
the imperative interface (`Impl.fsti`):

```fstar
// Membership: elements in x's or y's class join the merged class
(forall (z: nat). z < n ==>
  (pure_find(old, z) == pure_find(old, x) \/
   pure_find(old, z) == pure_find(old, y)) ==>
  pure_find(new, z) == pure_find(new, x))
```

## Remaining Specification Gap

### Rank bound not fully preserved (postcondition weakness)

The rank bound clauses show that each rank increases by at most 1, but do NOT
re-establish the `rank[i] < n` precondition directly. For a sequence of `k`
unions starting from a fresh forest (all ranks 0), the maximum rank after `k`
unions is at most `k`. Since at most `n-1` unions are meaningful (after which
all elements are in one class), the maximum rank is at most `n-1 < n`, so the
precondition is re-establishable in practice.

However, proving the tighter bound `rank[i] <= ⌊log₂ n⌋` (which is always
maintained by union-by-rank) requires threading the size-rank invariant from
`Lemmas.fst` through the imperative code. This stronger bound remains
unformalized at the imperative level.

**Impact:** Clients can chain unions on fresh forests (as demonstrated by the
test), but the proof effort grows with the number of unions because the rank
bound degrades by 1 per union. The logarithmic bound would eliminate this
degradation.

## Concrete Execution Results

The verified Pulse code has been successfully extracted to C and executed.

### Extraction Pipeline

1. **F* → KreMLin (.krml):** Pulse modules `ImplTest` and `Impl` extracted via
   `--codegen krml` with the Pulse extraction plugin.
2. **KreMLin → C:** `krml` translates the intermediate representation to C,
   bundling `CLRS.Ch21.UnionFind.*` into a single translation unit.
3. **C Compilation:** Standard C compiler (gcc/clang) with krmllib headers.
4. **Execution:** The compiled binary runs `test_union_find()` which exercises
   all three operations (make_set, find_set, union) on a 3-element forest.

### Build & Run

```
$ make test-c
EXTRACT  CLRS.Ch21.UnionFind.ImplTest
EXTRACT  CLRS.Ch21.UnionFind.Impl
KRML     CLRS_Ch21_UnionFind_ImplTest
CC       test_union_find
RUN      test_union_find
=== Union-Find C Extraction Test ===

Running verified test_union_find()... OK

All tests passed.
```

### Generated C Code Summary

The extracted C code contains:
- `make_set`: initializes parent and rank arrays (while loop)
- `find_root_imp`: read-only root traversal (while loop)
- `compress_path`: path compression from node to root (while loop)
- `find_set`: two-pass find (find root, then compress)
- `union0`: union by rank (find roots, link by rank comparison)
- `test_union_find`: allocates arrays, runs make_set → find_set × 3 →
  union(0,1) → find_set × 3 → union(1,2) → find_set × 3 → free

All ghost/spec code (assertions, rewrites, lemma calls, sequence operations)
is properly erased during extraction. The C code uses `size_t` for all values,
heap-allocated arrays (`KRML_HOST_CALLOC`/`KRML_HOST_FREE`), and contains
no unbounded data types.

### Status

✅ **F* verification:** All modules verify with no admits or assumes.
✅ **C extraction:** Clean extraction via karamel with no warnings in generated code.
✅ **C compilation:** Compiles with `-Wall` and no warnings (unused variables suppressed).
✅ **Execution:** Test completes successfully with exit code 0.
