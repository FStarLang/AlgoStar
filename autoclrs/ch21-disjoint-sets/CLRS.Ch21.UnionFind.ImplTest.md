# Union-Find — Spec Validation Test

**File:** `CLRS.Ch21.UnionFind.ImplTest.fst`

## Test Instance

| Parameter | Value |
|-----------|-------|
| `n`       | `3` (elements: {0, 1, 2}) |
| Operations | `make_set(3)`, `find_set(0..2)`, `union(0,1)`, `find_set(0..2)` |

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

### 5. No admits, no assumes

The test is fully verified by F* and Z3 with no admits or assumes.

## Specification Improvements Made

### Union membership clause (FIXED)

**Problem:** The original `union` postcondition only guaranteed:
1. **Merge:** `pure_find(new, x) == pure_find(new, y)`
2. **Stability:** For `z` not in `x`'s or `y`'s class:
   `pure_find(new, z) == pure_find(old, z)`

It said nothing about elements *already in* `x`'s or `y`'s class. This
prevented multi-step union reasoning (e.g., after `union(0,1)` then
`union(1,2)`, could not prove `find(new, 0) == find(new, 2)`).

**Fix:** Added a membership clause to both the pure spec (`Spec.fst`) and
the imperative interface (`Impl.fsti`):

```fstar
// Membership: elements in x's or y's class join the merged class
(forall (z: nat). z < n ==>
  (pure_find(old, z) == pure_find(old, x) \/
   pure_find(old, z) == pure_find(old, y)) ==>
  pure_find(new, z) == pure_find(new, x))
```

New lemmas in `Spec.fst`:
- `pure_union_membership`: per-element version
- `pure_union_membership_all`: universally quantified version

The proof uses `pure_find_after_link` to show that linking root_a under
root_b maps all elements in either tree to root_b.

## Remaining Specification Gap

### Rank bound not preserved (postcondition weakness)

The `union` **precondition** requires `rank[i] < n` for all `i`. However,
the **postcondition** does not re-establish this bound for the output rank
array. In the equal-rank case, one rank is incremented (`rank[root_x] + 1`),
and proving `rank[root_x] + 1 < n` requires the logarithmic rank bound
from `Lemmas.fst` (which uses the size-rank invariant on `uf_forest_sized`,
not currently threaded through the imperative code).

**Impact:** The client cannot chain multiple `union` calls without
independently establishing the rank bound between calls. For a single
`union` on a fresh forest (as in this test), the bound follows trivially
from all-zero initial ranks.

**Severity:** Medium. The rank bound IS maintained in practice (proven in
the pure model in `Lemmas.fst`), but the imperative postcondition doesn't
expose it. Fixing this would require connecting the `uf_forest_sized` model
from `Lemmas.fst` to the imperative code.
