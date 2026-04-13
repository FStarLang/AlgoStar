# Ch21 Disjoint Sets — C Spec vs Impl.fsti Review

## Overview

The C code (`union_find.c`) now proves both structural properties (parent bounds,
rank invariant) AND semantic connections to `Spec.pure_find` via `uf_inv` from
`CLRS.Ch21.UnionFind.Spec`. Bridge lemmas in `BridgeLemmas.fst` convert between
c2pulse's `Seq.seq (option SZ.t)` and the Spec's `Seq.seq nat` / `uf_forest` model.

Key technique: `(_slprop) _inline_pulse(with_pure(...))` annotations connect
c2pulse array ghost state (`array_value_of`) to Spec-level predicates.

---

## Per-Function Status

### 1. `make_set`

| Property | Impl.fsti | C code | Status |
|----------|-----------|--------|--------|
| parent[i] == i | ✓ | ✓ | ✅ |
| rank[i] == 0 | ✓ | ✓ | ✅ |
| uf_inv | ✓ | ✗ | ❌ c2pulse limitation |

**Note**: `uf_inv` cannot be expressed as a make_set postcondition because
`_ghost_stmt` observations are disconnected from `_ensures` observations in
c2pulse for modifying functions. The structural postconditions (parent[i]==i,
rank[i]==0) are logically equivalent to uf_inv for the identity forest.

### 2. `find_root` (helper for union_sets)

| Property | C code | Status |
|----------|--------|--------|
| return < n, parent[return]==return | ✓ | ✅ |
| arrays unchanged | ✓ | ✅ |
| uf_inv preserved | ✓ | ✅ NEW |
| return == pure_find(forest, x) | ✓ | ✅ NEW |

### 3. `find_set`

| Property | Impl.fsti | C code | Status |
|----------|-----------|--------|--------|
| return < n, root, parent[x]==return | ✓ | ✓ | ✅ |
| rank unchanged | ✓ | ✓ | ✅ |
| uf_inv preserved | ✓ | ✓ | ✅ NEW |
| return == pure_find(post-state, x) | ✓ | ✓ | ✅ NEW |
| pure_find preserved for all z | ✓ | ✗ | ❌ needs pre-state ref |

### 4. `link`

| Property | Impl.fsti | C code | Status |
|----------|-----------|--------|--------|
| parent[i]<n, rank monotonicity | ✓ | ✓ | ✅ |
| rank invariant preserved | ✓ | ✓ | ✅ |
| uf_inv preserved | ✓ | ✓ | ✅ NEW |
| Merge: pure_find(root_x)==pure_find(root_y) | ✓ | ✓ | ✅ NEW |
| Stability / Membership | ✓ | ✗ | ❌ needs pre-state ref |

### 5. `union_sets`

| Property | Impl.fsti | C code | Status |
|----------|-----------|--------|--------|
| parent[i]<n, rank invariant/mono | ✓ | ✓ | ✅ |
| uf_inv preserved | ✓ | ✓ | ✅ NEW |
| Merge: pure_find(x)==pure_find(y) | ✓ | ✗ | ❌ needs path chaining |
| Stability / Membership | ✓ | ✗ | ❌ needs pre-state ref |

---

## Limitations

Properties referencing BOTH pre-state and post-state forests cannot be expressed
in c2pulse annotations because `_old(array_value_of $(arr))` is not supported
in `_inline_pulse` contexts. This affects:
- pure_find preservation (find_set)
- Stability/membership (link, union_sets)
- union_sets merge (requires chaining through find_root's pre-state result)
