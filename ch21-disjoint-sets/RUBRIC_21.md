# Chapter 21: Disjoint Sets — Rubric Compliance

**Date:** 2025-07-24
**Source:** `RUBRIC.md` (canonical), `AUDIT_CH21.md` (existing audit)
**Verification status:** All 3 modules verify — zero admits, zero assumes

---

## Current File Inventory

| # | File | Lines | Rubric Role | Description |
|---|------|-------|-------------|-------------|
| 1 | `CLRS.Ch21.UnionFind.Spec.fst` | ~356 | **Spec** | Pure F\* specification: `uf_forest`, `pure_find` (total), `pure_union`, partition correctness (`pure_union_same_set`, `pure_union_other_set`), compression lemmas |
| 2 | `CLRS.Ch21.UnionFind.fst` | ~666 | **Impl** | Pulse implementation: `make_set`, `find_set` (two-pass full compression), `union` (by rank), bridge lemmas (`to_uf`, `to_nat_seq`) |
| 3 | `CLRS.Ch21.UnionFind.RankBound.fst` | ~677 | **Lemmas** (+ partial Complexity) | Rank bounds: `size ≥ 2^rank`, `rank ≤ ⌊log₂ n⌋`, `tree_height ≤ rank[root] ≤ log₂(n)` |

---

## Algorithms Covered

| CLRS Operation | CLRS §21.3 Pseudocode | AutoCLRS Function | File | Notes |
|---|---|---|---|---|
| **MAKE-SET(x)** | `x.p = x; x.rank = 0` | `make_set` | UnionFind.fst | Batch version: loop sets `parent[i]=i, rank[i]=0` for `i ∈ [0,n)`. Postcondition includes `Spec.uf_inv`. |
| **FIND-SET(x)** | `if x≠x.p then x.p = FIND-SET(x.p); return x.p` | `find_set` (+ `find_root_imp`, `compress_path`) | UnionFind.fst | Iterative two-pass: pass 1 finds root (read-only `find_root_imp`), pass 2 compresses all path nodes (`compress_path`). |
| **UNION(x,y)** | `LINK(FIND-SET(x), FIND-SET(y))` | `union` | UnionFind.fst | Union by rank. Uses read-only `find_root_imp` for both operands, then performs LINK logic. Returns `unit`. |

**Pure spec counterparts** (in Spec.fst): `pure_find` (total, termination via `count_above`), `pure_union` (union by rank on pure `uf_forest`).

---

## Rubric Compliance Matrix

| Rubric Artefact | Expected Name | Status | Actual File / Notes |
|---|---|---|---|
| **Spec.fst** | `CLRS.Ch21.UnionFind.Spec.fst` | ✅ Present | Complete pure model: `uf_forest`, total `pure_find`, `pure_union`, partition correctness, compression lemmas |
| **Lemmas.fst** | `CLRS.Ch21.UnionFind.Lemmas.fst` | 🔶 Name mismatch | `RankBound.fst` serves the Lemmas role — proves `size ≥ 2^rank`, `rank ≤ ⌊log₂ n⌋`, `tree_height ≤ rank[root]` |
| **Lemmas.fsti** | `CLRS.Ch21.UnionFind.Lemmas.fsti` | ❌ Missing | No interface file for lemma signatures |
| **Complexity.fst** | `CLRS.Ch21.UnionFind.Complexity.fst` | ❌ Missing | `RankBound.fst` contains logarithmic complexity results (`find_logarithmic_complexity`), but no dedicated Complexity file. Amortised O(α(n)) is not attempted. |
| **Complexity.fsti** | `CLRS.Ch21.UnionFind.Complexity.fsti` | ❌ Missing | No interface file for complexity signatures |
| **Impl.fst** | `CLRS.Ch21.UnionFind.Impl.fst` | 🔶 Name mismatch | `CLRS.Ch21.UnionFind.fst` is the Pulse implementation (not suffixed `.Impl`) |
| **Impl.fsti** | `CLRS.Ch21.UnionFind.Impl.fsti` | ❌ Missing | No public interface file for the imperative implementation |

### Summary Counts

| Status | Count | Items |
|--------|-------|-------|
| ✅ Fully compliant | 1 | Spec.fst |
| 🔶 Present, naming/structure mismatch | 2 | Lemmas.fst (as RankBound.fst), Impl.fst (no `.Impl` suffix) |
| ❌ Missing | 4 | Lemmas.fsti, Complexity.fst, Complexity.fsti, Impl.fsti |

---

## Detailed Action Items

### A1. Rename `RankBound.fst` → `Lemmas.fst` (or extract interface)

**Priority:** Medium
**Effort:** Low

`CLRS.Ch21.UnionFind.RankBound.fst` fulfils the Lemmas role. Either:
- Rename to `CLRS.Ch21.UnionFind.Lemmas.fst`, or
- Keep `RankBound.fst` and create a `Lemmas.fst` that re-exports its key results.

### A2. Create `Lemmas.fsti`

**Priority:** Medium
**Effort:** Low

Extract an interface file exposing the key lemma signatures:
- `rank_logarithmic_bound_sized`: `rank[x] ≤ ⌊log₂ n⌋`
- `height_le_root_rank`: `tree_height x ≤ rank[root(x)]`
- `find_logarithmic_complexity`: `tree_height x ≤ ⌊log₂ n⌋`
- `pure_union_sized_preserves_invariant`: size-rank invariant preservation

### A3. Create `Complexity.fst` + `Complexity.fsti`

**Priority:** Low (stretch goal)
**Effort:** High

Currently `RankBound.fst` proves the O(log n) worst-case bound. A dedicated Complexity module could:
1. Re-export the logarithmic bound from RankBound/Lemmas.
2. (Stretch) Formalise the amortised O(α(n)) bound using a potential function argument.

The amortised bound is mathematically deep (inverse Ackermann) and not attempted. The existing log₂(n) bound is already strong.

### A4. Rename implementation or add `.Impl` suffix

**Priority:** Low
**Effort:** Low

`CLRS.Ch21.UnionFind.fst` contains the Pulse implementation. The rubric expects `CLRS.Ch21.UnionFind.Impl.fst`. Either:
- Rename the file and update the module name, or
- Accept the current naming as a minor deviation (the `Spec` ↔ implementation split is clear).

### A5. Create `Impl.fsti`

**Priority:** Medium
**Effort:** Low–Medium

Extract a public interface exposing:
- `make_set`: signature with `Spec.uf_inv` postcondition
- `find_set`: signature with root-return + compression + `pure_find` equivalence postcondition
- `union`: signature with `is_forest` + `pure_find` merge postcondition

### A6. Strengthen implementation-level refinement (from audit)

**Priority:** Medium
**Effort:** Medium

Two specification gaps identified in AUDIT_CH21.md:
1. **`find_set` ↔ `pure_find` link:** `find_set` proves compression and root correctness, and the postcondition already states `root == Spec.pure_find(...)`. This is ✅ resolved.
2. **`union` partition correctness at imperative level:** The `union` postcondition proves `pure_find(result, x) == pure_find(result, y)` but does not prove stability (`pure_union_other_set` equivalent) at the imperative level. Adding this would close the refinement gap.

---

## Quality Checks

| Check | Status | Details |
|-------|--------|---------|
| **Zero admits** | ✅ | All 3 files: zero `admit()` |
| **Zero assumes** | ✅ | All 3 files: zero `assume(...)` |
| **Termination** | ✅ | `pure_find` terminates via `count_above` measure (no fuel). All loops have `decreases` clauses. |
| **Spec–Impl connection** | ✅ | `make_set` postcondition includes `Spec.uf_inv`. `find_set` postcondition links to `Spec.pure_find`. `union` postcondition links to `Spec.pure_find` merge. |
| **CLRS fidelity** | ✅ | All three CLRS §21.3 operations implemented faithfully (see Algorithms table above). |
| **Path compression** | ✅ | Full CLRS FIND-SET compression (two-pass iterative). `compress_preserves_find_all` proves all `pure_find` values preserved. |
| **Rank bound chain** | ✅ | `size ≥ 2^rank` → `rank ≤ ⌊log₂ n⌋` → `height ≤ rank[root] ≤ ⌊log₂ n⌋` — complete verified chain. |
| **No duplication** | ✅ | 3 files, consolidated architecture, no redundant definitions. |
| **`assert(False)` usage** | ✅ | Two occurrences, both in justified dead branches (see AUDIT_CH21.md §5). |
