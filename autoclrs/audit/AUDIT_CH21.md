# Audit Report: Chapter 21 — Disjoint Sets (Union-Find)

**Date:** 2025-07-17 (revised 2025-07-24)
**Auditor:** Copilot (automated)
**Scope:** `ch21-disjoint-sets/` — 3 files, ~1500 total lines
**Verification status:** All 3 modules verify — **zero admits, zero assumes**

---

## 1. CLRS Fidelity

### CLRS §21.3 Pseudocode (reference)

| CLRS Operation | CLRS Pseudocode | AutoCLRS Implementation | Match? |
|---|---|---|---|
| **MAKE-SET(x)** | `x.p = x; x.rank = 0` | `make_set` (UnionFind.fst): loop sets `parent[i]=i, rank[i]=0` for `i ∈ [0,n)` | ✅ Faithful (batch version) |
| **FIND-SET(x)** (full compression) | `if x≠x.p then x.p = FIND-SET(x.p); return x.p` | `find_set` (UnionFind.fst): iterative two-pass (pass 1: find root; pass 2: compress all path nodes) | ✅ Faithful (iterative equivalent of CLRS recursive) |
| **LINK(x,y)** | `if x.rank > y.rank then y.p=x else x.p=y; if x.rank==y.rank then y.rank+=1` | `union` (UnionFind.fst): union by rank with internal find_root, returns unit | ✅ Faithful |
| **UNION(x,y)** | `LINK(FIND-SET(x), FIND-SET(y))` | `union` calls read-only `find_root_imp` for both operands, then performs LINK logic | ✅ Faithful |

### Fidelity Notes

1. **LINK convention:** CLRS LINK lines 4–5 increment the *surviving* root's rank when ranks are equal. In AutoCLRS, the equal-rank case attaches `root_y` under `root_x` and increments `rank[root_x]`. This matches CLRS, choosing `root_x` as survivor.

2. **Full path compression:** `find_set` performs full CLRS FIND-SET with two-pass iterative compression. All nodes on the path to root are set to point directly to root.

3. **Pure spec model:** `Spec.fst` provides total `pure_find` and `pure_union` as pure F* functions with partition correctness proofs. The `make_set` postcondition includes `Spec.uf_inv`.

**Fidelity verdict: ✅ High fidelity.** All three CLRS operations implemented with full path compression. `union` returns unit (not tuple).

---

## 2. Specification Strength

### What is proven

| Property | Where | Strength |
|---|---|---|
| **Total `pure_find`** | Spec.fst: `pure_find` with `count_above` termination | ✅ No fuel, no Option |
| **`pure_union_same_set`** | Spec.fst: after union, `pure_find f' x == pure_find f' y` | ✅ **Key theorem** — merge correctness |
| **`pure_union_other_set`** | Spec.fst: unrelated elements unchanged | ✅ **Key theorem** — stability |
| **`pure_union_preserves_inv`** | Spec.fst: invariant preservation | ✅ |
| **`make_set` produces `uf_inv`** | UnionFind.fst: postcondition includes `Spec.uf_inv` | ✅ |
| **`find_set` returns root, compresses** | UnionFind.fst: full compression postcondition | ✅ |
| **`union` preserves `is_forest`** | UnionFind.fst: `is_forest sp n` in postcondition | ✅ |
| **size ≥ 2^rank** | RankBound.fst | ✅ |
| **rank ≤ ⌊log₂ n⌋** | RankBound.fst | ✅ |
| **Tree height ≤ rank[root] ≤ log₂(n)** | RankBound.fst | ✅ |

### Specification Gaps

1. **`find_set` does not prove `pure_find` equivalence.** The postcondition guarantees compression and root correctness, but does not formally link the result to `Spec.pure_find`. This is a refinement gap.

2. **`union` does not prove partition correctness at imperative level.** The Spec proves `pure_union_same_set` and `pure_union_other_set`, but the imperative `union` only proves `is_forest` preservation — the partition equivalence is not threaded through.

**Specification strength verdict: ✅ Strong at spec level, moderate at implementation level.** The pure spec has full partition correctness. The imperative implementation proves structural safety (forest preservation, compression) but lacks the refinement link to the pure model.

---

## 3. Complexity Analysis

### What is proven

| Claim | File | Status |
|---|---|---|
| **Rank bound: rank[x] ≤ ⌊log₂ n⌋** | RankBound.fst | ✅ Verified |
| **size ≥ 2^rank** | RankBound.fst | ✅ Verified |
| **Tree height ≤ rank[root]** | RankBound.fst: `height_le_root_rank` | ✅ Verified |
| **Tree height ≤ log₂(n)** | RankBound.fst: `find_logarithmic_complexity` | ✅ Verified |
| **Amortised O(α(n))** | — | ❌ Not attempted |

**Complexity verdict: ✅ Strong.** The complete chain `tree_height ≤ rank[root] ≤ log₂(n)` is verified. Only the amortised inverse-Ackermann bound is absent.

---

## 4. Code Quality

### Strengths

- **Consolidated architecture:** 3 files (down from 6), no duplication
- **Pure spec separated from implementation:** `Spec.fst` (247 lines) is a complete pure model
- **`make_set` connected to spec:** postcondition includes `Spec.uf_inv`
- **Full path compression as the only find:** no half-measures
- **`union` returns unit:** matches CLRS (previously returned tuple)
- **Zero admits, zero assumes** across all modules

### Issues

1. **`union` uses read-only `find_root_imp` internally** instead of the compressing `find_set`. This is a pragmatic choice to avoid needing the "compression preserves other roots" proof, but means `union` does not compress paths.

2. **Rank overflow guard:** The equal-rank branch caps rank at `n-1`. Since `rank ≤ log₂(n) < n-1`, this guard never fires in valid states. Harmless but theoretically unnecessary.

**Code quality verdict: ✅ Good.** Clean consolidated codebase with no duplication.

---

## 5. Proof Quality

### Formal Search Results

Zero admits, zero assumes across all 3 files.

### `assert (False)` / `unreachable`

| File | Usage | Justified? |
|---|---|---|
| `UnionFind.fst` | Dead branch in `find_set` loop (fuel exhausted → root must be at current position) | ✅ Yes |
| `RankBound.fst` | Contradiction branch in `rank_logarithmic_bound_sized` | ✅ Yes |

**Proof quality verdict: ✅ Excellent.** Zero admits/assumes. All proof branches justified.

---

## 6. Summary

| Dimension | Score | Notes |
|---|---|---|
| CLRS Fidelity | **A** | All operations with full path compression |
| Specification Strength | **A−** | Full partition correctness at spec level; structural safety at impl level |
| Complexity | **A−** | Complete log₂(n) bound; only α(n) absent |
| Code Quality | **A** | Consolidated, no duplication, clean architecture |
| Proof Quality | **A** | Zero admits/assumes |

**Overall: A− — A clean, consolidated verified implementation with total pure_find, partition correctness proofs, full path compression, and logarithmic complexity bounds.**

---

*End of audit.*
