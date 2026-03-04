# Chapter 25: All-Pairs Shortest Paths — Rubric Compliance

**Algorithm:** Floyd-Warshall (CLRS §25.2)
**Directory:** `ch25-apsp/`
**Date:** 2025-07-15 (initial), 2026-03-04 (rubric compliance refactoring)
**Canonical rubric:** `../RUBRIC.md`

---

## Current File Inventory

| # | File | Lines | Rubric Role | Notes |
|---|------|------:|-------------|-------|
| 1 | `CLRS.Ch25.FloydWarshall.Spec.fst` | ~115 | **Spec** | Pure specification: `inf`, safety predicates, `fw_inner_j/i`, `fw_outer`, `fw_entry` recurrence, length lemmas |
| 2 | `CLRS.Ch25.FloydWarshall.Lemmas.fsti` | ~100 | **Lemmas interface** | Signatures for all correctness lemmas |
| 3 | `CLRS.Ch25.FloydWarshall.Lemmas.fst` | ~310 | **Lemmas** | Correctness proofs: `fw_outer ≡ fw_entry` (main theorem) |
| 4 | `CLRS.Ch25.FloydWarshall.Paths.fst` | ~131 | **Lemmas (extended)** | Walk formalism; base case `fw_entry` at k=0 equals direct-edge weight |
| 5 | `CLRS.Ch25.FloydWarshall.Complexity.fsti` | ~50 | **Complexity interface** | `fw_complexity_bounded` predicate and `floyd_warshall_complexity` signature |
| 6 | `CLRS.Ch25.FloydWarshall.Complexity.fst` | ~163 | **Complexity** | Ghost-tick proof of exactly n³ relaxation ops (Θ(V³)) |
| 7 | `CLRS.Ch25.FloydWarshall.Impl.fsti` | ~40 | **Impl interface** | `floyd_warshall` function signature with pre/postconditions |
| 8 | `CLRS.Ch25.FloydWarshall.Impl.fst` | ~110 | **Impl** | Pulse implementation proven equivalent to `fw_outer` |
| 9 | `CLRS.Ch25.FloydWarshall.SpecTest.fst` | ~57 | _(test)_ | Concrete 3×3 output verification via `fw_entry` + `floyd_warshall_computes_shortest_paths` |
| 10 | `CLRS.Ch25.FloydWarshall.Test.fst` | ~59 | _(test)_ | Pulse runtime smoke test (3×3 graph) |
| | **Total** | **~1135** | | Zero admits, zero assumes |

---

## Algorithms Covered

### Floyd-Warshall (CLRS §25.2, Equation 25.5)

| CLRS Element | Code Location | Status |
|---|---|---|
| Recurrence d^(k)[i][j] = min(d^(k−1)[i][j], d^(k−1)[i][k] + d^(k−1)[k][j]) | `fw_entry` in Spec.fst | ✅ Faithfully encoded (0-indexed) |
| Triple nested loop (k, i, j) | `fw_outer`/`fw_inner_i`/`fw_inner_j` in Spec.fst | ✅ |
| In-place update correctness | `lemma_fw_inner_i_preserves_row_k` in Lemmas.fst | ✅ Proven |
| Predecessor matrix (Π) | — | ❌ Not implemented |
| Negative-cycle detection | `non_negative_diagonal` precondition in Spec.fst | 🔶 Assumed, not detected at runtime |

---

## Rubric Compliance Matrix

The canonical rubric (`RUBRIC.md`) requires seven files per algorithm. The table below maps each required artifact to what exists.

| Rubric Artifact | Expected Name | Actual File(s) | Status | Gap |
|---|---|---|---|---|
| **Spec.fst** — Pure specification | `CLRS.Ch25.FloydWarshall.Spec.fst` | `Spec.fst` | ✅ | Pure spec with `fw_entry`, `fw_inner_j/i`, `fw_outer`, `inf`, safety predicates, length lemmas |
| **Lemmas.fst** — Correctness proofs | `CLRS.Ch25.FloydWarshall.Lemmas.fst` | `Lemmas.fst` (+ `Paths.fst` for walk formalism) | ✅ | Main theorem `fw_outer ≡ fw_entry` plus all supporting lemmas |
| **Lemmas.fsti** — Lemma signatures | `CLRS.Ch25.FloydWarshall.Lemmas.fsti` | `Lemmas.fsti` | ✅ | All public lemma signatures exposed |
| **Complexity.fst** — Complexity proofs | `CLRS.Ch25.FloydWarshall.Complexity.fst` | `Complexity.fst` | ✅ | Exact n³ ghost-tick proof |
| **Complexity.fsti** — Complexity interface | `CLRS.Ch25.FloydWarshall.Complexity.fsti` | `Complexity.fsti` | ✅ | `fw_complexity_bounded` and `floyd_warshall_complexity` signature |
| **Impl.fst** — Pulse implementation | `CLRS.Ch25.FloydWarshall.Impl.fst` | `Impl.fst` | ✅ | Pulse implementation with `fw_outer` postcondition |
| **Impl.fsti** — Implementation interface | `CLRS.Ch25.FloydWarshall.Impl.fsti` | `Impl.fsti` | ✅ | Public `floyd_warshall` signature with pre/postconditions |

### Summary Counts

| Status | Count | Artifacts |
|--------|------:|-----------|
| ✅ Fully compliant | 7 | Spec.fst, Lemmas.fst, Lemmas.fsti, Complexity.fst, Complexity.fsti, Impl.fst, Impl.fsti |
| 🔶 Present, non-conforming | 0 | — |
| ❌ Missing | 0 | — |

---

## Detailed Action Items

### A. Structural / Naming (rubric compliance)

| # | Action | Priority | Status | Details |
|---|--------|----------|--------|---------|
| A-1 | **Extract pure spec into `FloydWarshall.Spec.fst`** | Medium | ✅ Done | Pure spec (fw_entry, fw_inner_j/i, fw_outer, inf, safety predicates, length lemmas) in standalone Spec module |
| A-2 | **Rename old `Spec.fst` → `Lemmas.fst`** | Medium | ✅ Done | Correctness proofs now in `Lemmas.fst` with proper module name |
| A-3 | **Keep `Paths.fst` as supplementary lemmas** | Low | ✅ Done | Kept as separate walk-formalism file |
| A-4 | **Rename `FloydWarshall.fst` → `Impl.fst`** | Medium | ✅ Done | Pulse implementation in `Impl.fst`, opens `Spec` for pure definitions |
| A-5 | **Create `Lemmas.fsti`** | Medium | ✅ Done | All public lemma signatures exposed |
| A-6 | **Create `Complexity.fsti`** | Low | ✅ Done | `fw_complexity_bounded` and `floyd_warshall_complexity` signature |
| A-7 | **Create `Impl.fsti`** | Medium | ✅ Done | `floyd_warshall` function signature with full pre/postconditions |

### B. Proof / Specification Gaps

| # | Action | Priority | Effort | Details |
|---|--------|----------|--------|---------|
| B-1 | **Complete walk-based δ(i,j) proof** | High | High | `Paths.fst` has the base case (k=0). The inductive step is outlined as future work. No admits. |
| B-2 | **Predecessor matrix (Π)** | Low | Medium | CLRS §25.2 includes Π for path reconstruction. Not implemented. |

### C. Code Quality

| # | Action | Priority | Status | Details |
|---|--------|----------|--------|---------|
| C-1 | Guard infinity sentinel | — | ✅ Done | `weights_bounded` predicate in Spec.fst |
| C-2 | Non-negative diagonal precondition | — | ✅ Done | `non_negative_diagonal` predicate in Spec.fst |
| C-3 | Eliminate Complexity.fst duplication | — | ✅ Done | Uses `open CLRS.Ch25.FloydWarshall.Spec` |
| C-4 | Concrete assertions in SpecTest.fst | — | ✅ Done | All 9 entries verified + no-negative-cycle |
| C-5 | Fix README statistics | — | ✅ Done | rlimit values corrected, file table updated |

---

## Quality Checks

| Check | Result | Evidence |
|-------|--------|----------|
| **Zero admits** | ✅ | `grep -rn "admit" *.fst` — no matches |
| **Zero assumes** | ✅ | `grep -rn "assume" *.fst` — no matches |
| **All files verified** | ✅ | All 10 `.fst`/`.fsti` files verified successfully |
| **Solver limits modest** | ✅ | Max `z3rlimit 40` (two locations); no `--z3seed` hacks |
| **Fuel/ifuel reasonable** | ✅ | `--fuel 8 --ifuel 2` only in SpecTest.fst (concrete evaluation); defaults elsewhere |
| **No sorry/magic** | ✅ | Not present |
| **Functional correctness** | ✅ | Postcondition: `contents' == fw_outer contents (SZ.v n) 0` |
| **Recurrence correctness** | ✅ | `fw_outer` proven equivalent to `fw_entry` at level n |
| **Complexity proven** | ✅ | Exact n³ relaxation count via ghost ticks |
| **Graph-theoretic δ(i,j) connection** | 🔶 Partial | Base case proven (k=0); inductive step outlined as future work in `Paths.fst` |
| **CLRS fidelity** | ✅ High | Loop structure and recurrence match §25.2; 0-indexed shift handled correctly |
| **Test coverage** | ✅ | `SpecTest.fst` (9 entries, all levels) + `Test.fst` (Pulse runtime) |
| **Rubric compliance** | ✅ Full | All 7 required artifacts present with correct names |
