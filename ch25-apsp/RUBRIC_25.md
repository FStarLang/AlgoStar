# Chapter 25: All-Pairs Shortest Paths — Rubric Compliance

**Algorithm:** Floyd-Warshall (CLRS §25.2)
**Directory:** `ch25-apsp/`
**Date:** 2025-07-15
**Canonical rubric:** `../RUBRIC.md`

---

## Current File Inventory

| # | File | Lines | Rubric Role | Notes |
|---|------|------:|-------------|-------|
| 1 | `CLRS.Ch25.FloydWarshall.fst` | 208 | **Impl** + **Spec** (combined) | Pulse implementation _and_ pure mirror spec (`fw_inner_j`, `fw_inner_i`, `fw_outer`) + safety predicates (`weights_bounded`, `non_negative_diagonal`) + length lemmas |
| 2 | `CLRS.Ch25.FloydWarshall.Spec.fst` | 389 | **Lemmas** | Defines `fw_entry` recurrence; proves `fw_outer ≡ fw_entry` (main correctness theorem) |
| 3 | `CLRS.Ch25.FloydWarshall.Paths.fst` | 131 | **Lemmas** | Walk formalism; proves base case `fw_entry` at k=0 equals direct-edge weight; inductive step is TODO |
| 4 | `CLRS.Ch25.FloydWarshall.Complexity.fst` | 170 | **Complexity** | Ghost-tick proof of exactly n³ relaxation ops (Θ(V³)) |
| 5 | `CLRS.Ch25.FloydWarshall.SpecTest.fst` | 57 | _(test)_ | Concrete 3×3 output verification via `fw_entry` + `floyd_warshall_computes_shortest_paths` |
| 6 | `CLRS.Ch25.FloydWarshall.Test.fst` | 59 | _(test)_ | Pulse runtime smoke test (3×3 graph) |
| | **Total** | **1 014** | | Zero admits, zero assumes |

---

## Algorithms Covered

### Floyd-Warshall (CLRS §25.2, Equation 25.5)

| CLRS Element | Code Location | Status |
|---|---|---|
| Recurrence d^(k)[i][j] = min(d^(k−1)[i][j], d^(k−1)[i][k] + d^(k−1)[k][j]) | `fw_entry` in Spec.fst:28–37 | ✅ Faithfully encoded (0-indexed) |
| Triple nested loop (k, i, j) | `fw_outer`/`fw_inner_i`/`fw_inner_j` in FloydWarshall.fst:41–63 | ✅ |
| In-place update correctness | `lemma_fw_inner_i_preserves_row_k` in Spec.fst:200–240 | ✅ Proven |
| Predecessor matrix (Π) | — | ❌ Not implemented |
| Negative-cycle detection | `non_negative_diagonal` precondition in FloydWarshall.fst:30–33 | 🔶 Assumed, not detected at runtime |

---

## Rubric Compliance Matrix

The canonical rubric (`RUBRIC.md`) requires seven files per algorithm. The table below maps each required artifact to what exists.

| Rubric Artifact | Expected Name | Actual File(s) | Status | Gap |
|---|---|---|---|---|
| **Spec.fst** — Pure specification | `CLRS.Ch25.FloydWarshall.Spec.fst` | `FloydWarshall.fst` (lines 41–63: `fw_inner_j/i`, `fw_outer`) | 🔶 | Pure spec is embedded in the Impl file, not in a standalone Spec module. The file _named_ `Spec.fst` actually contains lemmas/proofs. |
| **Lemmas.fst** — Correctness proofs | `CLRS.Ch25.FloydWarshall.Lemmas.fst` | `FloydWarshall.Spec.fst` (389 lines) + `FloydWarshall.Paths.fst` (131 lines) | 🔶 | Content is present and thorough but under non-standard names. `Spec.fst` proves `fw_outer ≡ fw_entry`; `Paths.fst` provides walk-based graph-theoretic lemmas. |
| **Lemmas.fsti** — Lemma signatures | `CLRS.Ch25.FloydWarshall.Lemmas.fsti` | _(missing)_ | ❌ | No interface file exposes lemma signatures. |
| **Complexity.fst** — Complexity proofs | `CLRS.Ch25.FloydWarshall.Complexity.fst` | `FloydWarshall.Complexity.fst` (170 lines) | ✅ | Exact n³ ghost-tick proof. |
| **Complexity.fsti** — Complexity interface | `CLRS.Ch25.FloydWarshall.Complexity.fsti` | _(missing)_ | ❌ | No interface file for complexity definitions/signatures. |
| **Impl.fst** — Pulse implementation | `CLRS.Ch25.FloydWarshall.Impl.fst` | `FloydWarshall.fst` (208 lines) | 🔶 | File serves as Impl but is not named `Impl.fst`; also bundles pure spec and safety predicates. |
| **Impl.fsti** — Implementation interface | `CLRS.Ch25.FloydWarshall.Impl.fsti` | _(missing)_ | ❌ | No public interface file for the imperative entry point. |

### Summary Counts

| Status | Count | Artifacts |
|--------|------:|-----------|
| ✅ Fully compliant | 1 | Complexity.fst |
| 🔶 Present, non-conforming name/structure | 3 | Spec.fst, Lemmas.fst, Impl.fst |
| ❌ Missing | 3 | Lemmas.fsti, Complexity.fsti, Impl.fsti |

---

## Detailed Action Items

### A. Structural / Naming (to reach full rubric compliance)

| # | Action | Priority | Effort | Details |
|---|--------|----------|--------|---------|
| A-1 | **Extract pure spec into `FloydWarshall.Spec.fst`** | Medium | Low | Move `fw_inner_j`, `fw_inner_i`, `fw_outer`, `fw_entry`, `inf`, safety predicates, and length lemmas out of the current `FloydWarshall.fst` into a true `Spec.fst`. The current `Spec.fst` content (correctness proofs) should be renamed to `Lemmas.fst`. |
| A-2 | **Rename current `Spec.fst` → `Lemmas.fst`** | Medium | Low | The file currently named `Spec.fst` contains lemma proofs, not the pure specification. Rename to align with rubric. |
| A-3 | **Merge or rename `Paths.fst`** | Low | Low | `Paths.fst` plays a Lemmas role. Either merge into `Lemmas.fst` or keep as a sub-module (`Lemmas.Paths.fst`). |
| A-4 | **Rename `FloydWarshall.fst` → `FloydWarshall.Impl.fst`** | Medium | Low | After extracting the pure spec (A-1), the remaining Pulse code should be named `Impl.fst` per rubric. |
| A-5 | **Create `Lemmas.fsti`** | Medium | Low | Extract top-level lemma signatures (`floyd_warshall_computes_shortest_paths`, `fw_outer_computes_entry`, `lemma_fw_entry_k0_is_shortest`) into an interface. |
| A-6 | **Create `Complexity.fsti`** | Low | Low | Extract `fw_complexity_bounded` definition and `floyd_warshall_complexity` signature into an interface. |
| A-7 | **Create `Impl.fsti`** | Medium | Low | Extract the `floyd_warshall` function signature (pre/postconditions) into a public interface. |

### B. Proof / Specification Gaps

| # | Action | Priority | Effort | Details |
|---|--------|----------|--------|---------|
| B-1 | **Complete walk-based δ(i,j) proof** | High | High | `Paths.fst` has the base case (k=0). The inductive step (walk decomposition/composition at vertex k−1, optimality) is outlined but unimplemented. Completing this would upgrade spec strength to full graph-theoretic correctness. |
| B-2 | **Predecessor matrix (Π)** | Low | Medium | CLRS §25.2 includes Π for path reconstruction. Currently not implemented. Deferred per audit. |

### C. Code Quality

| # | Action | Priority | Status | Details |
|---|--------|----------|--------|---------|
| C-1 | Guard infinity sentinel | — | ✅ Done | `weights_bounded` predicate added. |
| C-2 | Non-negative diagonal precondition | — | ✅ Done | `non_negative_diagonal` predicate added. |
| C-3 | Eliminate Complexity.fst duplication | — | ✅ Done | Now uses `open CLRS.Ch25.FloydWarshall`. |
| C-4 | Concrete assertions in SpecTest.fst | — | ✅ Done | All 9 entries verified + no-negative-cycle. |
| C-5 | Fix README statistics | — | ✅ Done | rlimit values corrected. |

---

## Quality Checks

| Check | Result | Evidence |
|-------|--------|----------|
| **Zero admits** | ✅ | `grep -rn "admit" *.fst` — no matches (only in comments stating "NO admits") |
| **Zero assumes** | ✅ | `grep -rn "assume" *.fst` — no matches (only in comments stating "NO assumes") |
| **All .checked files present** | ✅ | Six `.checked` files in `_cache/` |
| **Solver limits modest** | ✅ | Max `z3rlimit 40` (two locations); no `--z3seed` hacks |
| **Fuel/ifuel reasonable** | ✅ | `--fuel 8 --ifuel 2` only in SpecTest.fst (concrete evaluation); defaults elsewhere |
| **No sorry/magic** | ✅ | Not present |
| **Functional correctness** | ✅ | Postcondition: `contents' == fw_outer contents (SZ.v n) 0` |
| **Recurrence correctness** | ✅ | `fw_outer` proven equivalent to `fw_entry` at level n |
| **Complexity proven** | ✅ | Exact n³ relaxation count via ghost ticks |
| **Graph-theoretic δ(i,j) connection** | 🔶 Partial | Base case proven (k=0); inductive step outlined as future work in `Paths.fst` |
| **CLRS fidelity** | ✅ High | Loop structure and recurrence match §25.2; 0-indexed shift handled correctly |
| **Test coverage** | ✅ | `SpecTest.fst` (9 entries, all levels) + `Test.fst` (Pulse runtime) |
