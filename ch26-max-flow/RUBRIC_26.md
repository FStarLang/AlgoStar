# Chapter 26: Maximum Flow — Rubric Compliance

**Date**: 2025-07-18 (updated 2026-03-04)
**Canonical rubric**: `../RUBRIC.md`
**Audit reference**: `../AUDIT_CH26.md`
**Verification status**: All 10 `.checked` files present in `_cache/` (6 `.fst` + 4 `.fsti`)

---

## Current File Inventory

| # | File | Lines | Rubric Role | Verified |
|---|------|------:|-------------|:--------:|
| 1 | `CLRS.Ch26.MaxFlow.Spec.fst` | 341 | **Spec** — Pure specification: flow networks, residual graphs, augmenting paths, cuts | ✅ |
| 2 | `CLRS.Ch26.MaxFlow.Lemmas.fsti` | — | **Lemmas interface** — Public API for augmentation lemmas | ✅ |
| 3 | `CLRS.Ch26.MaxFlow.Lemmas.fst` | 679 | **Lemmas** — Augmentation preserves validity, increases flow value | ✅ |
| 4 | `CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut.fsti` | — | **MFMC interface** — Public API for MFMC theorem | ✅ |
| 5 | `CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut.fst` | 804 | **MFMC** — Weak duality, strong duality (CLRS Theorem 26.6) | ✅ |
| 6 | `CLRS.Ch26.MaxFlow.Complexity.fsti` | — | **Complexity interface** — Public API for complexity theorems | ✅ |
| 7 | `CLRS.Ch26.MaxFlow.Complexity.fst` | 618 | **Complexity** — O(VE²) bound with ghost tick counter | ✅ |
| 8 | `CLRS.Ch26.MaxFlow.Impl.fsti` | — | **Impl interface** — Public API for `max_flow` + bridge lemma | ✅ |
| 9 | `CLRS.Ch26.MaxFlow.Impl.fst` | ~1800 | **Impl** — Imperative Pulse implementation: BFS-based Ford-Fulkerson (Edmonds-Karp) | ✅ |
| 10 | `CLRS.Ch26.MaxFlow.Test.fst` | 61 | Test — Smoke test on 3-vertex graph | ✅ |
| | **Total** | **~4200** | | |

---

## Algorithms Covered

### Edmonds-Karp (Ford-Fulkerson with BFS) — CLRS §26.2–26.3

| CLRS Pseudocode Step | Implementation | Location |
|-----------------------|---------------|----------|
| **FORD-FULKERSON** line 1: init flow to 0 | `zero_init_flow flow nn` | MaxFlow.fst |
| **FORD-FULKERSON** line 2: while ∃ augmenting path in G_f | `bfs_residual` returns `found: bool` | MaxFlow.fst |
| **FORD-FULKERSON** line 3: augment flow along path | `find_bottleneck_imp` + `augment_imp` | MaxFlow.fst |
| **FORD-FULKERSON** line 4: return f | Returns `valid: bool` + flow in array | MaxFlow.fst |
| BFS shortest-path selection (Edmonds-Karp) | Standard BFS with queue, color, predecessor arrays | MaxFlow.fst `bfs_residual` |

**Spec-level variants** (Spec.fst):
- `ford_fulkerson` (line 203): explicit path-list functional specification
- `ford_fulkerson_fuel` (line 215): oracle + fuel iterative model

---

## Rubric Compliance Matrix

The canonical rubric (`RUBRIC.md`) requires the following file structure per algorithm:

| Rubric File | Expected Name | Actual File | Status | Notes |
|-------------|---------------|-------------|:------:|-------|
| `Spec.fst` | `CLRS.Ch26.MaxFlow.Spec.fst` | `CLRS.Ch26.MaxFlow.Spec.fst` | ✅ | 1125 lines, pure spec, zero admits |
| `Lemmas.fst` | `CLRS.Ch26.MaxFlow.Lemmas.fst` | `CLRS.Ch26.MaxFlow.Lemmas.fst` | ✅ | Renamed from Proofs.fst |
| `Lemmas.fsti` | `CLRS.Ch26.MaxFlow.Lemmas.fsti` | `CLRS.Ch26.MaxFlow.Lemmas.fsti` | ✅ | Created — exports key lemma signatures |
| `Complexity.fst` | `CLRS.Ch26.MaxFlow.Complexity.fst` | `CLRS.Ch26.MaxFlow.Complexity.fst` | 🔶 | Present, but contains 4 `assume val` axioms |
| `Complexity.fsti` | `CLRS.Ch26.MaxFlow.Complexity.fsti` | `CLRS.Ch26.MaxFlow.Complexity.fsti` | ✅ | Created — exports complexity theorem signatures |
| `Impl.fst` | `CLRS.Ch26.MaxFlow.Impl.fst` | `CLRS.Ch26.MaxFlow.Impl.fst` | 🔶 | Renamed from MaxFlow.fst; **1 `admit()` remains** (augment_imp_preserves_valid). BFS completeness fully proven. |
| `Impl.fsti` | `CLRS.Ch26.MaxFlow.Impl.fsti` | `CLRS.Ch26.MaxFlow.Impl.fsti` | ✅ | Created — exports `max_flow` public API |

### Proof Soundness Inventory

| # | File | Line | Construct | Severity | Context |
|---|------|-----:|-----------|:--------:|---------|
| **1** | **Impl.fst** | **842** | **`admit ()`** | **🔴 CRITICAL** | `lemma_augment_imp_preserves_valid` — asserts `imp_valid_flow` without proof |
| 2 | Test.fst | 47 | `assume_` | 🟡 Medium | Assumes `valid_caps` after manual array writes; test-only |
| 3 | Complexity.fst | 55 | `assume val` | 🟡 Medium | `axiom_spd_source_zero` — SPD source = 0 |
| 4 | Complexity.fst | 64 | `assume val` | 🟡 Medium | `axiom_spd_bounded` — SPD bounded by n−1 |
| 5 | Complexity.fst | 75 | `assume val` | 🟠 High | `lemma_distances_nondecreasing` — CLRS Lemma 26.7 |
| 6 | Complexity.fst | 342 | `assume val` | 🟠 High | `axiom_edge_critical_bound` — CLRS Lemma 26.8 |

**Eliminated** (previously present, now proven):
- ~~`assume val axiom_bfs_complete`~~ → Replaced by `lemma_bfs_complete` + `lemma_bottleneck_crossing` (proven by induction on path structure)
- ~~`assume_ (bfs_complete ...)`~~ → Eliminated via BFS loop counting invariant (`count_color1 == vtail - vhead`, `queue_color1`)
- ~~`assume_ (source colored)`~~ → Follows directly from BFS loop invariant

**Vacuous proofs** (accepted by F\* but logically trivial):

| # | File | Line | Function | Issue |
|---|------|-----:|----------|-------|
| 1 | Complexity.fst | ~40 | `shortest_path_distance` | Defined as constant (0 if source, else n); independent of flow |
| 2 | Complexity.fst | ~299 | `lemma_edge_critical_bound` | Now `assume val`; was formerly postcondition `True` |
| 3 | Complexity.fst | ~357 | `max_augmentations` | Defined directly as `V * E`; not derived from criticality bound |

### Theorem Coverage

| CLRS Result | Location | Status |
|-------------|----------|:------:|
| Lemma 26.4: \|f\| = net flow across any cut | Lemmas.MaxFlowMinCut.fst:262 | ✅ Proven |
| Corollary 26.5: Weak duality \|f\| ≤ c(S,T) | Lemmas.MaxFlowMinCut.fst:276 | ✅ Proven |
| Theorem 26.6: Max-flow min-cut | Lemmas.MaxFlowMinCut.fst:755 | ✅ Proven |
| Lemma 26.7: Distances non-decreasing | Complexity.fst:75 | ❌ `assume val` |
| Theorem 26.8: O(VE²) complexity | Complexity.fst:313 | 🔶 Arithmetic proven; key lemmas axiomatized |
| Augmentation preserves valid flow | Lemmas.fst:628 | ✅ Proven |
| Augmentation increases flow value | Lemmas.fst:656 | ✅ Proven |
| Zero flow is valid | Lemmas.fst:672 | ✅ Proven |
| Path shortening (pigeonhole) | Lemmas.MaxFlowMinCut.fst | ✅ Proven |
| imp_valid_flow ⟹ valid_flow (bridge) | Impl.fst | ✅ Proven |
| max_flow returns `completed` + no_augmenting_path | Impl.fst/fsti | ✅ Postcondition (via proven lemma_bfs_complete) |
| BFS completeness: bfs_complete ⟹ no_augmenting_path | Impl.fst | ✅ Proven (lemma_bottleneck_crossing, induction on path) |
| BFS termination ⟹ bfs_complete | Impl.fst | ✅ Proven (counting invariant: count_color1 + queue_color1) |

---

## Detailed Action Items

### 🔴 P0 — CRITICAL: Eliminate `admit()` in Production Code

**File**: `CLRS.Ch26.MaxFlow.Impl.fst`, line 842
**Function**: `lemma_augment_imp_preserves_valid`
**Current code**:
```fstar
let lemma_augment_imp_preserves_valid (flow_seq cap_seq: Seq.seq int) (n source sink: nat)
  : Lemma (ensures imp_valid_flow flow_seq cap_seq n source sink)
  = admit ()
```

**Impact**: This `admit()` is the **only** one in production code across all chapters. It allows the postcondition `imp_valid_flow` to be asserted without proof, meaning the static guarantee that the imperative implementation produces a valid flow is **unsound**. The implementation compensates with a runtime validity check (`check_imp_valid_flow_fn`), but the formal verification chain is broken at this point.

**Remediation plan** (from module header comments, lines 32–36):
1. **Prove BFS path correctness**: Show `bfs_residual` produces a valid augmenting path — i.e., returned `pred` array encodes a path with distinct vertices, bounded within `[0, n)`, from source to sink in the residual graph.
2. **Prove bottleneck correspondence**: Show `find_bottleneck_imp` computes `bn ≤ spec-level bottleneck(cap, flow, path)`.
3. **Prove augmentation refinement**: Show `augment_imp` refines `Spec.augment_aux` — i.e., the imperative updates to the flow array produce the same sequence as the pure-spec `augment`.
4. **Compose with `Proofs.augment_preserves_valid`**: Chain steps 1–3 with the already-proven pure lemma to discharge the obligation.

**Interim mitigation**: The runtime check `check_imp_valid_flow_fn` provides defense-in-depth — if the implementation has a bug, the caller sees `valid = false`. This limits blast radius but does not constitute a proof.

**Estimated complexity**: High. BFS correctness alone (step 1) is a substantial proof effort (task P3.1 in audit).

---

### 🟠 P1 — HIGH: Axiomatize or Prove Complexity Lemmas

| ID | Task | File:Line | Detail |
|----|------|-----------|--------|
| P1.1 | Prove CLRS Lemma 26.7 (distance monotonicity) | Complexity.fst:77 | Currently `assume val`. Requires BFS correctness proof (P3.1). Replace `shortest_path_distance` with a proper BFS distance abstraction and prove non-vacuously. |
| P1.2 | Prove CLRS Lemma 26.8 (edge criticality bound) | Complexity.fst:344 | Currently `assume val`. Depends on Lemma 26.7 + `axiom_spd_bounded`. Prove each edge becomes critical ≤ V/2 times. |
| P1.3 | Derive `max_augmentations` from criticality | Complexity.fst:357 | Currently defined directly as `V * E`. Should be derived from `lemma_augmentation_creates_critical_edge` + `axiom_edge_critical_bound`. |
| P1.4 | Prove `axiom_spd_source_zero` and `axiom_spd_bounded` | Complexity.fst:57,66 | Standard BFS properties; provable once BFS correctness is established. |

---

### 🟡 P2 — MEDIUM: Structural & Naming Compliance

| ID | Task | Detail | Status |
|----|------|--------|:------:|
| P2.1 | Rename `Proofs.fst` → `Lemmas.fst` | Rubric requires "Lemmas" not "Proofs". Updated all references. | ✅ Done |
| P2.2 | Rename `MaxFlow.fst` → `Impl.fst` | Rubric requires "Impl". Updated all references. | ✅ Done |
| P2.3 | Create `Lemmas.fsti` | Interface file with lemma signatures + helper lemmas used by Complexity. | ✅ Done |
| P2.4 | Create `Complexity.fsti` | Interface file with complexity definitions and theorem signatures. | ✅ Done |
| P2.5 | Create `Impl.fsti` | Public interface for `max_flow`, `valid_caps`, `imp_valid_flow`, `check_valid_caps_fn`. | ✅ Done |
| P2.6 | Strengthen main loop invariant | `max_flow` while-loop should carry `imp_valid_flow` (or weaker precursor) to remove runtime-check dependency | ⬜ Open |
| P2.7 | Add termination proof for main loop | Natural decreasing measure: `max_flow_value - current_flow_value` (bounded, decreases by ≥1 per iteration for integer capacities) | ⬜ Open |
| P2.8 | Eliminate `assume_` in test | Test.fst:47 — either prove `valid_caps` from the array writes or replace with a runtime check that produces the proof | ⬜ Open |

---

### 🟢 P3 — LOW: Polish

| ID | Task | Detail | Status |
|----|------|--------|:------:|
| P3.1 | Replace INT_MAX magic number | `find_bottleneck_imp` uses literal `2147483647`; replaced with named constant `int_max` | ✅ Done |
| P3.2 | Rewrite README.md | Updated to document current 8-file Edmonds-Karp implementation with Lemmas/Impl naming | ✅ Done |
| P3.3 | Add diverse test cases | Single 3-vertex smoke test; add edge cases (disconnected graph, zero-capacity edges, single edge, large fan-out) | ⬜ Open |

---

## Quality Checks

### Soundness Summary

| Dimension | Status | Detail |
|-----------|:------:|--------|
| **Zero `admit` in spec/lemmas** | ✅ | Spec.fst (1125 lines) and Lemmas.fst (679 lines) are fully proven |
| **Zero `admit` in complexity** | 🔶 | No `admit`, but 4 `assume val` axioms pending BFS correctness |
| **Zero `admit` in impl** | ❌ | **1 `admit()` at Impl.fst:842** — `lemma_augment_imp_preserves_valid` |
| **Zero `assume_` in production** | ✅ | All BFS `assume_` eliminated; only test `assume_` remains |
| **All files verified (.checked)** | ✅ | 10/10 `.checked` files in `_cache/` (6 `.fst` + 4 `.fsti`) |
| **MFMC theorem proven** | ✅ | Lemmas.MaxFlowMinCut.fst:755, constructive (2)⟹(3) direction of Theorem 26.6 |
| **Flow conservation proven** | ✅ | Lemmas.fst:628, for all augmentations on valid simple paths |
| **O(VE²) bound proven** | 🔶 | Arithmetic correct; depends on 4 axiomatized lemmas |

### Rubric Conformance Summary

| Criterion | Score | Notes |
|-----------|:-----:|-------|
| Spec file present & correct | ✅ | Pure definitions only (341 lines) |
| Lemmas file present | ✅ | Renamed from Proofs.fst to Lemmas.fst |
| Lemmas interface (.fsti) | ✅ | Created with key lemma + helper signatures |
| MFMC theorem in Lemmas | ✅ | Extracted to Lemmas.MaxFlowMinCut.fst/fsti (804 lines) |
| Complexity file present | 🔶 | Present; 4 `assume val` axioms |
| Complexity interface (.fsti) | ✅ | Created with theorem signatures |
| Impl file present | 🔶 | Renamed from MaxFlow.fst to Impl.fst; **has `admit()`** |
| Impl interface (.fsti) | ✅ | Created with `max_flow` public API |
| imp_valid_flow ↔ valid_flow | ✅ | Bridge lemma connects Impl postcondition to Spec.valid_flow |
| MFMC usable by callers | ✅ | `max_flow` returns `completed: bool`; when true, `no_augmenting_path` in postcondition enables MFMC |
| No admits in production | ❌ | **1 admit at Impl.fst:355** |
| Documentation accurate | ✅ | README updated to reflect current file structure |

### Overall Rating

| Dimension | Rating |
|-----------|--------|
| CLRS Fidelity | ★★★★☆ |
| Specification Strength | ★★★★★ |
| Complexity Proofs | ★★★☆☆ |
| Code Quality | ★★★★☆ |
| Proof Quality (Spec+Lemmas) | ★★★★★ |
| Proof Quality (Impl) | ★★★★☆ |
| Rubric Structural Compliance | ★★★★★ |
| Documentation | ★★★★★ |

**Bottom line**: Excellent pure-spec proofs (MFMC, conservation, augmentation — all zero-admit). MFMC theorem now isolated in Lemmas.MaxFlowMinCut with clean interface. Bridge lemma (`imp_valid_flow_implies_valid_flow`) connects Impl postcondition to `Spec.valid_flow`, enabling callers to use MFMC theorem results. `max_flow` returns `completed: bool` — when `true`, the postcondition includes `no_augmenting_path`, which is exactly the MFMC precondition. This makes the full theorem chain usable: `max_flow` → bridge lemma → `valid_flow` + `no_augmenting_path` → MFMC → max flow = min cut. **BFS completeness is fully proven**: counting invariants (`count_color1`, `queue_color1`, `queue_prefix_preserved`) track the BFS queue state through maybe_discover → bfs_explore_neighbors → bfs_residual, and `lemma_bottleneck_crossing` proves any source-to-sink path through the colored/uncolored partition has bottleneck ≤ 0 by induction on path structure. All `assume val` and `assume_` in BFS have been eliminated. All rubric naming and interface file requirements met. The **single `admit()` at Impl.fst** (augment_imp_preserves_valid) remains the highest-priority item. Four `assume val` axioms in Complexity.fst are secondary concerns.
