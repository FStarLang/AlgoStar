# Chapter 26: Maximum Flow — Rubric Compliance

**Date**: 2025-07-18
**Canonical rubric**: `../RUBRIC.md`
**Audit reference**: `../AUDIT_CH26.md`
**Verification status**: All 5 `.checked` files present in `_cache/`

---

## Current File Inventory

| # | File | Lines | Rubric Role | Verified |
|---|------|------:|-------------|:--------:|
| 1 | `CLRS.Ch26.MaxFlow.Spec.fst` | 1125 | **Spec** — Pure specification: flow networks, residual graphs, augmenting paths, cuts, MFMC theorem | ✅ |
| 2 | `CLRS.Ch26.MaxFlow.Proofs.fst` | 679 | **Lemmas** — Augmentation preserves validity, increases flow value | ✅ |
| 3 | `CLRS.Ch26.MaxFlow.Complexity.fst` | 618 | **Complexity** — O(VE²) bound with ghost tick counter | ✅ |
| 4 | `CLRS.Ch26.MaxFlow.fst` | 1285 | **Impl** — Imperative Pulse implementation: BFS-based Ford-Fulkerson (Edmonds-Karp) | ✅ |
| 5 | `CLRS.Ch26.MaxFlow.Test.fst` | 61 | Test — Smoke test on 3-vertex graph | ✅ |
| | **Total** | **3768** | | |

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
| `Lemmas.fst` | `CLRS.Ch26.MaxFlow.Lemmas.fst` | `CLRS.Ch26.MaxFlow.Proofs.fst` | 🔶 | Named "Proofs" not "Lemmas" |
| `Lemmas.fsti` | `CLRS.Ch26.MaxFlow.Lemmas.fsti` | *(missing)* | ❌ | No interface file for lemmas |
| `Complexity.fst` | `CLRS.Ch26.MaxFlow.Complexity.fst` | `CLRS.Ch26.MaxFlow.Complexity.fst` | 🔶 | Present, but contains 4 `assume val` axioms and vacuous key lemmas |
| `Complexity.fsti` | `CLRS.Ch26.MaxFlow.Complexity.fsti` | *(missing)* | ❌ | No interface file for complexity |
| `Impl.fst` | `CLRS.Ch26.MaxFlow.Impl.fst` | `CLRS.Ch26.MaxFlow.fst` | 🔶 | Named "MaxFlow" not "Impl"; **contains `admit()` at line 355** |
| `Impl.fsti` | `CLRS.Ch26.MaxFlow.Impl.fsti` | *(missing)* | ❌ | No public interface for implementation |

### Proof Soundness Inventory

| # | File | Line | Construct | Severity | Context |
|---|------|-----:|-----------|:--------:|---------|
| **1** | **MaxFlow.fst** | **355** | **`admit ()`** | **🔴 CRITICAL** | `lemma_augment_imp_preserves_valid` — asserts `imp_valid_flow` without proof |
| 2 | Test.fst | 47 | `assume_` | 🟡 Medium | Assumes `valid_caps` after manual array writes; test-only |
| 3 | Complexity.fst | 57 | `assume val` | 🟡 Medium | `axiom_spd_source_zero` — SPD source = 0 |
| 4 | Complexity.fst | 66 | `assume val` | 🟡 Medium | `axiom_spd_bounded` — SPD bounded by n−1 |
| 5 | Complexity.fst | 77 | `assume val` | 🟠 High | `lemma_distances_nondecreasing` — CLRS Lemma 26.7 |
| 6 | Complexity.fst | 344 | `assume val` | 🟠 High | `axiom_edge_critical_bound` — CLRS Lemma 26.8 |

**Vacuous proofs** (accepted by F\* but logically trivial):

| # | File | Line | Function | Issue |
|---|------|-----:|----------|-------|
| 1 | Complexity.fst | ~40 | `shortest_path_distance` | Defined as constant (0 if source, else n); independent of flow |
| 2 | Complexity.fst | ~299 | `lemma_edge_critical_bound` | Now `assume val`; was formerly postcondition `True` |
| 3 | Complexity.fst | ~357 | `max_augmentations` | Defined directly as `V * E`; not derived from criticality bound |

### Theorem Coverage

| CLRS Result | Location | Status |
|-------------|----------|:------:|
| Lemma 26.4: \|f\| = net flow across any cut | Spec.fst:582 | ✅ Proven |
| Corollary 26.5: Weak duality \|f\| ≤ c(S,T) | Spec.fst:597 | ✅ Proven |
| Theorem 26.6: Max-flow min-cut | Spec.fst:1076 | ✅ Proven |
| Lemma 26.7: Distances non-decreasing | Complexity.fst:77 | ❌ `assume val` |
| Theorem 26.8: O(VE²) complexity | Complexity.fst:315 | 🔶 Arithmetic proven; key lemmas axiomatized |
| Augmentation preserves valid flow | Proofs.fst:628 | ✅ Proven |
| Augmentation increases flow value | Proofs.fst:656 | ✅ Proven |
| Zero flow is valid | Proofs.fst:672 | ✅ Proven |
| Path shortening (pigeonhole) | Spec.fst:877+ | ✅ Proven |

---

## Detailed Action Items

### 🔴 P0 — CRITICAL: Eliminate `admit()` in Production Code

**File**: `CLRS.Ch26.MaxFlow.fst`, line 355
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

| ID | Task | Detail |
|----|------|--------|
| P2.1 | Rename `CLRS.Ch26.MaxFlow.Proofs.fst` → `CLRS.Ch26.MaxFlow.Lemmas.fst` | Rubric requires "Lemmas" not "Proofs". Update all `open` / dependency references. |
| P2.2 | Rename `CLRS.Ch26.MaxFlow.fst` → `CLRS.Ch26.MaxFlow.Impl.fst` | Rubric requires "Impl" for the imperative implementation. Update all references. |
| P2.3 | Create `CLRS.Ch26.MaxFlow.Lemmas.fsti` | Interface file with lemma signatures (augment_preserves_valid, augment_increases_value, zero_flow_valid, etc.) |
| P2.4 | Create `CLRS.Ch26.MaxFlow.Complexity.fsti` | Interface file with complexity definitions and theorem signatures |
| P2.5 | Create `CLRS.Ch26.MaxFlow.Impl.fsti` | Public interface for the imperative implementation (`max_flow` signature) |
| P2.6 | Strengthen main loop invariant | `max_flow` while-loop should carry `imp_valid_flow` (or weaker precursor) to remove runtime-check dependency |
| P2.7 | Add termination proof for main loop | Natural decreasing measure: `max_flow_value - current_flow_value` (bounded, decreases by ≥1 per iteration for integer capacities) |
| P2.8 | Eliminate `assume_` in test | Test.fst:47 — either prove `valid_caps` from the array writes or replace with a runtime check that produces the proof |

---

### 🟢 P3 — LOW: Polish

| ID | Task | Detail |
|----|------|--------|
| P3.1 | Replace INT_MAX magic number | `find_bottleneck_imp` uses literal `2147483647`; replace with named constant |
| P3.2 | Rewrite README.md | README describes a prior simpler version (138 lines, no BFS). Must document current 5-file, 3768-line Edmonds-Karp implementation with MFMC theorem |
| P3.3 | Add diverse test cases | Single 3-vertex smoke test; add edge cases (disconnected graph, zero-capacity edges, single edge, large fan-out) |

---

## Quality Checks

### Soundness Summary

| Dimension | Status | Detail |
|-----------|:------:|--------|
| **Zero `admit` in spec/proofs** | ✅ | Spec.fst (1125 lines) and Proofs.fst (679 lines) are fully proven |
| **Zero `admit` in complexity** | 🔶 | No `admit`, but 4 `assume val` axioms pending BFS correctness |
| **Zero `admit` in impl** | ❌ | **1 `admit()` at MaxFlow.fst:355** — `lemma_augment_imp_preserves_valid` |
| **Zero `assume_` in production** | ✅ | Only `assume_` is in Test.fst (test-only) |
| **All files verified (.checked)** | ✅ | 5/5 `.checked` files in `_cache/` |
| **MFMC theorem proven** | ✅ | Spec.fst:1076, constructive (2)⟹(3) direction of Theorem 26.6 |
| **Flow conservation proven** | ✅ | Proofs.fst:628, for all augmentations on valid simple paths |
| **O(VE²) bound proven** | 🔶 | Arithmetic correct; depends on 4 axiomatized lemmas |

### Rubric Conformance Summary

| Criterion | Score | Notes |
|-----------|:-----:|-------|
| Spec file present & correct | ✅ | Naming matches rubric exactly |
| Lemmas file present | 🔶 | Present as "Proofs.fst" — needs rename |
| Lemmas interface (.fsti) | ❌ | Missing |
| Complexity file present | 🔶 | Present; 4 `assume val` axioms |
| Complexity interface (.fsti) | ❌ | Missing |
| Impl file present | 🔶 | Present as "MaxFlow.fst" — needs rename; **has `admit()`** |
| Impl interface (.fsti) | ❌ | Missing |
| No admits in production | ❌ | **1 admit at MaxFlow.fst:355** |
| Documentation accurate | ❌ | README describes prior version |

### Overall Rating

| Dimension | Rating |
|-----------|--------|
| CLRS Fidelity | ★★★★☆ |
| Specification Strength | ★★★★☆ |
| Complexity Proofs | ★★★☆☆ |
| Code Quality | ★★★★☆ |
| Proof Quality (Spec+Proofs) | ★★★★★ |
| Proof Quality (Impl) | ★★☆☆☆ |
| Rubric Structural Compliance | ★★☆☆☆ |
| Documentation | ★★☆☆☆ |

**Bottom line**: Excellent pure-spec proofs (MFMC, conservation, augmentation — all zero-admit). The **single `admit()` at MaxFlow.fst:355** is the highest-priority item: it breaks the static proof chain from implementation to spec. Four `assume val` axioms in Complexity.fst and three missing `.fsti` interface files are secondary concerns. README is severely outdated.
