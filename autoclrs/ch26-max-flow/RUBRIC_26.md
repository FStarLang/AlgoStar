# Chapter 26: Maximum Flow — Rubric Compliance

**Date**: 2025-07-18 (updated 2025-07-20)
**Canonical rubric**: `../RUBRIC.md`
**Audit reference**: `../AUDIT_CH26.md`
**Verification status**: All 10 `.checked` files present in `_cache/` (6 `.fst` + 4 `.fsti`)

---

## Current File Inventory

| # | File | Lines | Rubric Role | Verified |
|---|------|------:|-------------|:--------:|
| 1 | `CLRS.Ch26.MaxFlow.Spec.fst` | 356 | **Spec** — Pure specification: flow networks, residual graphs, augmenting paths, cuts | ✅ |
| 2 | `CLRS.Ch26.MaxFlow.Lemmas.fsti` | 159 | **Lemmas interface** — Public API for augmentation lemmas | ✅ |
| 3 | `CLRS.Ch26.MaxFlow.Lemmas.fst` | 887 | **Lemmas** — Augmentation preserves validity, increases flow value, edge commutativity | ✅ |
| 4 | `CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut.fsti` | 52 | **MFMC interface** — Public API for MFMC theorem | ✅ |
| 5 | `CLRS.Ch26.MaxFlow.Lemmas.MaxFlowMinCut.fst` | 800 | **MFMC** — Weak duality, strong duality (CLRS Theorem 26.6) | ✅ |
| 6 | `CLRS.Ch26.MaxFlow.Complexity.fsti` | 67 | **Complexity interface** — Public API for complexity theorems | ✅ |
| 7 | `CLRS.Ch26.MaxFlow.Complexity.fst` | 1546 | **Complexity** — O(VE²) bound with ghost tick counter, BFS layer proofs | ✅ |
| 8 | `CLRS.Ch26.MaxFlow.Impl.fsti` | 122 | **Impl interface** — Public API for `max_flow` + bridge lemma | ✅ |
| 9 | `CLRS.Ch26.MaxFlow.Impl.fst` | 2996 | **Impl** — Imperative Pulse implementation: BFS-based Ford-Fulkerson (Edmonds-Karp) | ✅ |
| 10 | `CLRS.Ch26.MaxFlow.Test.fst` | 274 | Test — 5 test cases (3-vertex, disconnected, single edge, diamond, bottleneck) | ✅ |
| | **Total** | **~7260** | | |

---

## Algorithms Covered

### Edmonds-Karp (Ford-Fulkerson with BFS) — CLRS §26.2–26.3

| CLRS Pseudocode Step | Implementation | Location |
|-----------------------|---------------|----------|
| **FORD-FULKERSON** line 1: init flow to 0 | `zero_init_flow flow nn` | Impl.fst |
| **FORD-FULKERSON** line 2: while ∃ augmenting path in G_f | `bfs_residual` returns `found: bool` | Impl.fst |
| **FORD-FULKERSON** line 3: augment flow along path | `find_bottleneck_imp` + `augment_imp` | Impl.fst |
| **FORD-FULKERSON** line 4: return f | Returns flow in array with `imp_valid_flow` + `no_augmenting_path` | Impl.fst |
| BFS shortest-path selection (Edmonds-Karp) | Standard BFS with queue, color, predecessor arrays | Impl.fst `bfs_residual` |

**Spec-level variants** (Spec.fst):
- `ford_fulkerson` (line 203): explicit path-list functional specification
- `ford_fulkerson_fuel` (line 215): oracle + fuel iterative model

---

## Rubric Compliance Matrix

The canonical rubric (`RUBRIC.md`) requires the following file structure per algorithm:

| Rubric File | Expected Name | Actual File | Status | Notes |
|-------------|---------------|-------------|:------:|-------|
| `Spec.fst` | `CLRS.Ch26.MaxFlow.Spec.fst` | `CLRS.Ch26.MaxFlow.Spec.fst` | ✅ | 356 lines, pure spec, zero admits |
| `Lemmas.fst` | `CLRS.Ch26.MaxFlow.Lemmas.fst` | `CLRS.Ch26.MaxFlow.Lemmas.fst` | ✅ | Renamed from Proofs.fst; includes edge commutativity proofs |
| `Lemmas.fsti` | `CLRS.Ch26.MaxFlow.Lemmas.fsti` | `CLRS.Ch26.MaxFlow.Lemmas.fsti` | ✅ | Created — exports key lemma signatures |
| `Complexity.fst` | `CLRS.Ch26.MaxFlow.Complexity.fst` | `CLRS.Ch26.MaxFlow.Complexity.fst` | ✅ | Present, zero admits, zero assume vals. All 4 former axioms now fully proven. |
| `Complexity.fsti` | `CLRS.Ch26.MaxFlow.Complexity.fsti` | `CLRS.Ch26.MaxFlow.Complexity.fsti` | ✅ | Created — exports complexity theorem signatures |
| `Impl.fst` | `CLRS.Ch26.MaxFlow.Impl.fst` | `CLRS.Ch26.MaxFlow.Impl.fst` | ✅ | Renamed from MaxFlow.fst; **zero admits**, augmentation statically proven to preserve `imp_valid_flow` |
| `Impl.fsti` | `CLRS.Ch26.MaxFlow.Impl.fsti` | `CLRS.Ch26.MaxFlow.Impl.fsti` | ✅ | Created — exports `max_flow` public API with unconditional `no_augmenting_path` |

### Proof Soundness Inventory

| # | File | Line | Construct | Severity | Context |
|---|------|-----:|-----------|:--------:|---------|
| — | (none) | — | — | — | **Zero admits, zero assumes across all files including Test.fst** |

**Eliminated** (previously present, now proven):
- ~~`admit()` in `lemma_augment_imp_preserves_valid`~~ → Replaced by static proof chain: `lemma_augment_chain` chains `imp_valid_flow → valid_flow → augment_preserves_valid → valid_flow → imp_valid_flow`
- ~~Runtime `check_imp_valid_flow_fn`~~ → Removed; augmentation statically proven to preserve `imp_valid_flow`
- ~~`completed` flag / partial results~~ → Removed; `no_augmenting_path` is unconditional in postcondition
- ~~Defensive re-zero path~~ → Removed; impossible to reach with static proofs
- ~~`assume val axiom_bfs_complete`~~ → Replaced by `lemma_bfs_complete` + `lemma_bottleneck_crossing` (proven by induction on path structure)
- ~~`assume_ (bfs_complete ...)`~~ → Eliminated via BFS loop counting invariant (`count_color1 == vtail - vhead`, `queue_color1`)
- ~~`assume_ (source colored)`~~ → Follows directly from BFS loop invariant
- ~~`assume val axiom_spd_source_zero`~~ → Proved: δ(s,s) = 0 from BFS-layer definition
- ~~`assume val axiom_spd_bounded`~~ → Proved: δ(s,v) ≤ n from BFS-layer bound
- ~~`assume val lemma_distances_nondecreasing` (Lemma 26.7)~~ → Proved: BFS layer nondecreasing by induction + new-edge-from-path argument
- ~~`assume val axiom_edge_critical_bound` (Lemma 26.8)~~ → Proved: forward/backward criticality bounds via two-state machine induction

**Vacuous proofs**: None remaining. All previously-vacuous definitions have been replaced with proper BFS-layer computations.

### Theorem Coverage

| CLRS Result | Location | Status |
|-------------|----------|:------:|
| Lemma 26.4: \|f\| = net flow across any cut | Lemmas.MaxFlowMinCut.fst:262 | ✅ Proven |
| Corollary 26.5: Weak duality \|f\| ≤ c(S,T) | Lemmas.MaxFlowMinCut.fst:276 | ✅ Proven |
| Theorem 26.6: Max-flow min-cut | Lemmas.MaxFlowMinCut.fst:755 | ✅ Proven |
| Lemma 26.7: Distances non-decreasing | Complexity.fst | ✅ Proven (BFS layer induction + new-edge-from-path) |
| Theorem 26.8: O(VE²) complexity | Complexity.fst | ✅ Fully proven; all supporting lemmas verified |
| Augmentation preserves valid flow | Lemmas.fst:628 | ✅ Proven |
| Augmentation increases flow value | Lemmas.fst:656 | ✅ Proven |
| Zero flow is valid | Lemmas.fst:672 | ✅ Proven |
| Path shortening (pigeonhole) | Lemmas.MaxFlowMinCut.fst | ✅ Proven |
| imp_valid_flow ⟹ valid_flow (bridge) | Impl.fst | ✅ Proven |
| valid_flow ⟹ imp_valid_flow (reverse bridge) | Impl.fst | ✅ Proven |
| augment_imp preserves imp_valid_flow (static) | Impl.fst `lemma_augment_chain` | ✅ Proven (chains: imp→valid→augment_preserves→valid→imp) |
| augment_imp refines augment_via_pred | Impl.fst `augment_imp` postcondition | ✅ Proven (loop invariant tracks `augment_via_pred`) |
| find_bottleneck_imp = bottleneck_via_pred | Impl.fst `find_bottleneck_imp` postcondition | ✅ Proven (loop invariant tracks `bottleneck_via_pred`) |
| imp_valid_flow loop invariant (zero init + static proof) | Impl.fst | ✅ Verified |
| Edmonds-Karp terminates (no fuel) | Impl.fst | ✅ Proven (flow_value bounded by cap_sum, decreasing measure) |
| MFMC usable by callers | Impl.fst/fsti | ✅ `no_augmenting_path` unconditional in postcondition |
| BFS completeness: bfs_complete ⟹ no_augmenting_path | Impl.fst | ✅ Proven (lemma_bottleneck_crossing, induction on path) |
| BFS termination ⟹ bfs_complete | Impl.fst | ✅ Proven (counting invariant: count_color1 + queue_color1) |

---

## Detailed Action Items

### ✅ P0 — RESOLVED: `admit()` and Runtime Checks Eliminated

**File**: `CLRS.Ch26.MaxFlow.Impl.fst`
**Resolution**: Fully static proof chain replaces all runtime checks:
1. `lemma_zero_flow_imp_valid` proves the zero flow satisfies `imp_valid_flow` (loop invariant initialization)
2. `imp_valid_flow` is carried as a conjunct in the main Ford-Fulkerson while-loop invariant
3. After each augmentation, `lemma_augment_chain` statically proves `imp_valid_flow` is preserved
4. `find_bottleneck_imp` postcondition proves `bn > 0 /\ bn == bottleneck_via_pred ...`
5. `augment_imp` postcondition proves `flow_seq' == augment_via_pred ...`
6. `no_augmenting_path` is unconditionally guaranteed — no `completed` flag needed

**Key proof artifacts**:
- `lemma_augment_chain`: Chains imp_valid_flow → valid_flow → augment_preserves_valid → valid_flow → imp_valid_flow; also proves flow_value strictly increases
- `lemma_bottleneck_step` / `lemma_augment_step`: One-loop-iteration lemmas for loop invariant maintenance
- `lemma_augment_edge_fwd/bwd`: Bridges Pulse array operations to pure `augment_edge` specification
- `bfs_pred_ok`: Opaque predicate that bundles all BFS postcondition properties for ghost parameter passing

---

### ✅ P1 — RESOLVED: Complexity Lemmas Fully Proven

| ID | Task | Status |
|----|------|:------:|
| P1.1 | Prove CLRS Lemma 26.7 (distance monotonicity) | ✅ Proven: `lemma_bfs_layer_nondecreasing` + `lemma_distances_nondecreasing` |
| P1.2 | Prove CLRS Lemma 26.8 (edge criticality bound) | ✅ Proven: `lemma_forward_critical_bound` + `lemma_backward_critical_bound` + `lemma_edge_critical_bound` |
| P1.3 | Derive `max_augmentations` from criticality | ✅ `lemma_max_augmentations_justified` proven |
| P1.4 | Prove `axiom_spd_source_zero` and `axiom_spd_bounded` | ✅ Proven: from BFS-layer definitions |

---

### 🟡 P2 — MEDIUM: Structural & Naming Compliance

| ID | Task | Detail | Status |
|----|------|--------|:------:|
| P2.1 | Rename `Proofs.fst` → `Lemmas.fst` | Rubric requires "Lemmas" not "Proofs". Updated all references. | ✅ Done |
| P2.2 | Rename `MaxFlow.fst` → `Impl.fst` | Rubric requires "Impl". Updated all references. | ✅ Done |
| P2.3 | Create `Lemmas.fsti` | Interface file with lemma signatures + helper lemmas used by Complexity. | ✅ Done |
| P2.4 | Create `Complexity.fsti` | Interface file with complexity definitions and theorem signatures. | ✅ Done |
| P2.5 | Create `Impl.fsti` | Public interface for `max_flow`, `valid_caps`, `imp_valid_flow`, `check_valid_caps_fn`. | ✅ Done |
| P2.6 | Strengthen main loop invariant | `max_flow` while-loop now carries `imp_valid_flow` as a loop invariant | ✅ Done |
| P2.7 | Add termination proof for main loop | `max_flow` terminates without fuel: flow_value increases by ≥1 per augmentation, bounded by cap_sum = Σ cap[source][v]. Measure: `cap_sum + 1 - iters`. | ✅ Done |
| P2.8 | Eliminate `assume_` in test | Test.fst — replaced `assume_` with `check_valid_caps_fn` + `valid_caps_intro` lemma; branches on runtime check result | ✅ Done |

---

### 🟢 P3 — LOW: Polish

| ID | Task | Detail | Status |
|----|------|--------|:------:|
| P3.1 | Replace INT_MAX magic number | `find_bottleneck_imp` uses literal `2147483647`; replaced with named constant `int_max` | ✅ Done |
| P3.2 | Rewrite README.md | Updated to document current 8-file Edmonds-Karp implementation with Lemmas/Impl naming | ✅ Done |
| P3.3 | Add diverse test cases | Added: disconnected graph (no path), single edge, diamond (multiple paths), bottleneck (capacity-limited middle edge) | ✅ Done |

---

## Quality Checks

### Soundness Summary

| Dimension | Status | Detail |
|-----------|:------:|--------|
| **Zero `admit` in spec/lemmas** | ✅ | Spec.fst (1125 lines) and Lemmas.fst (679 lines) are fully proven |
| **Zero `admit` in complexity** | ✅ | No `admit`, no `assume val`; all 4 former axioms fully proven |
| **Zero `admit` in impl** | ✅ | `lemma_augment_imp_preserves_valid` eliminated; `imp_valid_flow` maintained as loop invariant |
| **Zero `assume_` in production** | ✅ | All BFS `assume_` eliminated; zero `assume_` across all files including Test.fst |
| **All files verified (.checked)** | ✅ | 10/10 `.checked` files in `_cache/` (6 `.fst` + 4 `.fsti`) |
| **MFMC theorem proven** | ✅ | Lemmas.MaxFlowMinCut.fst:755, constructive (2)⟹(3) direction of Theorem 26.6 |
| **Flow conservation proven** | ✅ | Lemmas.fst:628, for all augmentations on valid simple paths |
| **O(VE²) bound proven** | ✅ | Arithmetic correct; all supporting lemmas fully proven |

### Rubric Conformance Summary

| Criterion | Score | Notes |
|-----------|:-----:|-------|
| Spec file present & correct | ✅ | Pure definitions only (341 lines) |
| Lemmas file present | ✅ | Renamed from Proofs.fst to Lemmas.fst |
| Lemmas interface (.fsti) | ✅ | Created with key lemma + helper signatures |
| MFMC theorem in Lemmas | ✅ | Extracted to Lemmas.MaxFlowMinCut.fst/fsti (804 lines) |
| Complexity file present | ✅ | Present; zero admits, zero assume vals |
| Complexity interface (.fsti) | ✅ | Created with theorem signatures |
| Impl file present | ✅ | Renamed from MaxFlow.fst to Impl.fst; zero admits, no runtime checks |
| Impl interface (.fsti) | ✅ | Created with `max_flow` public API; `no_augmenting_path` unconditional |
| imp_valid_flow ↔ valid_flow | ✅ | Bridge lemma (both directions) connects Impl postcondition to Spec.valid_flow |
| MFMC usable by callers | ✅ | `no_augmenting_path` unconditional in postcondition — directly satisfies MFMC precondition |
| No admits in production | ✅ | Zero admits across Spec, Lemmas, MFMC, and Impl |
| Documentation accurate | ✅ | README updated to reflect current file structure |

### Overall Rating

| Dimension | Rating |
|-----------|--------|
| CLRS Fidelity | ★★★★★ |
| Specification Strength | ★★★★★ |
| Complexity Proofs | ★★★★★ |
| Code Quality | ★★★★★ |
| Proof Quality (Spec+Lemmas) | ★★★★★ |
| Proof Quality (Impl) | ★★★★★ |
| Rubric Structural Compliance | ★★★★★ |
| Documentation | ★★★★★ |

**Bottom line**: Excellent pure-spec proofs (MFMC, conservation, augmentation — all zero-admit). **Zero admits, zero assume vals, zero runtime checks in all code** (Spec, Lemmas, MFMC, Complexity, Impl, Test). **All 4 former Complexity axioms now fully proven**: BFS-layer shortest_path_distance definition, spd_source_zero, spd_bounded, Lemma 26.7 (distances non-decreasing via BFS layer induction + new-edge-from-path argument), and Lemma 26.8 (edge criticality bound via forward/backward two-state machine induction). **Edmonds-Karp termination proven without fuel**: flow_value increases by ≥1 per augmentation, bounded by cap_sum = Σ cap[source][v]; decreasing measure `cap_sum + 1 - iters` guarantees finite iterations. **Augmentation statically proven correct**: `lemma_augment_chain` chains imp_valid_flow → valid_flow → augment_preserves_valid → valid_flow → imp_valid_flow, eliminating all runtime validity checks and defensive re-zero paths. MFMC theorem isolated in Lemmas.MaxFlowMinCut with clean interface. Bridge lemmas (both directions) connect Impl postcondition to `Spec.valid_flow`, enabling callers to use MFMC theorem results. `no_augmenting_path` is **unconditional** in the postcondition — exactly the MFMC precondition. **BFS completeness fully proven**: counting invariants track BFS queue state, and `lemma_bottleneck_crossing` proves any source-to-sink path through the colored/uncolored partition has bottleneck ≤ 0 by induction on path structure. **Test.fst** uses `check_valid_caps_fn` + `valid_caps_intro` to establish preconditions without any `assume_`.
