# Chapter 22: Elementary Graph Algorithms — Rubric Compliance

**Files:** 26 (21 `.fst` + 5 `.fsti`) | **Verified:** All
**Date:** 2025-07-14 (updated 2026-03-04)

---

## Current File Inventory

| # | File | Lines | Layer | Role |
|---|------|------:|-------|------|
| 1 | `CLRS.Ch22.BFS.Spec.fst` | 166 | Spec | Pure BFS level-set specification |
| 2 | `CLRS.Ch22.BFS.DistanceSpec.fst` | 1,116 | Spec | BFS shortest-path distance — CLRS Thm 22.5 fully proved |
| 3 | `CLRS.Ch22.BFS.Lemmas.fst` | ~90 | Lemmas | ✅ **NEW** Consolidates key BFS lemma proofs |
| 4 | `CLRS.Ch22.BFS.Lemmas.fsti` | ~90 | Lemmas | ✅ **NEW** Interface for BFS lemma signatures |
| 5 | `CLRS.Ch22.BFS.Complexity.fst` | ~28 | Complexity | ✅ **NEW** BFS O(V²) complexity proofs |
| 6 | `CLRS.Ch22.BFS.Complexity.fsti` | ~22 | Complexity | ✅ **NEW** Interface for BFS complexity bounds |
| 7 | `CLRS.Ch22.DFS.Spec.fst` | 2,929 | Spec | Pure DFS with timestamps, parenthesis theorem, edge classification |
| 8 | `CLRS.Ch22.DFS.WhitePath.fst` | 1,103 | Spec | White-path theorem (CLRS Thm 22.9) both directions |
| 9 | `CLRS.Ch22.DFS.Lemmas.fst` | ~50 | Lemmas | ✅ **NEW** Consolidates key DFS lemma proofs |
| 10 | `CLRS.Ch22.DFS.Lemmas.fsti` | ~55 | Lemmas | ✅ **NEW** Interface for DFS lemma signatures |
| 11 | `CLRS.Ch22.DFS.Complexity.fst` | ~28 | Complexity | ✅ **NEW** DFS O(V²) complexity proofs |
| 12 | `CLRS.Ch22.DFS.Complexity.fsti` | ~30 | Complexity | ✅ **NEW** Interface for DFS complexity bounds |
| 13 | `CLRS.Ch22.DFS.TopologicalSort.fst` | 731 | Spec | DFS-based topological sort (§22.4), bridges DFS.Spec ↔ TS.Spec |
| 14 | `CLRS.Ch22.TopologicalSort.Spec.fst` | 243 | Spec | Topological order definition, DAG property |
| 15 | `CLRS.Ch22.TopologicalSort.Lemmas.fst` | 692 | Lemmas | Helper lemmas for Kahn's correctness proof |
| 16 | `CLRS.Ch22.TopologicalSort.Verified.fst` | 608 | Lemmas | Full correctness proof: Kahn's → `is_topological_order` |
| 17 | `CLRS.Ch22.TopologicalSort.Complexity.fst` | ~26 | Complexity | ✅ **NEW** Kahn's O(V²) complexity proofs |
| 18 | `CLRS.Ch22.TopologicalSort.Complexity.fsti` | ~22 | Complexity | ✅ **NEW** Interface for TopSort complexity bounds |
| 19 | `CLRS.Ch22.Graph.Common.fst` | 78 | Shared | `has_edge`, `reachable_in`, `tick`, `product_strict_bound` |
| 20 | `CLRS.Ch22.Graph.Complexity.fst` | 69 | Shared | O(V²) meta-bound for adjacency-matrix algorithms |
| 21 | `CLRS.Ch22.IterativeBFS.fst` | 265 | Impl | Relaxation-based BFS (Bellman-Ford-like, O(V³)) |
| 22 | `CLRS.Ch22.QueueBFS.fst` | 661 | Impl | **Canonical** queue-based BFS (CLRS §22.2, O(V²)) |
| 23 | `CLRS.Ch22.StackDFS.fst` | 1,105 | Impl | **Canonical** stack-based DFS (CLRS §22.3, O(V²)) |
| 24 | `CLRS.Ch22.KahnTopologicalSort.Defs.fst` | 1,827 | Impl | Kahn's topological sort: predicate lemmas |
| 25 | `CLRS.Ch22.KahnTopologicalSort.Defs.fsti` | 1,293 | Impl | Kahn's topological sort: interface (predicates + `val` signatures) |
| 26 | `CLRS.Ch22.KahnTopologicalSort.fst` | 751 | Impl | Kahn's topological sort: Pulse implementation |

---

## Algorithms Covered

### 1. BFS (CLRS §22.2) — Two Variants

| Variant | File(s) | Fidelity | Data Structure | Colors | Complexity |
|---------|---------|----------|---------------|--------|------------|
| **QueueBFS** (canonical) | `QueueBFS.fst` | High — follows CLRS pseudocode | Explicit array-based queue | W/G/B (0/1/2) | ≤ 2·V² ticks (ghost counter) |
| **IterativeBFS** (alternative) | `IterativeBFS.fst` | Low — relaxation-based | n-round level expansion | Binary (0/non-zero) | Not tracked (O(V³) work) |

**Shared spec:** `BFS.Spec.fst` (level sets), `BFS.DistanceSpec.fst` (path/distance infrastructure).

### 2. DFS (CLRS §22.3) — Two Implementations

| Variant | File(s) | Fidelity | Timestamps | Predecessor | Complexity |
|---------|---------|----------|------------|-------------|------------|
| **StackDFS** (canonical) | `StackDFS.fst` | High — explicit stack simulating recursion | d[u], f[u] | π[u] | ≤ 2·V² ticks (ghost counter) |
| *IterativeDFS* | *(deleted)* | N/A — was graph reachability, not DFS | — | — | — |

**Spec:** `DFS.Spec.fst` (pure functional DFS, parenthesis theorem, edge classification, cycle detection), `DFS.WhitePath.fst` (Thm 22.9).

### 3. Topological Sort (CLRS §22.4) — Two Algorithms

| Algorithm | File(s) | CLRS Section | Approach |
|-----------|---------|-------------|----------|
| **DFS-based** (CLRS canonical) | `DFS.TopologicalSort.fst` | §22.4 | Decreasing finish-time order from DFS |
| **Kahn's** (alternative) | `KahnTopologicalSort.fst`, `KahnTopologicalSort.Defs.fst/.fsti` | Mentioned briefly §22.4 | BFS-based in-degree reduction |

**Shared spec:** `TopologicalSort.Spec.fst` (`is_topological_order`), `TopologicalSort.Lemmas.fst`, `TopologicalSort.Verified.fst`.

### 4. Shared Infrastructure

| File | Purpose |
|------|---------|
| `Graph.Common.fst` | `has_edge`, `reachable_in`, `tick/incr_nat`, `product_strict_bound` — used by QueueBFS, StackDFS |
| `Graph.Complexity.fst` | O(V²) meta-bound proving O(V+E) ≤ O(V²) for adjacency-matrix representation |

---

## Rubric Compliance Matrix

The rubric requires per-algorithm: **Spec**, **Lemmas** (`.fst` + `.fsti`), **Complexity** (`.fst` + `.fsti`), **Impl** (`.fst` + `.fsti`).

### BFS (§22.2)

| Rubric File | Expected Name | Status | Actual File | Notes |
|-------------|---------------|--------|-------------|-------|
| `Spec.fst` | `CLRS.Ch22.BFS.Spec.fst` | ✅ Present | `BFS.Spec.fst` (166 lines) | Level-set BFS, zero admits |
| `Lemmas.fst` | `CLRS.Ch22.BFS.Lemmas.fst` | ✅ Present | `BFS.Lemmas.fst` | ✅ **NEW** Consolidates results from BFS.Spec + BFS.DistanceSpec |
| `Lemmas.fsti` | `CLRS.Ch22.BFS.Lemmas.fsti` | ✅ Present | `BFS.Lemmas.fsti` | ✅ **NEW** Key BFS lemma signatures |
| `Complexity.fst` | `CLRS.Ch22.BFS.Complexity.fst` | ✅ Present | `BFS.Complexity.fst` | ✅ **NEW** BFS-specific O(V²) proofs |
| `Complexity.fsti` | `CLRS.Ch22.BFS.Complexity.fsti` | ✅ Present | `BFS.Complexity.fsti` | ✅ **NEW** Interface for BFS complexity |
| `Impl.fst` | `CLRS.Ch22.BFS.Impl.fst` | 🔶 Name differs | `QueueBFS.fst` (661 lines) | Correct implementation, non-standard name |
| `Impl.fsti` | `CLRS.Ch22.BFS.Impl.fsti` | 🔶 Skipped | — | QueueBFS.fst is the canonical impl; renaming would break imports |

**Additional BFS files (outside rubric):**
- `BFS.DistanceSpec.fst` (1,116 lines) — path infrastructure for Thm 22.5 (hard direction unproved)
- `IterativeBFS.fst` (265 lines) — alternative relaxation-based BFS (self-contained)

### DFS (§22.3)

| Rubric File | Expected Name | Status | Actual File | Notes |
|-------------|---------------|--------|-------------|-------|
| `Spec.fst` | `CLRS.Ch22.DFS.Spec.fst` | ✅ Present | `DFS.Spec.fst` (2,929 lines) | Outstanding: parenthesis thm, edge classification, cycle detection |
| `Lemmas.fst` | `CLRS.Ch22.DFS.Lemmas.fst` | ✅ Present | `DFS.Lemmas.fst` | ✅ **NEW** Consolidates from DFS.Spec + DFS.WhitePath |
| `Lemmas.fsti` | `CLRS.Ch22.DFS.Lemmas.fsti` | ✅ Present | `DFS.Lemmas.fsti` | ✅ **NEW** Key DFS lemma signatures |
| `Complexity.fst` | `CLRS.Ch22.DFS.Complexity.fst` | ✅ Present | `DFS.Complexity.fst` | ✅ **NEW** DFS-specific O(V²) proofs |
| `Complexity.fsti` | `CLRS.Ch22.DFS.Complexity.fsti` | ✅ Present | `DFS.Complexity.fsti` | ✅ **NEW** Interface for DFS complexity |
| `Impl.fst` | `CLRS.Ch22.DFS.Impl.fst` | 🔶 Name differs | `StackDFS.fst` (1,105 lines) | Correct implementation, non-standard name |
| `Impl.fsti` | `CLRS.Ch22.DFS.Impl.fsti` | 🔶 Skipped | — | StackDFS.fst is the canonical impl; renaming would break imports |

### Topological Sort (§22.4) — DFS-Based (CLRS Canonical)

| Rubric File | Expected Name | Status | Actual File | Notes |
|-------------|---------------|--------|-------------|-------|
| `Spec.fst` | `CLRS.Ch22.TopologicalSort.Spec.fst` | ✅ Present | `TopologicalSort.Spec.fst` (243 lines) | `is_topological_order` definition, DAG proof |
| `Lemmas.fst` | `CLRS.Ch22.TopologicalSort.Lemmas.fst` | ✅ Present | `TopologicalSort.Lemmas.fst` (692 lines) | `strong_order_inv` and helpers |
| `Lemmas.fsti` | `CLRS.Ch22.TopologicalSort.Lemmas.fsti` | 🔶 Skipped | — | Adding .fsti would restrict interface; existing dependents (KahnTopologicalSort.Defs, TopologicalSort.Verified) need full access |
| `Complexity.fst` | `CLRS.Ch22.TopologicalSort.Complexity.fst` | ✅ Present | `TopologicalSort.Complexity.fst` | ✅ **NEW** Kahn's O(V²) proofs |
| `Complexity.fsti` | `CLRS.Ch22.TopologicalSort.Complexity.fsti` | ✅ Present | `TopologicalSort.Complexity.fsti` | ✅ **NEW** Interface for TopSort complexity |
| `Impl.fst` | `CLRS.Ch22.TopologicalSort.Impl.fst` | 🔶 Split | `KahnTopologicalSort.fst` (751 lines) | Kahn's algorithm (not CLRS canonical) |
| `Impl.fsti` | `CLRS.Ch22.TopologicalSort.Impl.fsti` | 🔶 Exists (different name) | `KahnTopologicalSort.Defs.fsti` (1,293 lines) | Interface exists for Kahn's definitions |

**Additional Topological Sort files:**
- `DFS.TopologicalSort.fst` (731 lines) — bridges DFS.Spec to TopologicalSort.Spec (the CLRS §22.4 algorithm)
- `TopologicalSort.Verified.fst` (608 lines) — full Kahn's correctness proof
- `KahnTopologicalSort.Defs.fst` (1,827 lines) — Kahn's predicate lemmas

### Summary Counts

| | ✅ Present | 🔶 Partial/Renamed/Skipped | ❌ Missing | Total Expected |
|---|:---:|:---:|:---:|:---:|
| **Spec.fst** | 3 | 0 | 0 | 3 |
| **Lemmas.fst** | 3 | 0 | 0 | 3 |
| **Lemmas.fsti** | 2 | 1 | 0 | 3 |
| **Complexity.fst** | 3 | 0 | 0 | 3 |
| **Complexity.fsti** | 3 | 0 | 0 | 3 |
| **Impl.fst** | 0 | 3 | 0 | 3 |
| **Impl.fsti** | 0 | 3 | 0 | 3 |
| **Total** | **14** | **7** | **0** | **21** |

---

## Detailed Action Items

### Priority 1 — Specification & Proof Gaps

| # | Action | Impact | Effort | Files | Status |
|---|--------|--------|--------|-------|--------|
| 1.1 | **Prove BFS shortest-path optimality (CLRS Thm 22.5, hard direction)** | Core BFS correctness | High | `BFS.DistanceSpec.fst` | ✅ **Already proved** — `bfs_correctness` (line 997) proves both directions. Stale header comment fixed. |
| 1.2 | **Add reachability postcondition to QueueBFS** — currently proves "visited ⟹ dist ≥ 0" but not "reachable ⟹ visited" | Spec completeness | Medium | `QueueBFS.fst` | Remaining |
| 1.3 | **Add reachability postcondition to StackDFS** — proves "all BLACK with valid timestamps" but not "reachable ⟹ visited" | Spec completeness | Low | `StackDFS.fst` | Remaining |

### Priority 2 — Missing Interface Files (`.fsti`)

| # | Action | Impact | Effort | Status |
|---|--------|--------|--------|--------|
| 2.1 | **Create `BFS.Lemmas.fsti`** — key BFS lemma signatures | Rubric compliance | Low | ✅ **Done** — verified |
| 2.2 | **Create `DFS.Lemmas.fsti`** — interface for parenthesis, white-path, completeness | Rubric compliance | Low | ✅ **Done** — verified |
| 2.3 | **Create `TopologicalSort.Lemmas.fsti`** — interface for `strong_order_inv` | Rubric compliance | Low | 🔶 **Skipped** — would break dependent modules |
| 2.4 | **Create `BFS.Impl.fsti`** — public signature for QueueBFS | Rubric compliance | Low | 🔶 **Skipped** — QueueBFS naming is stable; wrapper would be fragile |
| 2.5 | **Create `DFS.Impl.fsti`** — public signature for StackDFS | Rubric compliance | Low | 🔶 **Skipped** — StackDFS naming is stable; wrapper would be fragile |

### Priority 3 — Missing Complexity Files

| # | Action | Impact | Effort | Status |
|---|--------|--------|--------|--------|
| 3.1 | **Create `BFS.Complexity.fst` / `.fsti`** — BFS O(V²) bound | Rubric compliance | Medium | ✅ **Done** — verified |
| 3.2 | **Create `DFS.Complexity.fst` / `.fsti`** — DFS O(V²) bound | Rubric compliance | Medium | ✅ **Done** — verified |
| 3.3 | **Create `TopologicalSort.Complexity.fst` / `.fsti`** — Kahn's O(V²) bound | Rubric compliance | Medium | ✅ **Done** — verified |

### Priority 4 — Naming / Organization

| # | Action | Impact | Effort | Status |
|---|--------|--------|--------|--------|
| 4.1 | Consider renaming `QueueBFS.fst` → `BFS.Impl.fst` | Rubric naming | Low | 🔶 Deferred — may break imports |
| 4.2 | Consider renaming `StackDFS.fst` → `DFS.Impl.fst` | Rubric naming | Low | 🔶 Deferred — may break imports |
| 4.3 | **Create `BFS.Lemmas.fst`** — consolidate BFS lemmas | Rubric structure | Medium | ✅ **Done** — verified |
| 4.4 | **Fix stale comment in `TopologicalSort.Verified:431`** | Accuracy | Trivial | ✅ **Already fixed** — says "fully proved" |
| 4.5 | **Fix stale comment in `DFS.WhitePath:1099`** | Accuracy | Trivial | ✅ **Already fixed** — says "fully proved" |
| 4.6 | **Fix stale comment in `BFS.DistanceSpec:9`** — said "harder — admitted" | Accuracy | Trivial | ✅ **Done** — updated to "fully proved via bfs_correctness" |

---

## Quality Checks

### Proof Quality: ✅ Excellent

- **Zero admits** across all 13,637 lines — no `admit()`, `admit_()`, `assume()`, or `assume_()` calls
- **Deep CLRS theorems proved:**
  - Parenthesis Theorem (Thm 22.7) — mutual induction in `DFS.Spec`
  - White-Path Theorem (Thm 22.9) — both directions in `DFS.WhitePath`
  - Edge classification (Tree/Back/Forward/Cross) — `DFS.Spec`
  - Cycle ⟺ back edge (Thm 22.11) — `DFS.Spec`
  - Kahn's correctness including pigeonhole — `TopologicalSort.Verified`
  - DFS-based topological sort correctness — `DFS.TopologicalSort`
- **Complexity accounting:** Ghost tick counters in QueueBFS (≤ 2V²), StackDFS (≤ 2V²), KahnTopologicalSort (≤ V²)

### CLRS Fidelity: ✅ High

- **QueueBFS** faithfully follows CLRS §22.2 pseudocode (ENQUEUE/DEQUEUE, W/G/B colors, predecessor)
- **StackDFS** faithfully follows CLRS §22.3 (explicit stack simulating recursion, d/f timestamps, scan_idx)
- **DFS.TopologicalSort** implements the CLRS §22.4 algorithm (decreasing finish-time)
- **KahnTopologicalSort** is an alternative (mentioned in CLRS but not the primary algorithm)
- **IterativeBFS** is a valid but non-standard relaxation-based alternative (documented as such)

### Code Duplication: 🔶 Moderate

- `has_edge` defined 5× with incompatible signatures (flat int, flat bool, 2D int, prop vs bool)
- `reachable_in` copy-pasted 3× (IterativeBFS, QueueBFS retained local copy for Z3 sensitivity, StackDFS)
- `incr_nat`/`tick` duplicated in KahnTopologicalSort (local copy retained for Z3 sensitivity)
- `Graph.Common.fst` consolidates shared definitions; QueueBFS and StackDFS migrated, others retain local copies due to Z3 proof sensitivity (documented in `Graph.Common` header)

### Graph Representation Mismatch: 🔶 Known Issue

- `DFS.Spec` uses 2D adjacency matrix (`Seq.seq (Seq.seq int)`)
- All Pulse implementations + `TopologicalSort.Spec` use flat 1D matrix (`Seq.seq int`)
- `DFS.TopologicalSort` bridges the two representations via `adj_equiv` + `has_edge_equiv`
- `BFS.DistanceSpec` uses `Seq.seq bool` (distinct from all others)

### Z3 Resource Usage: ✅ Reasonable

- Maximum rlimit: 600 (StackDFS, QueueBFS) — acceptable for complex Pulse invariants
- Typical: 200 for helpers, 30–50 for spec lemmas
- Fuel: consistently `--fuel 2 --ifuel 1` for Pulse code

### Stale Comments: ✅ Fixed

1. `TopologicalSort.Verified:431` — ✅ Already says "fully proved" (was previously stale)
2. `DFS.WhitePath:1099` — ✅ Already says "fully proved" (was previously stale)
3. `BFS.DistanceSpec:9` — ✅ **Fixed**: updated "harder — admitted" to "harder direction — fully proved via bfs_correctness"
