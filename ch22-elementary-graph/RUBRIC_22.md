# Chapter 22: Elementary Graph Algorithms — Rubric Compliance

**Files:** 16 (15 `.fst` + 1 `.fsti`) | **Lines:** 13,637 | **Verified:** All (`.checked` present)
**Date:** 2025-07-14

---

## Current File Inventory

| # | File | Lines | Layer | Role |
|---|------|------:|-------|------|
| 1 | `CLRS.Ch22.BFS.Spec.fst` | 166 | Spec | Pure BFS level-set specification |
| 2 | `CLRS.Ch22.BFS.DistanceSpec.fst` | 1,116 | Spec | BFS shortest-path distance infrastructure |
| 3 | `CLRS.Ch22.DFS.Spec.fst` | 2,929 | Spec | Pure DFS with timestamps, parenthesis theorem, edge classification |
| 4 | `CLRS.Ch22.DFS.WhitePath.fst` | 1,103 | Spec | White-path theorem (CLRS Thm 22.9) both directions |
| 5 | `CLRS.Ch22.DFS.TopologicalSort.fst` | 731 | Spec | DFS-based topological sort (§22.4), bridges DFS.Spec ↔ TS.Spec |
| 6 | `CLRS.Ch22.TopologicalSort.Spec.fst` | 243 | Spec | Topological order definition, DAG property |
| 7 | `CLRS.Ch22.TopologicalSort.Lemmas.fst` | 692 | Lemmas | Helper lemmas for Kahn's correctness proof |
| 8 | `CLRS.Ch22.TopologicalSort.Verified.fst` | 608 | Lemmas | Full correctness proof: Kahn's → `is_topological_order` |
| 9 | `CLRS.Ch22.Graph.Common.fst` | 78 | Shared | `has_edge`, `reachable_in`, `tick`, `product_strict_bound` |
| 10 | `CLRS.Ch22.Graph.Complexity.fst` | 69 | Shared | O(V²) meta-bound for adjacency-matrix algorithms |
| 11 | `CLRS.Ch22.IterativeBFS.fst` | 265 | Impl | Relaxation-based BFS (Bellman-Ford-like, O(V³)) |
| 12 | `CLRS.Ch22.QueueBFS.fst` | 661 | Impl | **Canonical** queue-based BFS (CLRS §22.2, O(V²)) |
| 13 | `CLRS.Ch22.StackDFS.fst` | 1,105 | Impl | **Canonical** stack-based DFS (CLRS §22.3, O(V²)) |
| 14 | `CLRS.Ch22.KahnTopologicalSort.Defs.fst` | 1,827 | Impl | Kahn's topological sort: predicate lemmas |
| 15 | `CLRS.Ch22.KahnTopologicalSort.Defs.fsti` | 1,293 | Impl | Kahn's topological sort: interface (predicates + `val` signatures) |
| 16 | `CLRS.Ch22.KahnTopologicalSort.fst` | 751 | Impl | Kahn's topological sort: Pulse implementation |

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
| `Lemmas.fst` | `CLRS.Ch22.BFS.Lemmas.fst` | ❌ Missing | — | Properties spread across `BFS.Spec`, `BFS.DistanceSpec` |
| `Lemmas.fsti` | `CLRS.Ch22.BFS.Lemmas.fsti` | ❌ Missing | — | No interface file |
| `Complexity.fst` | `CLRS.Ch22.BFS.Complexity.fst` | 🔶 Partial | `Graph.Complexity.fst` (shared) | O(V²) meta-bound; no BFS-specific proof file |
| `Complexity.fsti` | `CLRS.Ch22.BFS.Complexity.fsti` | ❌ Missing | — | No interface file |
| `Impl.fst` | `CLRS.Ch22.BFS.Impl.fst` | 🔶 Name differs | `QueueBFS.fst` (661 lines) | Correct implementation, non-standard name |
| `Impl.fsti` | `CLRS.Ch22.BFS.Impl.fsti` | ❌ Missing | — | No interface file for QueueBFS |

**Additional BFS files (outside rubric):**
- `BFS.DistanceSpec.fst` (1,116 lines) — path infrastructure for Thm 22.5 (hard direction unproved)
- `IterativeBFS.fst` (265 lines) — alternative relaxation-based BFS (self-contained)

### DFS (§22.3)

| Rubric File | Expected Name | Status | Actual File | Notes |
|-------------|---------------|--------|-------------|-------|
| `Spec.fst` | `CLRS.Ch22.DFS.Spec.fst` | ✅ Present | `DFS.Spec.fst` (2,929 lines) | Outstanding: parenthesis thm, edge classification, cycle detection |
| `Lemmas.fst` | `CLRS.Ch22.DFS.Lemmas.fst` | 🔶 Name differs | `DFS.WhitePath.fst` (1,103 lines) | White-path theorem only; other lemmas inline in Spec |
| `Lemmas.fsti` | `CLRS.Ch22.DFS.Lemmas.fsti` | ❌ Missing | — | No interface file |
| `Complexity.fst` | `CLRS.Ch22.DFS.Complexity.fst` | 🔶 Partial | `Graph.Complexity.fst` (shared) | O(V²) meta-bound; ghost ticks in StackDFS |
| `Complexity.fsti` | `CLRS.Ch22.DFS.Complexity.fsti` | ❌ Missing | — | No interface file |
| `Impl.fst` | `CLRS.Ch22.DFS.Impl.fst` | 🔶 Name differs | `StackDFS.fst` (1,105 lines) | Correct implementation, non-standard name |
| `Impl.fsti` | `CLRS.Ch22.DFS.Impl.fsti` | ❌ Missing | — | No interface file for StackDFS |

### Topological Sort (§22.4) — DFS-Based (CLRS Canonical)

| Rubric File | Expected Name | Status | Actual File | Notes |
|-------------|---------------|--------|-------------|-------|
| `Spec.fst` | `CLRS.Ch22.TopologicalSort.Spec.fst` | ✅ Present | `TopologicalSort.Spec.fst` (243 lines) | `is_topological_order` definition, DAG proof |
| `Lemmas.fst` | `CLRS.Ch22.TopologicalSort.Lemmas.fst` | ✅ Present | `TopologicalSort.Lemmas.fst` (692 lines) | `strong_order_inv` and helpers |
| `Lemmas.fsti` | `CLRS.Ch22.TopologicalSort.Lemmas.fsti` | ❌ Missing | — | No interface file |
| `Complexity.fst` | `CLRS.Ch22.TopologicalSort.Complexity.fst` | ❌ Missing | — | Kahn's has ghost ticks (≤ V²), no separate file |
| `Complexity.fsti` | `CLRS.Ch22.TopologicalSort.Complexity.fsti` | ❌ Missing | — | No interface file |
| `Impl.fst` | `CLRS.Ch22.TopologicalSort.Impl.fst` | 🔶 Split | `KahnTopologicalSort.fst` (751 lines) | Kahn's algorithm (not CLRS canonical) |
| `Impl.fsti` | `CLRS.Ch22.TopologicalSort.Impl.fsti` | 🔶 Exists (different name) | `KahnTopologicalSort.Defs.fsti` (1,293 lines) | Interface exists for Kahn's definitions |

**Additional Topological Sort files:**
- `DFS.TopologicalSort.fst` (731 lines) — bridges DFS.Spec to TopologicalSort.Spec (the CLRS §22.4 algorithm)
- `TopologicalSort.Verified.fst` (608 lines) — full Kahn's correctness proof
- `KahnTopologicalSort.Defs.fst` (1,827 lines) — Kahn's predicate lemmas

### Summary Counts

| | ✅ Present | 🔶 Partial/Renamed | ❌ Missing | Total Expected |
|---|:---:|:---:|:---:|:---:|
| **Spec.fst** | 3 | 0 | 0 | 3 |
| **Lemmas.fst** | 1 | 1 | 1 | 3 |
| **Lemmas.fsti** | 0 | 0 | 3 | 3 |
| **Complexity.fst** | 0 | 2 | 1 | 3 |
| **Complexity.fsti** | 0 | 0 | 3 | 3 |
| **Impl.fst** | 0 | 3 | 0 | 3 |
| **Impl.fsti** | 0 | 1 | 2 | 3 |
| **Total** | **4** | **7** | **10** | **21** |

---

## Detailed Action Items

### Priority 1 — Specification & Proof Gaps

| # | Action | Impact | Effort | Files |
|---|--------|--------|--------|-------|
| 1.1 | **Prove BFS shortest-path optimality (CLRS Thm 22.5, hard direction)** — `BFS.DistanceSpec` has 1,116 lines of infrastructure but the key lemma "no shorter path exists" is missing | Core BFS correctness | High | `BFS.DistanceSpec.fst` |
| 1.2 | **Add reachability postcondition to QueueBFS** — currently proves "visited ⟹ dist ≥ 0" but not "reachable ⟹ visited" (IterativeBFS proves the stronger property) | Spec completeness | Medium | `QueueBFS.fst` |
| 1.3 | **Add reachability postcondition to StackDFS** — proves "all BLACK with valid timestamps" but not "reachable ⟹ visited" | Spec completeness | Low | `StackDFS.fst` |

### Priority 2 — Missing Interface Files (`.fsti`)

| # | Action | Impact | Effort | Files to Create |
|---|--------|--------|--------|-----------------|
| 2.1 | **Create `BFS.Lemmas.fsti`** — extract key BFS lemma signatures from `BFS.Spec` and `BFS.DistanceSpec` | Rubric compliance | Low | `CLRS.Ch22.BFS.Lemmas.fsti` |
| 2.2 | **Create `DFS.Lemmas.fsti`** — interface for parenthesis theorem, white-path theorem, edge classification | Rubric compliance | Low | `CLRS.Ch22.DFS.Lemmas.fsti` |
| 2.3 | **Create `TopologicalSort.Lemmas.fsti`** — interface for `strong_order_inv` and helper signatures | Rubric compliance | Low | `CLRS.Ch22.TopologicalSort.Lemmas.fsti` |
| 2.4 | **Create `BFS.Impl.fsti`** — public signature for QueueBFS entry point | Rubric compliance | Low | `CLRS.Ch22.BFS.Impl.fsti` (or `QueueBFS.fsti`) |
| 2.5 | **Create `DFS.Impl.fsti`** — public signature for StackDFS entry point | Rubric compliance | Low | `CLRS.Ch22.DFS.Impl.fsti` (or `StackDFS.fsti`) |

### Priority 3 — Missing Complexity Files

| # | Action | Impact | Effort | Files to Create |
|---|--------|--------|--------|-----------------|
| 3.1 | **Create `BFS.Complexity.fst` / `.fsti`** — extract QueueBFS ghost-tick bound (≤ 2·V² ticks) into standalone complexity proof | Rubric compliance | Medium | `CLRS.Ch22.BFS.Complexity.fst/.fsti` |
| 3.2 | **Create `DFS.Complexity.fst` / `.fsti`** — extract StackDFS amortized bound (≤ 2·V² ticks) into standalone complexity proof | Rubric compliance | Medium | `CLRS.Ch22.DFS.Complexity.fst/.fsti` |
| 3.3 | **Create `TopologicalSort.Complexity.fst` / `.fsti`** — extract Kahn's bound (≤ V² ticks) | Rubric compliance | Medium | `CLRS.Ch22.TopologicalSort.Complexity.fst/.fsti` |

### Priority 4 — Naming / Organization

| # | Action | Impact | Effort | Notes |
|---|--------|--------|--------|-------|
| 4.1 | Consider renaming `QueueBFS.fst` → `BFS.Impl.fst` | Rubric naming | Low | May break imports in other chapters |
| 4.2 | Consider renaming `StackDFS.fst` → `DFS.Impl.fst` | Rubric naming | Low | May break imports |
| 4.3 | **Create `BFS.Lemmas.fst`** — consolidate BFS lemmas from `BFS.Spec` + `BFS.DistanceSpec` | Rubric structure | Medium | Currently split across two Spec files |
| 4.4 | **Fix stale comment in `TopologicalSort.Verified:431`** — says "we admit two standard lemmas" but both are now fully proved | Accuracy | Trivial | One-line fix |
| 4.5 | **Fix stale comment in `DFS.WhitePath:1099`** — references "assume val predicates" that no longer exist | Accuracy | Trivial | One-line fix |

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

### Stale Comments: 🔶 Two Found

1. `TopologicalSort.Verified:431` — claims "we admit two standard lemmas" but both are now proved
2. `DFS.WhitePath:1099` — references "assume val predicates" that no longer exist
