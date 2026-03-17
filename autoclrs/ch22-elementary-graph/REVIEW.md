# Chapter 22: Elementary Graph Algorithms — Review

**Date:** 2026-03-16
**Reviewer:** Copilot audit agent
**Files:** 19 (14,708 lines total)
**Algorithms:** BFS (§22.2), DFS (§22.3), Topological Sort (§22.4)

---

## Executive Summary

Ch22 is the strongest chapter in proof completeness: **zero admits** across all
~14,700 lines and **19/19 files verified** (all `.checked` caches current). The
chapter proves major CLRS theorems (parenthesis theorem, white-path theorem,
BFS shortest-path optimality, edge classification, cycle⟺back-edge,
topological sort correctness) and provides three Pulse implementations with
verified O(V²) complexity bounds.

The main weaknesses are: (1) high z3rlimits in Pulse implementations signaling
fragile proofs, (2) rubric non-compliance (inline lemmas rather than separate
Lemmas/Complexity files), (3) graph representation proliferation
(`has_edge` defined 6× with 4+ signatures), and (4) Spec↔Impl disconnect for
BFS and DFS.

---

## File Inventory

| # | File | Lines | `.checked` | Rubric Role | Algorithm |
|---|------|------:|:----------:|-------------|-----------|
| 1 | `CLRS.Ch22.Graph.Common.fst` | 93 | ✅ | Shared infra | All Pulse impls |
| 2 | `CLRS.Ch22.BFS.Spec.fst` | 166 | ✅ | **Spec** | BFS |
| 3 | `CLRS.Ch22.BFS.DistanceSpec.fst` | 1,116 | ✅ | **Spec** (shortest-path) | BFS |
| 4 | `CLRS.Ch22.BFS.Impl.fst` | 1,093 | ✅ | **Impl** (Pulse) | BFS |
| 5 | `CLRS.Ch22.BFS.Impl.fsti` | 90 | ✅ | **Impl** interface | BFS |
| 6 | `CLRS.Ch22.IterativeBFS.fst` | 265 | ✅ | **Impl** (Pulse, alt) | BFS (relaxation) |
| 7 | `CLRS.Ch22.DFS.Spec.fst` | 2,929 | ✅ | **Spec** + Lemmas | DFS |
| 8 | `CLRS.Ch22.DFS.WhitePath.fst` | 1,103 | ✅ | **Lemmas** | DFS |
| 9 | `CLRS.Ch22.DFS.TopologicalSort.fst` | 731 | ✅ | **Lemmas** (bridge) | DFS→TopoSort |
| 10 | `CLRS.Ch22.DFS.Impl.fst` | 1,198 | ✅ | **Impl** (Pulse) | DFS |
| 11 | `CLRS.Ch22.DFS.Impl.fsti` | 96 | ✅ | **Impl** interface | DFS |
| 12 | `CLRS.Ch22.TopologicalSort.Spec.fst` | 243 | ✅ | **Spec** | TopologicalSort |
| 13 | `CLRS.Ch22.TopologicalSort.Lemmas.fsti` | 421 | ✅ | **Lemmas** interface | TopologicalSort |
| 14 | `CLRS.Ch22.TopologicalSort.Lemmas.fst` | 629 | ✅ | **Lemmas** | TopologicalSort |
| 15 | `CLRS.Ch22.TopologicalSort.Verified.fst` | 608 | ✅ | **Lemmas** (bridge) | TopologicalSort |
| 16 | `CLRS.Ch22.TopologicalSort.Impl.Defs.fsti` | 1,293 | ✅ | **Impl** defs iface | TopologicalSort |
| 17 | `CLRS.Ch22.TopologicalSort.Impl.Defs.fst` | 1,827 | ✅ | **Impl** defs | TopologicalSort |
| 18 | `CLRS.Ch22.TopologicalSort.Impl.fst` | 751 | ✅ | **Impl** (Pulse) | TopologicalSort |
| 19 | `CLRS.Ch22.TopologicalSort.Impl.fsti` | 56 | ✅ | **Impl** interface | TopologicalSort |

---

## Proof Quality

### Admits / Assumes
- **Zero** `admit()`, `admit_()`, `assume()`, `assume_()` across all files.

### CLRS Theorems Proved
| Theorem | File(s) |
|---------|---------|
| Parenthesis Theorem (Thm 22.7) | `DFS.Spec` |
| White-Path Theorem (Thm 22.9) | `DFS.WhitePath` |
| Edge Classification (tree/back/forward/cross) | `DFS.Spec` |
| Cycle ⟺ Back Edge (Thm 22.11) | `DFS.Spec` |
| BFS Edge Property (Lemma 22.1) | `BFS.Spec` |
| BFS Shortest-Path Optimality (Thm 22.5) | `BFS.DistanceSpec` |
| DFS-based topological sort correctness | `DFS.TopologicalSort` |
| Topological order ⟹ DAG | `TopologicalSort.Spec` |
| Kahn's algorithm correctness + completeness | `TopologicalSort.Verified` |

### Functional Correctness (Impl files)
- **BFS.Impl**: Complete reachability characterization (forward + reverse)
  - Discovered ⟹ `reachable_in adj n source v dist[v]`
  - Reachable ⟹ discovered (`scolor[v] ≠ 0`)
- **DFS.Impl**: `pred_edge_ok` — predecessor tree is valid subgraph
- **TopologicalSort.Impl**: Full chain Spec → Lemmas → Verified → Impl

### Complexity Verification
- BFS.Impl: ghost tick ≤ 2V²
- DFS.Impl: ghost tick ≤ 2V²
- TopologicalSort.Impl: ghost tick ≤ V²
- IterativeBFS: no complexity tracking (O(V³) by construction)

---

## Proof Stability Assessment

### High z3rlimits (fragility indicators)

All z3rlimits have been reduced to ≤ 200 (previously max was 2400).

| File | Line | z3rlimit (old → new) | Function/Section |
|------|------|---------------------|------------------|
| `BFS.Impl.fst` | 757 | **2400 → 200** | Main `queue_bfs` loop |
| `DFS.Impl.fst` | 555 | **800 → 200** | `dfs_visit` inner loop |
| `DFS.Impl.fst` | 958 | **600 → 200** | `stack_dfs` outer loop |
| `BFS.Impl.fst` | 646 | **600 → 200** | `maybe_discover` |

### Makefile flags
```makefile
OTHERFLAGS := ... --ext optimize_let_vc=false --ext fly_deps=false ...
```
Both `optimize_let_vc` and `fly_deps` are disabled because they break proofs in
TopologicalSort.Impl and TopologicalSort.Verified. This is a stability red
flag — proofs should be robust to these optimizations.

---

## Rubric Compliance

### Per-algorithm assessment

**BFS:**
- ✅ Spec: `BFS.Spec.fst`, `BFS.DistanceSpec.fst`
- ❌ Lemmas.fst / Lemmas.fsti: lemmas are inline in Spec files
- ❌ Complexity.fst / Complexity.fsti: complexity is inline (ghost ticks)
- ✅ Impl.fst / Impl.fsti: `BFS.Impl.fst` + `BFS.Impl.fsti`

**DFS:**
- ✅ Spec: `DFS.Spec.fst` (2,929 lines — very large, combines spec + lemmas)
- ⚠️ Lemmas: `DFS.WhitePath.fst` exists but no `.fsti` interface; other lemmas inline
- ❌ Complexity.fst / Complexity.fsti: complexity is inline (ghost ticks)
- ✅ Impl.fst / Impl.fsti: `DFS.Impl.fst` + `DFS.Impl.fsti`

**TopologicalSort:**
- ✅ Spec: `TopologicalSort.Spec.fst`
- ✅ Lemmas.fst / Lemmas.fsti: `TopologicalSort.Lemmas.fst` + `.fsti`
- ❌ Complexity.fst / Complexity.fsti: complexity is inline (ghost ticks)
- ✅ Impl.fst / Impl.fsti: full chain Spec → Lemmas → Verified → Impl.Defs → Impl
- ✅ Bridge: `DFS.TopologicalSort.fst` connects DFS-based + Kahn's proofs

---

## Architectural Issues

### 1. Graph representation proliferation
`has_edge` is defined **6 times** with 4+ different type signatures:
- `Graph.Common`: `(seq int, nat, nat, nat) → prop` (flat matrix, prop return)
- `BFS.Spec`: `(nat, seq int, nat, nat) → bool` (flat matrix, bool return)
- `BFS.DistanceSpec`: `(nat, seq bool, nat, nat) → bool` (bool adjacency)
- `DFS.Spec`: `(nat, seq (seq int), nat, nat) → bool` (2D adjacency)
- `TopologicalSort.Spec`: `(nat, seq int, nat, nat) → bool` (flat, bool return)
- `IterativeBFS`: `(seq int, nat, nat, nat) → prop` (copy of Graph.Common)

### 2. Code duplication
- `reachable_in` duplicated in `IterativeBFS.fst` (identical to `Graph.Common`)
- `has_edge` + `reachable_in` duplicated in `IterativeBFS.fst`
- Documented as Z3 proof sensitivity

### 3. Spec↔Impl disconnect
- BFS: Spec uses `seq int` flat, DistanceSpec uses `seq bool`, Impl uses
  `seq int` flat — but Impl proves its own invariants independently, not via Spec
- DFS: Spec uses 2D `seq (seq int)`, Impl uses flat `seq int` —
  `DFS.TopologicalSort.fst` bridges them but only for the topological sort case

### 4. Stale documentation
- `TIMESTAMP_TRACKING_NOTES.md` documents an `assume_` that no longer exists
  in the code (the assume has been eliminated). File should be removed or
  updated.

---

## Spec Validation (ImplTest)

Three spec validation tests were written and verified (zero admits, zero
assumes) following the methodology from https://arxiv.org/abs/2406.09757.

### Test Files

| File | Status | Lines |
|------|--------|------:|
| `CLRS.Ch22.BFS.ImplTest.fst` | ✅ Verified | ~190 |
| `CLRS.Ch22.DFS.ImplTest.fst` | ✅ Verified | ~190 |
| `CLRS.Ch22.TopologicalSort.ImplTest.fst` | ✅ Verified | ~190 |

All tests use the same 3-vertex DAG: 0→1, 1→2. See individual
`ImplTest.md` files for detailed analysis.

### Summary of Findings

| Algorithm | Precondition | Postcondition Precision | Spec Issue |
|-----------|-------------|------------------------|------------|
| **BFS** | ✅ Satisfiable | ✅ Strong for unique-path graphs — proves completeness, dist[0]=0, dist[1]=1, dist[2]=2 | Missing shortest-path guarantee for general graphs |
| **DFS** | ✅ Satisfiable | ⚠️ Partial — proves all BLACK, timestamps, pred_edge_ok, but no graph-theoretic properties | Spec↔Impl disconnect (known) |
| **TopologicalSort** | ✅ Satisfiable (DAG proof via witness) | ✅ Strong — proves valid topo order, distinct, valid indices | Minor: exact output not determinable |

### Spec Incompleteness Issues Found

1. **BFS Impl.fsti — Missing shortest-path property (P1)**
   - The postcondition says `reachable_in sadj n source w dist[w]` (path EXISTS
     of dist[w] steps) but does NOT say `∀k. reachable_in ⟹ dist[w] ≤ k`
     (dist is SHORTEST).
   - This property IS proven in `BFS.DistanceSpec.fst` (Theorem 22.5) but is
     not exposed through the implementation interface.
   - **Fix:** Add shortest-path clause to `BFS.Impl.fsti` postcondition.

2. **DFS Impl.fsti — Missing graph-theoretic properties (P2)**
   - Edge classification, white-path theorem, cycle⟺back-edge are all proven
     in `DFS.Spec.fst` but not exposed through `DFS.Impl.fsti`.
   - The Spec uses 2D `seq (seq int)` while Impl uses flat `seq int`, making
     bridging difficult without representation-conversion lemmas.
   - **Fix:** Add bridging lemmas connecting DFS.Spec to DFS.Impl.

3. **TopologicalSort Impl.fsti — Output determinism (P3, minor)**
   - For graphs with a unique topological order, the postcondition does not
     uniquely determine the output. This requires a combinatorial argument
     combining distinctness + topological constraints.
   - **Impact:** Minor; the postcondition is sufficient for practical uses.

---

## Checklist — Priority Items

### P0 — Immediate (correctness/hygiene)
- [x] Verify zero admits/assumes (confirmed: none)
- [x] Verify all 19/19 files have `.checked` caches (confirmed)
- [x] Update stale `TIMESTAMP_TRACKING_NOTES.md` (marked RESOLVED, assume eliminated)

### P1 — Proof Stability (high priority)
- [x] Profile verification times for all files (see table above)
- [x] Reduce z3rlimit 2400 → 200 in `BFS.Impl.fst:757` (main loop) ✅
- [x] Reduce z3rlimit 800 → 200 in `DFS.Impl.fst:555` (dfs_visit) ✅
- [x] Reduce z3rlimit 600 → 200 in `DFS.Impl.fst:958` (stack_dfs) ✅
- [x] Reduce z3rlimit 600 → 200 in `BFS.Impl.fst:646` (inner loop) ✅
- [x] Fix 14× Warning 337 (duplicate decreases) in `TopologicalSort.Lemmas.fsti` ✅
- [ ] Investigate `optimize_let_vc=false` / `fly_deps=false` necessity

### P2 — Rubric Compliance (medium priority)
- [ ] Extract BFS lemmas from `BFS.Spec.fst` into `BFS.Lemmas.fst/.fsti`
- [ ] Create `BFS.Complexity.fst/.fsti` (formalize O(V+E) bound)
- [ ] Split `DFS.Spec.fst` (2,929 lines) into Spec + Lemmas
- [ ] Create `DFS.Lemmas.fsti` interface for `DFS.WhitePath.fst`
- [ ] Create `DFS.Complexity.fst/.fsti`
- [ ] Create `TopologicalSort.Complexity.fst/.fsti`

### P3 — Code Quality (lower priority)
- [ ] Unify `has_edge` signatures or document representation rationale
- [ ] Eliminate `reachable_in` duplication in `IterativeBFS.fst`
- [ ] Add Spec↔Impl bridging lemmas for BFS (like DFS.TopologicalSort does)
- [ ] Add Spec↔Impl bridging lemmas for DFS (beyond topological sort)

---

## Verification Profile (wall-clock, single-threaded)

| File | Time | z3rlimit max | Risk | Notes |
|------|-----:|-------------|------|-------|
| `DFS.Impl.fst` | **298s** | 200 | Low | Slowest file, stack DFS (was z3rlimit 800) |
| `TopologicalSort.Verified.fst` | 128s | — | Medium | split_queries warning |
| `TopologicalSort.Impl.fst` | 105s | — | Low | Kahn's Pulse impl |
| `BFS.Impl.fst` | **84s** | 200 | Low | Queue BFS (was z3rlimit 2400) |
| `DFS.Spec.fst` | 68s | 50 | Low | 2,929 lines pure spec |
| `DFS.TopologicalSort.fst` | 42s | — | Medium | 2× split_queries warning |
| `DFS.WhitePath.fst` | 31s | — | Low | |
| `IterativeBFS.fst` | 28s | 200 | Low | Self-contained alt |
| `TopologicalSort.Impl.Defs.fst` | 26s | 100 | Low | |
| `BFS.DistanceSpec.fst` | 24s | 80 | Low | |
| `TopologicalSort.Lemmas.fst` | 13s | — | Low | ~~14× warning 337~~ fixed |
| Other (8 files) | ≤6s each | — | — | |
| **Total** | **~870s** | | | ~14.5 min sequential |

### Warnings observed
- ~~**14× Warning 337** in `TopologicalSort.Lemmas.fst`: duplicate decreases clauses~~ **FIXED**
- **1× Warning 349** in `TopologicalSort.Verified.fst:558`: relies on split_queries
- **2× Warning 349** in `DFS.TopologicalSort.fst:318,487`: relies on split_queries
- **1× Warning 328** in `TopologicalSort.Impl.Defs.fst:1503`: unused recursive binding
- **1× Warning 328** in `DFS.TopologicalSort.fst:310`: unused recursive binding
