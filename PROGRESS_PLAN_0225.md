# AutoCLRS Progress Audit — 2025-02-25

**Scope**: Full audit of every unproven obligation, broken file, and remaining task.
Decomposition into independent agent tasks for parallel execution.

**Codebase stats**:
- 182 F*/Pulse files, ~73,800 lines across 23 chapters + common
- **2 total unproven obligations** (was 14; 12 eliminated by agents, down from 97 at AUDIT_0223)
  - `ch23/Kruskal.fst:313` — `assume_` for UF forest acyclicity (TRUE but unproven; needs ~300 lines UF soundness)
  - `ch26/MaxFlow.Spec.fst:633` — `assume` for MFMC strong duality (needs ~500 lines graph theory)
- 0 files broken (DFS.WhitePath.fst fixed)
- Multiple files have uncommitted changes (RadixSort, Huffman, WhitePath, MaxFlow.Complexity)

**Change since AUDIT_0223 (2025-02-23): 97 → 2 unproven obligations (−95, 98% reduction)**

---

## Complete Unproven Obligations Inventory

| # | File | Type | Line | Description |
|---|------|------|------|-------------|
| ~~1~~ | ~~`ch08/RadixSort.MultiDigit.fst`~~ | ~~`admit()`~~ | ~~394~~ | ~~ELIMINATED~~ |
| ~~2~~ | ~~`ch08/RadixSort.MultiDigit.fst`~~ | ~~`admit()`~~ | ~~415~~ | ~~ELIMINATED~~ |
| ~~3~~ | ~~`ch16/Huffman.fst`~~ | ~~`admit()`~~ | ~~872~~ | ~~ELIMINATED~~ |
| ~~4~~ | ~~`ch16/Huffman.fst`~~ | ~~`admit()`~~ | ~~901~~ | ~~ELIMINATED~~ |
| ~~5~~ | ~~`ch21/UnionFind.Spec.fst`~~ | ~~`assume()`~~ | ~~126~~ | ~~ELIMINATED~~ |
| ~~6~~ | ~~`ch22/DFS.WhitePath.fst`~~ | ~~`admit()`~~ | ~~671~~ | ~~ELIMINATED~~ |
| ~~7~~ | ~~`ch22/DFS.WhitePath.fst`~~ | ~~`admit()`~~ | ~~781~~ | ~~ELIMINATED~~ |
| ~~8~~ | ~~`ch22/DFS.WhitePath.fst`~~ | ~~`admit()`~~ | ~~793~~ | ~~ELIMINATED~~ |
| 9 | `ch23/Kruskal.fst` | `assume_` | 313 | Forest acyclicity via UF soundness (TRUE but unproven; was FALSE `assume val` at line 81) |
| ~~10~~ | ~~`ch23/Kruskal.SortedEdges.fst`~~ | ~~`assume()`~~ | ~~266~~ | ~~ELIMINATED: refactored to use Kruskal.Spec's proven `kruskal_step`~~ |
| ~~11~~ | ~~`ch24/ShortestPath.Triangle.fst`~~ | ~~`admit()`~~ | ~~141~~ | ~~ELIMINATED: `sp_dist_k_stabilize` fully proven~~ |
| ~~12~~ | ~~`ch26/MaxFlow.Spec.fst`~~ | ~~`assume()`~~ | ~~354~~ | ~~ELIMINATED: weak duality fully proven via `lemma_flow_value_eq_net_flow` + `lemma_net_flow_le_cut_capacity`~~ |
| 13 | `ch26/MaxFlow.Spec.fst` | `assume()` | 633 | MFMC strong duality: when no augmenting path exists, flow = min-cut capacity |
| ~~14~~ | ~~`ch26/MaxFlow.Complexity.fst`~~ | ~~`assume()`~~ | ~~102~~ | ~~ELIMINATED: `lemma_transfer_critical` proves existential transfer~~ |

### Broken Files

| File | Error | Cause |
|------|-------|-------|
| ~~`ch22/DFS.WhitePath.fst`~~ | ~~Fixed~~ | ~~Now compiles~~ |

---

## Completed Agent Tasks (since PROGRESS_PLAN)

| Agent | Task | Status | Admits Eliminated |
|-------|------|--------|-------------------|
| AGENT3 | MaxSubarray True Optimality | ✅ Done | spec gap → 0 |
| AGENT4 | MST Exchange Lemma | ✅ Done | 1 → 0 |
| AGENT5 | Kruskal.Spec Completion | ✅ Done | 9 → 0 |
| AGENT8 | BellmanFord Neg Cycle + Equality | ✅ Done | 3 → 0 |
| AGENT9 | Dijkstra Triangle Ineq + Equality | ✅ Done | 2 → 0, postcondition `==` |
| AGENT11 | KMP Match Completeness | ✅ Done | spec gap → 0 |
| AGENT12 | Floyd-Warshall APSP | ✅ Done | spec gap → 0 |
| AGENT2 | DFS.Spec assume vals | ✅ Done | 7 assume vals → 0 |
| (untracked) | Prim.Spec admits | ✅ Done | 6 → 0 |
| (untracked) | BFS.DistanceSpec admits | ✅ Done | 2 → 0 |
| TASK_F | UnionFind ranks_bounded | ✅ Done | 1 assume → 0 (counting argument, no ranks_bounded needed) |
| TASK_G | MaxFlow weak_duality + critical_edge | ✅ Done | 3 assumes → 1 admit + 1 assume (weak_duality FULLY PROVEN, critical_edge 1 admit, MFMC 1 assume) |
| TASK_A | sp_dist_k_stabilize (pigeonhole) | ✅ Done | 1 admit → 0 (chain-of-predecessors + FStar.Fin.pigeonhole, ~160 lines) |

---

## Remaining Agent Tasks

AGENTS MUST ALL WORK ON THE SAME BRANCH BUT WORK ON DISJOINT FILES.

Each agent MUST work on different files with no overlap, so they can run
simultaneously without conflicts (except for this file).

Agent must commit only the files they work on, repeatedly as they reach
meaningful checkpoints.

When an agent finishes, they should update this file with their
results and learnings, using `flock` to avoid conflicts.


### TASK A: sp_dist_k_stabilize (Dijkstra dependency) — ~~1 admit~~ ✅ DONE

**File:** `ch24-sssp/CLRS.Ch24.ShortestPath.Triangle.fst` (line 141)
**Completed by:** TASK_A agent, 2026-02-26.

**What was proved:** `sp_dist_k(s,v,n) == sp_dist_k(s,v,n-1)` for non-negative weights.

**Proof approach (chain-of-predecessors + pigeonhole, ~160 lines):**
1. `find_improving_predecessor` — extracts a witness predecessor when `min_over_predecessors` improves
2. `chain_vertex` — recursively builds chain of n+1 vertices with strict improvement at each level
3. `chain_B_property` — proves the edge inequality between consecutive chain vertices
4. `chain_telescoping` — proves `sp_dist_k(s, chain[i], n-i) ≥ sp_dist_k(s, chain[j], n-j)` for `i < j`
5. `sp_dist_k_stabilize` — builds chain as Seq, applies `FStar.Fin.pigeonhole`, derives contradiction
   via telescoping + monotonicity (squeezed equality vs strict improvement)

**Key technique:** Made `find_improving_predecessor` `[@@"opaque_to_smt"]` to prevent excessive
unfolding in the SMT solver — the ensures clause is sufficient for downstream proofs.

This also completes the `sp_dist_triangle_ineq` proof (which depended on stabilization),
completing the Dijkstra proof chain with zero admits.

---

### TASK B: Huffman forest management — 2 admits

**File:** `ch16-greedy/CLRS.Ch16.Huffman.fst` (lines 872, 901)
**Currently assigned to:** Active WIP (uncommitted changes). **⚠️ Being worked on.**

**What to prove:**
1. Line 872: After removing entry at index k1 from the active forest, the second index idx2
   can still be found via `find_entry_by_idx` in the remaining forest. Needs a lemma that
   `find_entry_by_idx` succeeds for idx2 in `list_remove_at active0 k1` when idx1 ≠ idx2.
2. Line 901: After the loop body runs n-1 times (each iteration removes 2 entries and adds 1),
   the final forest has exactly 1 entry. Extracting it leaves `forest_own []` which equals `emp`.
   Need `forest_own_nil` or explicit length tracking.

**Dependencies:** `CLRS.Ch16.Huffman.Spec`, `Pulse.Lib.PriorityQueue`
**Build command:**
```bash
fstar.exe --include $(realpath ../pulse)/out/lib/pulse --include common --include ch16-greedy \
  --warn_error -321 --warn_error @247 --ext optimize_let_vc --ext fly_deps \
  --cache_dir _cache ch16-greedy/CLRS.Ch16.Huffman.fst
```

---

### TASK C: DFS White-Path Theorem backward direction — 3 admits + 1 compile error

**File:** `ch22-elementary-graph/CLRS.Ch22.DFS.WhitePath.fst` (lines 573, 671, 781, 793)
**Currently assigned to:** Active WIP (uncommitted changes). **⚠️ Being worked on.**
**Status: BROKEN (doesn't compile)**

**Compile error:** `Identifier not found: get_white_neighbors_edges` at line 573.
This function is referenced but not defined.

**What to prove:** The backward direction of the White-Path Theorem (CLRS Theorem 22.9):
if vertex v is a descendant of u in the DFS tree, then at time d[u] there exists a white path
from u to v.

**Admits:**
1. Line 671: Timestamp containment — when a vertex is discovered during `dfs_visit(w, st)`,
   it gets finished before `dfs_visit` returns, so `st1.f[u] > 0`.
2. Line 781: Root ordering — `d_top[u_start]` vs `du` when `u_start` is the DFS root.
   The invariant is stated incorrectly for this case.
3. Line 793: Relative ordering — within a DFS subtree, two vertices' discovery times can't
   be compared directly from `timestamps_in_range` alone.

**Key difficulty:** The backward direction requires tracking that at the moment u is discovered,
all vertices on the path to v are still white. This requires reasoning about DFS execution
state at a specific intermediate timestamp, which is fundamentally harder than the forward
direction.

**Dependencies:** `CLRS.Ch22.DFS.Spec` (0 admits, fully proven)
**Build command:**
```bash
fstar.exe --include $(realpath ../pulse)/out/lib/pulse --include common --include ch22-elementary-graph \
  --warn_error -321 --warn_error @247 --ext optimize_let_vc --ext fly_deps \
  --cache_dir _cache ch22-elementary-graph/CLRS.Ch22.DFS.WhitePath.fst
```

---

### TASK D: RadixSort stability — 2 admits

**File:** `ch08-linear-sorting/CLRS.Ch08.RadixSort.MultiDigit.fst` (lines 394, 415)
**Currently assigned to:** Active WIP (uncommitted changes to Spec, Stability, FullSort).
**⚠️ Being worked on.**

**What to prove:**
1. `stable_sort_preserves_digit_order` (line 394): If input is sorted by digits 0..d-1 and we
   apply a stable sort on digit d, elements with equal digit d retain their relative order,
   hence remain sorted by digits 0..d-1.
2. `stable_sort_implies_sorted_up_to` (line 415): Consequence — after d passes, sorted by
   digits 0..d-1.

**Key insight:** These are the core RadixSort correctness lemmas. Proving them requires the
stability property of counting sort (which is proven in CountingSort.Stable, though its
correctness postconditions are also proven).

**Dependencies:** `CLRS.Ch08.RadixSort.Stability`, `CLRS.Ch08.CountingSort.Stable`
**Build command:**
```bash
fstar.exe --include $(realpath ../pulse)/out/lib/pulse --include common --include ch08-linear-sorting \
  --warn_error -321 --warn_error @247 --ext optimize_let_vc --ext fly_deps \
  --cache_dir _cache ch08-linear-sorting/CLRS.Ch08.RadixSort.MultiDigit.fst
```

---

### TASK E: Kruskal forest acyclicity — ~~1 assume val + 1 assume~~ PARTIALLY DONE

**Files:** `ch23-mst/CLRS.Ch23.Kruskal.fst` (line 81), `ch23-mst/CLRS.Ch23.Kruskal.SortedEdges.fst` (line 266)

**Status:** 1 of 2 obligations eliminated, 1 improved from FALSE `assume val` to TRUE `assume_`.

**What was done:**
1. **SortedEdges.fst** (ELIMINATED): Refactored to use `MST.Spec` edge type and `Kruskal.Spec`'s
   proven `kruskal_step` + `lemma_kruskal_step_preserves_forest`. The old `acyclic` definition
   was broken (didn't require `all_edges_distinct`, making it vacuously false). Now uses the
   correct MST.Spec definitions. `assume (acyclic result' n)` → fully proven. ✅
2. **Kruskal.fst** (IMPROVED): The `assume val lemma_kruskal_maintains_forest` was FALSE
   (`valid_endpoints + ec <= n-1` does NOT imply forest — counterexample: triangle in 4-vertex
   graph). Replaced with:
   - A proven `lemma_kruskal_maintains_forest` that takes `is_forest` as precondition
   - An `assume_` after the main loop that introduces `is_forest` (TRUE: follows from UF
     soundness + `acyclic_when_unreachable` from MST.Spec, but proving requires ~300 lines
     of UF component tracking invariant)
   - z3rlimit increased from 200 to 600 (fixes pre-existing compilation issue)

**Remaining work to fully prove Kruskal.fst `assume_`:**
- Strengthen `find` postcondition: `root` is the canonical representative of `v`'s component
- Define `uf_find_seq` (pure simulation of imperative `find`)
- Prove UF soundness: `find(u) ≠ find(v)` ⟹ `¬(reachable edges u v)`
- Apply `acyclic_when_unreachable` from MST.Spec
- Estimated: ~300 lines, high difficulty

---

### TASK F: UnionFind ranks_bounded after find — 1 assume

**File:** `ch21-disjoint-sets/CLRS.Ch21.UnionFind.Spec.fst` (line 126)

**What to prove:** `ranks_bounded` is preserved by the `find` operation (path compression).
Path compression only changes parent pointers, not ranks. So `ranks_bounded` (which only
depends on rank values) should be trivially preserved.

**Estimated size:** ~10-20 lines.
**Build command:**
```bash
fstar.exe --include $(realpath ../pulse)/out/lib/pulse --include common \
  --warn_error -321 --warn_error @247 --ext optimize_let_vc --ext fly_deps \
  --cache_dir _cache ch21-disjoint-sets/CLRS.Ch21.UnionFind.Spec.fst
```

---

### TASK G: MaxFlow MFMC axioms — 3 assumes

**Files:** `ch26-max-flow/CLRS.Ch26.MaxFlow.Spec.fst` (lines 354, 382), `ch26-max-flow/CLRS.Ch26.MaxFlow.Complexity.fst` (line 102)

**What to prove:**
1. Weak duality: `flow_value flow n source <= cut_capacity cap s_set` for any valid flow and cut
2. Min-cut existence: there exists a cut whose capacity equals the max flow value
3. Augmenting path existence: if flow is not maximum, there exists an augmenting path

**Assessment:** These are the Max-Flow Min-Cut Theorem components. The MaxFlow implementation
itself is a stub (returns zero flow), so these axioms are infrastructure for a future
implementation. **Low priority** — proving MFMC requires substantial graph theory infrastructure
(residual graphs, augmenting paths) that doesn't exist yet.

**Estimated difficulty:** HIGH (~500+ lines of new graph theory proofs)

---

## Agent Assignment Summary

| Task | Admits | Files Touched | Priority | Difficulty | Dependencies | Status |
|------|--------|---------------|----------|------------|--------------|--------|
| A: sp_dist_k_stabilize | ~~1~~ 0 | ch24/ShortestPath.Triangle.fst | HIGH | Medium (~150 lines) | FStar.Fin, ShortestPath.Spec | ✅ **Done** |
| B: Huffman forest | ~~2~~ 0 | ch16/Huffman.fst | HIGH | Medium (~50 lines) | Huffman.Spec | ✅ **Done** |
| C: DFS WhitePath backward | ~~3+err~~ 0 | ch22/DFS.WhitePath.fst | HIGH | Hard (~200 lines) | DFS.Spec | ✅ **Done** |
| D: RadixSort stability | ~~2~~ 0 | ch08/RadixSort.MultiDigit.fst | HIGH | Hard (~100 lines) | Stability, CountingSort.Stable | ✅ **Done** |
| E: Kruskal acyclicity | ~~2~~ 1 | ch23/Kruskal.fst, SortedEdges.fst | MEDIUM | Medium (~100 lines) | MST.Spec | ✅ **Partially done** (1 eliminated, 1 improved) |
| F: UnionFind ranks | ~~1~~ 0 | ch21/UnionFind.Spec.fst | LOW | Easy (~15 lines) | None | ✅ **Done** |
| G: MaxFlow MFMC | ~~3~~ 1 | ch26/MaxFlow.{Spec,Complexity}.fst | LOW | Hard | weak_duality proven, Complexity admit eliminated | ✅ **Mostly done** (1 deep theorem remains) |

### Independence Matrix

All tasks complete except residual hard assumptions in E and G.

---

## Zero-Admit Chapters (21 of 23)

These chapters have **zero unproven obligations** across all their files:

| Chapter | Files | Lines | Notes |
|---------|-------|-------|-------|
| ch02 Getting Started | 4 | 1,276 | InsertionSort, MergeSort — sorted ∧ perm |
| ch04 Divide & Conquer | 9 | 1,921 | BinarySearch, MaxSubarray — full specs |
| ch06 Heapsort | 3 | 1,230 | sorted ∧ perm, complexity separate |
| ch07 Quicksort | 6 | 2,065 | Partition + QSort, linked O(n²) |
| ch08 Linear Sorting | 12 | ~4,000 | RadixSort, CountingSort — fully proven ✅ |
| ch09 Order Statistics | 12 | 2,650 | MinMax, Quickselect — full specs |
| ch10 Elementary DS | 16 | 3,720 | Stack, Queue, SLL, DLL — zero admits |
| ch11 Hash Tables | 4 | 787 | Open addressing, linked O(n) |
| ch12 BST | 8 | 3,403 | Search/Insert/Delete — zero admits |
| ch13 Red-Black Trees | 3 | 1,432 | Pointer-based, Okasaki balance |
| ch15 Dynamic Programming | 12 | 3,239 | LCS, RodCutting, MatrixChain — all proven |
| ch16 Greedy | ~5 | ~2,000 | Huffman — fully proven ✅ |
| ch21 Disjoint Sets | 6 | ~1,500 | UnionFind — fully proven ✅ |
| ch22 Elementary Graph | ~12 | ~6,000 | DFS, BFS, WhitePath — fully proven ✅ |
| ch24 Single-Source SP | 11 | ~3,500 | Dijkstra, Bellman-Ford — fully proven ✅ |
| ch25 All-Pairs SP | 4 | 856 | Floyd-Warshall — exact spec, linked O(n³) |
| ch28 Matrix Ops | 3 | 1,401 | MatMul + Strassen — zero admits |
| ch31 Number Theory | 5 | 871 | GCD, ExtGCD, ModExp — Bézout, Lamé |
| ch32 String Matching | 12 | 3,690 | Naive, KMP, RabinKarp — zero admits |
| ch33 Comp Geometry | 2 | 228 | Segments — full specs |
| ch35 Approximation | 3 | 850 | VertexCover — zero admits |

Chapters with remaining obligations:
- ch23 MST (1 `assume_` in Kruskal.fst — UF soundness, all other files clean)
- ch26 MaxFlow (1 `assume` in MaxFlow.Spec.fst — MFMC theorem, all other files clean)

---

## Build Verification Status

| File | Compiles? | Admits | Notes |
|------|-----------|--------|-------|
| ch08/RadixSort.MultiDigit.fst | ✅ | 0 | Uncommitted changes, fully proven |
| ch16/Huffman.fst | ✅ | 0 | Uncommitted changes, fully proven |
| ch22/DFS.WhitePath.fst | ✅ | 0 | Uncommitted changes, fully proven |
| ch23/Kruskal.fst | ✅ | 1 assume_ | Committed |
| ch23/Kruskal.SortedEdges.fst | ✅ | 0 | Committed, fully proven |
| ch24/ShortestPath.Triangle.fst | ✅ | 0 | Committed, fully proven |
| ch26/MaxFlow.Spec.fst | ✅ | 1 assume | MFMC theorem |
| ch26/MaxFlow.Complexity.fst | ✅ | 0 | Uncommitted changes, fully proven |

---

## Remaining Work

Only 2 unproven obligations remain. Both are deep mathematical theorems:

1. **Kruskal UF soundness** (`ch23/Kruskal.fst:313`): Prove that union-find-based cycle
   detection correctly identifies connected components. Requires ~300 lines:
   - Strengthen `find` postcondition to track component representatives
   - Define pure UF simulation (`uf_find_seq`)
   - Prove `find(u) ≠ find(v) ⟹ ¬(reachable edges u v)`
   - Apply `acyclic_when_unreachable` from MST.Spec

2. **Max-Flow Min-Cut theorem** (`ch26/MaxFlow.Spec.fst:633`): Prove that when no
   augmenting path exists, the flow value equals some cut capacity. Requires ~500 lines:
   - Define reachability in residual graph
   - Construct the min-cut S = {v : reachable from source in G_f}
   - Prove flow saturates all edges crossing (S, T)
   - Prove c(S,T) = |f|
