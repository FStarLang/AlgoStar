# AutoCLRS Progress Audit — 2025-02-25

**Scope**: Full audit of every unproven obligation, broken file, and remaining task.
Decomposition into independent agent tasks for parallel execution.

**Codebase stats**:
- 182 F*/Pulse files, ~73,800 lines across 23 chapters + common
- **12 total unproven obligations** (was 14; Task F eliminated 1, Task E eliminated 1 + improved 1) (8 `admit()`, 4 `assume()`, 1 `assume_`)
  across 7 files in 6 chapters
- 1 file broken (doesn't compile): `DFS.WhitePath.fst`
- 5 files have uncommitted changes (3 RadixSort, 1 Huffman, 1 WhitePath)

**Change since AUDIT_0223 (2025-02-23): 97 → 14 unproven obligations (−83, 86% reduction)**

---

## Complete Unproven Obligations Inventory

| # | File | Type | Line | Description |
|---|------|------|------|-------------|
| 1 | `ch08/RadixSort.MultiDigit.fst` | `admit()` | 394 | `stable_sort_preserves_digit_order`: stability of counting sort preserves prior digit ordering |
| 2 | `ch08/RadixSort.MultiDigit.fst` | `admit()` | 415 | `stable_sort_implies_sorted_up_to`: consequence of stability preservation |
| 3 | `ch16/Huffman.fst` | `admit()` | 872 | PQ loop: prove `find_entry_by_idx remaining1 idx2 = Some _` (second tree exists in forest after removing first) |
| 4 | `ch16/Huffman.fst` | `admit()` | 901 | Post-loop: prove `forest_own []` is emp after extracting single remaining tree |
| 5 | `ch21/UnionFind.Spec.fst` | `assume()` | 126 | `ranks_bounded` after path compression in `find` |
| 6 | `ch22/DFS.WhitePath.fst` | `admit()` | 671 | White-path backward: timestamp containment for visited vertex in DFS subtree |
| 7 | `ch22/DFS.WhitePath.fst` | `admit()` | 781 | White-path backward: `d_top[u_start]` ordering when u_start is DFS root |
| 8 | `ch22/DFS.WhitePath.fst` | `admit()` | 793 | White-path backward: relative discovery time ordering within DFS subtree |
| 9 | `ch23/Kruskal.fst` | `assume_` | 313 | Forest acyclicity via UF soundness (TRUE but unproven; was FALSE `assume val` at line 81) |
| ~~10~~ | ~~`ch23/Kruskal.SortedEdges.fst`~~ | ~~`assume()`~~ | ~~266~~ | ~~ELIMINATED: refactored to use Kruskal.Spec's proven `kruskal_step`~~ |
| 11 | `ch24/ShortestPath.Triangle.fst` | `admit()` | 141 | `sp_dist_k_stabilize`: `sp_dist_k(s,v,n) == sp_dist_k(s,v,n-1)` (pigeonhole + cycle removal) |
| 12 | `ch26/MaxFlow.Spec.fst` | `assume()` | 354 | Weak duality: flow value ≤ cut capacity |
| 13 | `ch26/MaxFlow.Spec.fst` | `assume()` | 382 | Min-cut existence for max flow |
| 14 | `ch26/MaxFlow.Complexity.fst` | `assume()` | 102 | Augmenting path existence when flow is not maximum |

### Broken Files

| File | Error | Cause |
|------|-------|-------|
| `ch22/DFS.WhitePath.fst` | `Error 72: Identifier not found: get_white_neighbors_edges` (line 573) | Uncommitted WIP — references undefined function |

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

---

## Remaining Agent Tasks

AGENTS MUST ALL WORK ON THE SAME BRANCH BUT WORK ON DISJOINT FILES.

Each agent MUST work on different files with no overlap, so they can run
simultaneously without conflicts (except for this file).

Agent must commit only the files they work on, repeatedly as they reach
meaningful checkpoints.

When an agent finishes, they should update this file with their
results and learnings, using `flock` to avoid conflicts.


### TASK A: sp_dist_k_stabilize (Dijkstra dependency) — 1 admit

**File:** `ch24-sssp/CLRS.Ch24.ShortestPath.Triangle.fst` (line 141)
**Currently assigned to:** Was AGENT9 scope, not yet done.

**What to prove:** `sp_dist_k(s,v,n) == sp_dist_k(s,v,n-1)` for non-negative weights.

**Strategy:**
- Already have `<=` direction (monotonicity, proven)
- Need `>=` direction: any path with n edges has n+1 vertices in a graph with n vertices
- By `FStar.Fin.pigeonhole`: a sequence of n+1 values in `[0,n)` has two equal indices
- This means the path has a cycle; for non-negative weights, removing it gives a shorter-or-equal
  path with fewer edges
- Therefore `sp_dist_k(s,v,n-1) <= sp_dist_k(s,v,n)`

**Proof outline (~150-200 lines):**
1. Define path as `Seq.seq (under n)` of length ≥ 2 with valid edges
2. `path_has_cycle`: path with > n edges has a repeated vertex (via `FStar.Fin.pigeonhole`)
3. `remove_cycle`: given repeated vertex at indices i < j, take `path[0..i] @ path[j..]`;
   weight decreases for non-negative weights
4. `contract_path`: repeatedly remove cycles until path has ≤ n-1 edges
5. Connect to `sp_dist_k`: `sp_dist_k` is minimum over all paths with ≤ k edges;
   path contraction shows any n-edge path has a ≤ (n-1)-edge path with ≤ weight

**Dependencies:** `FStar.Fin` (pigeonhole), `CLRS.Ch24.ShortestPath.Spec` (sp_dist_k definition)
**Build command:**
```bash
fstar.exe --include $(realpath ../pulse)/out/lib/pulse --include common --include ch24-sssp \
  --warn_error -321 --warn_error @247 --ext optimize_let_vc --ext fly_deps \
  --cache_dir _cache ch24-sssp/CLRS.Ch24.ShortestPath.Triangle.fst
```

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
| A: sp_dist_k_stabilize | 1 | ch24/ShortestPath.Triangle.fst | HIGH | Medium (~150 lines) | FStar.Fin, ShortestPath.Spec | **Available** |
| B: Huffman forest | 2 | ch16/Huffman.fst | HIGH | Medium (~50 lines) | Huffman.Spec | **⚠️ Being worked on** |
| C: DFS WhitePath backward | 3+err | ch22/DFS.WhitePath.fst | HIGH | Hard (~200 lines) | DFS.Spec | **⚠️ Being worked on** |
| D: RadixSort stability | 2 | ch08/RadixSort.MultiDigit.fst | HIGH | Hard (~100 lines) | Stability, CountingSort.Stable | **⚠️ Being worked on** |
| E: Kruskal acyclicity | ~~2~~ 1 | ch23/Kruskal.fst, SortedEdges.fst | MEDIUM | Medium (~100 lines) | MST.Spec | ✅ **Partially done** (1 eliminated, 1 improved) |
| F: UnionFind ranks | ~~1~~ 0 | ch21/UnionFind.Spec.fst | LOW | Easy (~15 lines) | None | ✅ **Done** |
| G: MaxFlow MFMC | 3→1a+1 | ch26/MaxFlow.{Spec,Complexity}.fst | LOW | Mostly done | weak_duality proven | **Done** |

### Independence Matrix

All tasks touch disjoint files and are fully independent of each other.

- Tasks B, C, D have active uncommitted changes — new agents should start from those working copies.
- Tasks A, E, F, G can start from HEAD.

---

## Zero-Admit Chapters (18 of 23)

These chapters have **zero unproven obligations** across all their files:

| Chapter | Files | Lines | Notes |
|---------|-------|-------|-------|
| ch02 Getting Started | 4 | 1,276 | InsertionSort, MergeSort — sorted ∧ perm |
| ch04 Divide & Conquer | 9 | 1,921 | BinarySearch, MaxSubarray — full specs |
| ch06 Heapsort | 3 | 1,230 | sorted ∧ perm, complexity separate |
| ch07 Quicksort | 6 | 2,065 | Partition + QSort, linked O(n²) |
| ch09 Order Statistics | 12 | 2,650 | MinMax, Quickselect — full specs |
| ch10 Elementary DS | 16 | 3,720 | Stack, Queue, SLL, DLL — zero admits |
| ch11 Hash Tables | 4 | 787 | Open addressing, linked O(n) |
| ch12 BST | 8 | 3,403 | Search/Insert/Delete — zero admits |
| ch13 Red-Black Trees | 3 | 1,432 | Pointer-based, Okasaki balance |
| ch15 Dynamic Programming | 12 | 3,239 | LCS, RodCutting, MatrixChain — all proven |
| ch25 All-Pairs SP | 4 | 856 | Floyd-Warshall — exact spec, linked O(n³) |
| ch28 Matrix Ops | 3 | 1,401 | MatMul + Strassen — zero admits |
| ch31 Number Theory | 5 | 871 | GCD, ExtGCD, ModExp — Bézout, Lamé |
| ch32 String Matching | 12 | 3,690 | Naive, KMP, RabinKarp — zero admits |
| ch33 Comp Geometry | 2 | 228 | Segments — full specs |
| ch35 Approximation | 3 | 850 | VertexCover — zero admits |

**Total zero-admit: 106 files, ~29,619 lines**

Plus chapters with very few remaining obligations:
- ch08 (2 admits in MultiDigit only, 10 other files clean)
- ch21 (1 assume in Spec only, 5 other files clean)
- ch24 (1 admit in Triangle only, 10 other files clean)

---

## Build Verification Status

| File | Compiles? | Admits | Notes |
|------|-----------|--------|-------|
| ch08/RadixSort.MultiDigit.fst | ✅ | 2 | Uncommitted changes, verifies |
| ch08/RadixSort.FullSort.fst | ✅ | 0 | Uncommitted changes, verifies |
| ch08/RadixSort.Stability.fst | ✅ | 0 | Uncommitted changes, verifies |
| ch08/RadixSort.Spec.fst | ✅ | 0 | Uncommitted changes, verifies |
| ch16/Huffman.fst | ✅ | 2 | Uncommitted changes, verifies |
| ch22/DFS.WhitePath.fst | ❌ | 3 | Error 72: `get_white_neighbors_edges` not found |
| ch24/ShortestPath.Triangle.fst | ✅ | 1 | Committed, verifies |

---

## Recommended Priorities

### Highest Impact (eliminate admits in verified, compilable code)
1. **TASK A** (sp_dist_k_stabilize) — Completes Dijkstra equality proof chain. 1 admit, medium difficulty, uses FStar.Fin.pigeonhole which is available. **Best ROI.**
2. **TASK F** (UnionFind ranks) — Trivial: path compression doesn't change ranks. ~15 lines.

### Medium Impact (complete ongoing work)
3. **TASK B** (Huffman) — 2 admits in Pulse forest management. Already close.
4. **TASK D** (RadixSort) — 2 admits in stability. Core CLRS correctness.
5. **TASK E** (Kruskal) — ~~2 obligations~~ 1 remaining `assume_` (TRUE). UF soundness proof needed.

### Lower Priority
6. **TASK C** (DFS WhitePath) — Currently broken. Hard proof (backward white-path theorem).
7. **TASK G** (MaxFlow) — Implementation is a stub. Proving MFMC axioms without real algorithm is academic exercise.
