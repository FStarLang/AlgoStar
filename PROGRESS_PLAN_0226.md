# PROGRESS PLAN — Feb 26, 2026

## Current Status

**184 F\* source files**, **75,730 lines**.
**2 unproven obligations** remaining (down from 97 at first audit, 14 at Feb 25 audit):

| # | File | Type | Line | Description |
|---|------|------|------|-------------|
| 1 | `ch23-mst/CLRS.Ch23.Kruskal.fst` | `assume_()` | 313 | Forest property: UF-based cycle detection ensures acyclicity. Needs formal UF component tracking. |
| 2 | `ch26-max-flow/CLRS.Ch26.MaxFlow.Spec.fst` | `assume()` | 600 | Max-flow min-cut theorem (CLRS Thm 26.6): when no augmenting path, reachable set defines min cut. |

Everything else — all 182 other files — is fully verified with zero admits, assumes, or assume vals.

---

## Structural Issues

### ISSUE 1: Duplicated Algorithms (Correctness vs Complexity)

The project has **27 Pulse algorithms where correctness and complexity are in separate files**, duplicating the algorithm code. The user's directive: **merge correctness and complexity into a single file** per algorithm.

Each pair below has a `.fst` (correctness only) and a `.Complexity.fst` (re-implements the same algorithm with ghost tick counters). The goal is to merge them into a single file that proves *both* correctness and complexity.

| Ch | Correctness File | Complexity File | Lines (C+X) | Difficulty |
|----|-----------------|-----------------|-------------|-----------|
| 02 | InsertionSort.fst | InsertionSort.Complexity.fst | 218+230 | Easy |
| 04 | BinarySearch.fst | BinarySearch.Complexity.fst | 145+186 | Easy |
| 04 | MaxSubarray.Kadane.fst | MaxSubarray.Kadane.Complexity.fst | 230+142 | Easy |
| 07 | Partition.fst | Partition.Complexity.fst | 240+272 | Easy |
| 07 | Quicksort.fst | Quicksort.Complexity.Enhanced.fst | 589+583 | Medium |
| 09 | MinMax.fst | MinMax.Complexity.fst | 135+162 | Easy |
| 11 | HashTable.fst | HashTable.Complexity.fst | ~300+284 | Medium |
| 15 | LCS.fst | LCS.Complexity.fst | 298+253 | Medium |
| 15 | RodCutting.fst | RodCutting.Complexity.fst | 243+256 | Medium |
| 16 | ActivitySelection.fst | ActivitySelection.Complexity.fst | 182+146 | Easy |
| 22 | QueueBFS.fst | QueueBFS.Complexity.fst | 560+455 | Hard |
| 22 | StackDFS.fst | StackDFS.Complexity.fst | 876+873 | Hard |
| 22 | KahnTopologicalSort.fst | KahnTopologicalSort.Complexity.fst | 670+387 | Hard |
| 23 | Kruskal.fst | Kruskal.Complexity.fst | 325+521 | Hard |
| 23 | Prim.fst | Prim.Complexity.fst | 353+433 | Hard |
| 24 | Dijkstra.fst | Dijkstra.Complexity.fst | ~200+372 | Hard |
| 24 | BellmanFord.fst | BellmanFord.Complexity.Instrumented.fst | 180+418 | Hard |
| 25 | FloydWarshall.fst | FloydWarshall.Complexity.fst | ~200+221 | Medium |
| 28 | MatrixMultiply.fst | MatrixMultiply.Complexity.fst | 199+227 | Medium |
| 31 | GCD.fst | GCD.Complexity.fst | 88+216 | Easy |
| 31 | ModExp.fst | ModExp.Complexity.fst | 182+213 | Easy |
| 32 | KMP.fst | KMP.Complexity.fst | 445+515 | Hard |
| 32 | NaiveStringMatch.fst | NaiveStringMatch.Complexity.fst | 206+221 | Medium |
| 33 | Segments.fst | Segments.Complexity.fst | 163+65 | Easy |
| 35 | VertexCover.fst | VertexCover.Complexity.fst | 356+44 | Easy |

**Not duplicated** (pure standalone complexity — keep separate):
- `ch02/MergeSort.Complexity.fst` (pure recurrence, no Pulse)
- `ch06/Heap.Complexity.fst` (pure bounds, no Pulse)
- `ch07/Quicksort.Complexity.fst` (pure recurrence, 96 lines)
- `ch08/CountingSort.Complexity.fst` (pure, 32 lines)
- `ch08/RadixSort.Complexity.fst` (pure, 146 lines)
- `ch09/PartialSelectionSort.Complexity.fst` (pure, 135 lines)
- `ch09/Quickselect.Complexity.fst` (pure, 48 lines)
- `ch10/DataStructures.Complexity.fst` (pure, 96 lines)
- `ch12/BST.Complexity.fst` (pure bounds)
- `ch12/BST.Spec.Complexity.fst` (pure tick counting on inductive tree)
- `ch13/RBTree.Complexity.fst` (pure tick counting)
- `ch15/MatrixChain.Complexity.fst` (pure, 106 lines)
- `ch16/Huffman.Complexity.fst` (pure, 225 lines)
- `ch22/Graph.Complexity.fst` (pure, 69 lines)
- `ch23/MST.Complexity.fst` (pure, 102 lines)
- `ch24/BellmanFord.Complexity.fst` (pure, 101 lines)
- `ch32/RabinKarp.Complexity.fst` (pure, 113 lines)

**Also keep**: `.Enhanced.fst` files that extend pure complexity analysis (ch06, ch07, ch09, ch10) — these are standalone pure analyses, not duplicated Pulse.

### ISSUE 2: Duplicated Spec Definitions

**`has_edge`** — defined in **12 files** across ch22, ch23, ch35:
- ch22: BFS.Spec, BFS.DistanceSpec, DFS.Spec, QueueBFS, QueueBFS.Complexity, StackDFS, StackDFS.Complexity, IterativeBFS, IterativeDFS, TopologicalSort.Spec
- ch23: Prim.Spec
- ch35: VertexCover.fst

Should be defined **once** in a shared graph module (e.g., `CLRS.Common.Graph`).

**`sorted`** — defined in **17 files** (ch06, ch07, ch08, ch09, ch12, ch16, ch23, common):
- `CLRS.Common.SortSpec.fst` already has it, but most files define their own version.

**`permutation`** — defined in **15 files** (ch06–ch09, ch23, common):
- `CLRS.Common.SortSpec.fst` already has it, but most files redefine.

**`kadane_spec` / `max_sub_sum`** — defined in **3 files** (Kadane.fst, Kadane.Complexity.fst, DivideConquer.fst):
- Should be in a single shared `MaxSubarray.Spec.fst`.

### ISSUE 3: Experimental/Proof-Pattern Files in Chapter Dirs

Per notes.md, these should be moved to a `proof_patterns/` folder:
- `ch04-divide-conquer/CLRS.Ch04.BinarySearch.Corrected.fst` (293 lines)
- `ch04-divide-conquer/CLRS.Ch04.BinarySearch.Pattern.fst` (332 lines)

### ISSUE 4: Redundant Complexity Files in Ch06

Per notes.md, `Heap.Complexity.fst` (101 lines) and `Heap.Complexity.Enhanced.fst` (446 lines) are both pure standalone analyses not tied to the Pulse heapsort code. They should be consolidated into one file. They also share duplicated `log2_floor` definitions.

### ISSUE 5: Weak Specs

**BucketSort** (`ch08/BucketSort.fst`): postcondition is `sorted ys /\ List.length ys == List.length xs` — proves sorted + length but **not permutation**. Should prove `permutation xs ys`.

**MaxFlow** (`ch26/MaxFlow.fst`): Pulse implementation only initializes zero flow. The full Ford-Fulkerson loop (BFS, augment, repeat) is specified in pure F* but not implemented in Pulse.

### ISSUE 6: Missing CLRS Algorithms

Not a cleanup issue, but noted for completeness:
- No Ch14 (augmented data structures — interval trees)
- No Ch17 (amortized analysis — dynamic tables)
- No Ch19–20 (Fibonacci heaps, van Emde Boas)
- No Ch29 (linear programming)
- No Ch34 (NP-completeness — decision/search problems)

---

## Task Decomposition

All tasks below are independent and can be executed by separate agents in parallel.

AGENTS MUST ALL WORK ON THE SAME BRANCH BUT WORK ON DISJOINT FILES.

Each agent MUST work on different files with no overlap, so they can run
simultaneously without conflicts (except for this file).

Agent must commit only the files they work on, repeatedly as they reach
meaningful checkpoints.

When an agent finishes, they should update this file with their
results and learnings, using `flock` to avoid conflicts.

### TASK A: Merge Correctness + Complexity — ch02, ch04

**Files to merge (4 pairs):**
1. `InsertionSort.fst` ← `InsertionSort.Complexity.fst`
2. `BinarySearch.fst` ← `BinarySearch.Complexity.fst`
3. `Kadane.fst` ← `Kadane.Complexity.fst`
4. Move `BinarySearch.Corrected.fst` and `BinarySearch.Pattern.fst` to `proof_patterns/`

**Spec dedup:**
- Extract `kadane_spec` and `max_sub_sum` from `Kadane.fst`, `Kadane.Complexity.fst`, and `DivideConquer.fst` into a shared `MaxSubarray.Spec.fst`. All three files import from it.

**Difficulty:** Easy. 4 simple merges + 1 spec extraction + 2 file moves.

### TASK B: Merge Correctness + Complexity — ch06, ch07

**Files to merge (2 pairs):**
1. `Partition.fst` ← `Partition.Complexity.fst`
2. `Quicksort.fst` ← `Quicksort.Complexity.Enhanced.fst`

**Consolidation:**
- Merge `Heap.Complexity.fst` + `Heap.Complexity.Enhanced.fst` into one file. Remove duplicated `log2_floor` definitions.

**Difficulty:** Medium. Quicksort merge involves threading tick counter through recursion.

### TASK C: Merge Correctness + Complexity — ch09, ch10, ch11

**Files to merge (2 pairs):**
1. `MinMax.fst` ← `MinMax.Complexity.fst`
2. `HashTable.fst` ← `HashTable.Complexity.fst`

**Note:** `DLL.Complexity.fst` / `DLL.Complexity.Enhanced.fst` are already tied to the Pulse DLL code (ticks added to existing operations). Review whether they truly need separate files or can be merged into `DLL.fst`.

**Difficulty:** Easy–Medium.

### TASK D: Merge Correctness + Complexity — ch15, ch16

**Files to merge (3 pairs):**
1. `LCS.fst` ← `LCS.Complexity.fst`
2. `RodCutting.fst` ← `RodCutting.Complexity.fst`
3. `ActivitySelection.fst` ← `ActivitySelection.Complexity.fst`

**Difficulty:** Medium. DP loops need ghost counters threaded through nested iterations.

### TASK E: Merge Correctness + Complexity — ch22

**Files to merge (3 pairs):**
1. `QueueBFS.fst` ← `QueueBFS.Complexity.fst`
2. `StackDFS.fst` ← `StackDFS.Complexity.fst`
3. `KahnTopologicalSort.fst` ← `KahnTopologicalSort.Complexity.fst`

**Spec dedup:**
- Extract `has_edge` (and possibly `reachable`, color constants) from 10+ files into `CLRS.Ch22.Graph.Common.fst`. All ch22 files import from it.

**Difficulty:** Hard. These are large files (500–900 lines each). The complexity files already import predicates from the correctness files, so merging requires careful invariant integration.

### TASK F: Merge Correctness + Complexity — ch23, ch24, ch25

**Files to merge (5 pairs):**
1. `Kruskal.fst` ← `Kruskal.Complexity.fst`
2. `Prim.fst` ← `Prim.Complexity.fst`
3. `Dijkstra.fst` ← `Dijkstra.Complexity.fst`
4. `BellmanFord.fst` ← `BellmanFord.Complexity.Instrumented.fst`
5. `FloydWarshall.fst` ← `FloydWarshall.Complexity.fst`

**Spec dedup:**
- `has_edge` defined in `Prim.Spec.fst` should import from `CLRS.Ch22.Graph.Common.fst` (task E creates this).

**Difficulty:** Hard. Graph algorithms have complex invariants. Kruskal still has 1 assume_.

### TASK G: Merge Correctness + Complexity — ch28, ch31, ch32, ch33, ch35

**Files to merge (7 pairs):**
1. `MatrixMultiply.fst` ← `MatrixMultiply.Complexity.fst`
2. `GCD.fst` ← `GCD.Complexity.fst`
3. `ModExp.fst` ← `ModExp.Complexity.fst`
4. `KMP.fst` ← `KMP.Complexity.fst`
5. `NaiveStringMatch.fst` ← `NaiveStringMatch.Complexity.fst`
6. `Segments.fst` ← `Segments.Complexity.fst`
7. `VertexCover.fst` ← `VertexCover.Complexity.fst`

**Spec dedup:**
- `has_edge` in `VertexCover.fst` should import from shared graph module.

**Difficulty:** Easy–Hard (varies). GCD/ModExp/Segments are easy; KMP is hard.

### TASK H: Fix BucketSort Spec

**File:** `ch08-linear-sorting/CLRS.Ch08.BucketSort.fst`

**Current postcondition:** `sorted ys /\ List.length ys == List.length xs`
**Target postcondition:** `sorted ys /\ permutation xs ys`

This requires proving that `filter_bucket` + `sort_all_buckets` + `concat_all` preserves multiset membership. The building blocks (insertion sort per bucket) already prove permutation, so this is a matter of threading the property through the bucket distribution and concatenation steps.

**Difficulty:** Medium. ~200 lines of additional proof.

### TASK I: Prove Kruskal Forest Property

**File:** `ch23-mst/CLRS.Ch23.Kruskal.fst`, line 313

**Current:** `assume_ (pure (... KSpec.is_forest ...))`
**Goal:** Prove that UF-based cycle detection ensures the selected edges form an acyclic forest.

This requires establishing a formal UF component tracking invariant: at each step, `root_u <> root_v` implies `u` and `v` are in different connected components, so adding edge `(u,v)` cannot create a cycle.

**Difficulty:** Hard. Requires connecting union-find invariants (from ch21) to graph acyclicity (from ch23 MST.Spec). ~300–500 lines.

### TASK J: Prove Max-Flow Min-Cut Theorem

**File:** `ch26-max-flow/CLRS.Ch26.MaxFlow.Spec.fst`, line 600

**Current:** `assume (exists (s_set: ...) ...)`
**Goal:** When no augmenting path exists in the residual graph, define S = {v reachable from source in G_f} and show this cut has capacity equal to |f|.

This requires:
1. Define reachability in the residual graph
2. Show that for unreachable v, residual_capacity(s→v) = 0 for all s ∈ S
3. Conclude net flow across the cut equals cut capacity

**Difficulty:** Hard. ~300–500 lines of graph-theoretic reasoning.

---

## Merge Strategy (for Tasks A–G)

For each pair `Algo.fst` + `Algo.Complexity.fst`:

1. **Start from the Complexity file** (it already has ghost counters).
2. **Add missing correctness postconditions** from the original file.
3. **Remove the original file** (the merged file replaces both).
4. **Update all imports** (`open` / `module` declarations) in dependent files.
5. **Verify** the merged file builds cleanly.

Key principle: the merged file should have a single Pulse function with postcondition proving *both* `correctness_spec` *and* `complexity_bounded`.

For spec deduplication:
1. **Create shared module** (e.g., `CLRS.Common.Graph.fst` or `MaxSubarray.Spec.fst`).
2. **Move canonical definitions** to shared module.
3. **Replace local definitions** with `open` + import.
4. **Verify** all dependent files still build.

---

## Summary Table

| Task | Scope | Pairs | Difficulty | Dependencies |
|------|-------|-------|-----------|-------------|
| A | ch02, ch04 | 3 merge + 1 spec + 2 move | Easy | None |
| B | ch06, ch07 | 2 merge + 1 consolidate | Medium | None |
| C | ch09, ch10, ch11 | 2–3 merge | Easy–Medium | None |
| D | ch15, ch16 | 3 merge | Medium | None |
| E | ch22 | 3 merge + spec dedup | Hard | None |
| F | ch23, ch24, ch25 | 5 merge + spec dedup | Hard | E (for has_edge) |
| G | ch28, ch31, ch32, ch33, ch35 | 7 merge + spec dedup | Easy–Hard | E (for has_edge) |
| H | ch08 BucketSort | Fix weak spec | Medium | None |
| I | ch23 Kruskal | Prove 1 assume_ | Hard | None |
| J | ch26 MaxFlow | Prove 1 assume | Hard | None |

**Critical path**: E → F, G (shared graph module). All others independent.

**Priority order**:
1. **H** (BucketSort spec fix) — quick win, improves fidelity
2. **I, J** (last 2 unproven obligations) — reach zero admits
3. **A** (ch02/ch04 merge) — easiest merge, establishes pattern
4. **E** (ch22 spec dedup + merge) — unblocks F, G
5. **B, C, D, F, G** — remaining merges in any order

---

## Task C Results (Agent)

**Status: COMPLETE**

### Merges completed:
1. **MinMax** (ch09): `CLRS.Ch09.MinMax.fst` now proves both correctness (min/max value exists and is universally bounded) and complexity (exactly n-1 comparisons, Θ(n)). Deleted `CLRS.Ch09.MinMax.Complexity.fst`.

2. **HashTable** (ch11): `CLRS.Ch11.HashTable.fst` now proves both correctness (`key_in_table` on insert, found index contains key on search) and complexity (at most n probes, O(n)). Deleted `CLRS.Ch11.HashTable.Complexity.fst`.

### Other updates:
- Updated `CLRS.Ch11.HashTable.Test.fst` to use ghost tick counter
- Updated `doc/ch11_hash_tables.rst` snippet references to point to merged file

### ch10 DLL Review:
- `DoublyLinkedList.Complexity.fst` and `DoublyLinkedList.Complexity.Enhanced.fst` define their own `node` type (no `prev` pointer) and `is_dlist` predicate — structurally different from `DLL.fst` (which uses `prev` pointer + `dls` segment predicate). These are standalone implementations, NOT duplicates. **Keep separate.**
- `DataStructures.Complexity.fst` is pure standalone — already in the keep-separate list.

### Verification: All files verified with zero admits.
