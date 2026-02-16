# AutoCLRS: Verified CLRS Algorithms in Pulse/F*

## Quick Reference

### Build & Verify

```bash
cd /home/nswamy/workspace/everest/AutoCLRS

# Full build (all chapters, parallel)
make -j128

# Verify a single file
fstar.exe --include $(realpath ../pulse)/out/lib/pulse --include common <file.fst>

# Files needing chapter-level includes:
#   --include ch08-linear-sorting    (RadixSort, CountingSort.Stable, BucketSort)
#   --include ch09-order-statistics  (Select.Correctness, etc.)
#   --include ch12-bst               (BST.Insert.Spec, BST.Delete.Spec)
#   --include ch16-greedy            (Huffman.Complete)
#   --include ch22-elementary-graph  (DFS.WhitePath, DFS.Spec, TopologicalSort)
#   --include ch23-mst               (Kruskal.Spec, Prim.Spec, etc.)
#   --include ch24-sssp              (Dijkstra.TriangleInequality, BellmanFord.Spec)
#   --include ch32-string-matching   (KMP.StrengthenedSpec, RabinKarp.Spec)

# Debugging verification failures
fstar.exe --query_stats --split_queries always --z3refresh <file.fst>
```

### Conventions

- **Functional correctness**: Imperative code proven equivalent to a pure, total, recursive spec.
  E.g., postcondition `result == sort_spec input` or `sorted s ∧ permutation s0 s`.
- **Complexity proofs**: Ghost tick counter `ctr: GR.ref nat` threaded through Pulse code.
  Postcondition asserts `GR.pts_to ctr (c0 + bound)` where `bound` is a formula on input size.
  "**Linked**" = ghost ticks in Pulse code. "**Separate**" = pure F* analysis only, not connected.
- **Graphs**: Adjacency matrix as flat `array int` of size `n*n`, `1000000` as infinity.
- **Trees**: Array-backed with `left[i]`, `right[i]`, `color[i]`, `key[i]` arrays; `-1` as null.
- **DLL**: True doubly-linked via DLS segment predicate (separation logic, box-allocated nodes).

### Proof Techniques That Work

- **FiniteSet algebra** (BST): `FStar.FiniteSet.Base` with `FS.all_finite_set_facts_lemma()`.
  Discharges set equality for tree insert/delete key-set proofs.
- **Queue/stack validity invariants** (Graph algos): `forall i. i in range ==> element < n`.
- **strong_valid_state pattern** (DFS): Bidirectional color↔timestamp invariant.
- **Ghost tick via GhostReference**: `tick ctr` increments counter; postcondition bounds it.

### Pitfalls to Avoid

- Agents replacing `admit()` with `assume val` don't reduce the real admit count.
- z3rlimit > 100 causes timeouts. Keep ≤ 50.
- `--admit_smt_queries true` hides real failures — never use.
- Removing `rec` can break SMT encoding (3 known cases in Select.Spec).
- Strengthening preconditions cascades to all callers — requires full invariant propagation.

---

## Current Status (2025-02-15, updated)

**167 F* files, ~50K lines, 145 admits across 34 files**

### Per-Algorithm Status Table

| Ch | Algorithm | CLRS § | Func. Spec | Complexity | Admits | Notes |
|----|-----------|--------|------------|------------|--------|-------|
| 02 | Insertion Sort | §2.1 | ✅ sorted ∧ perm | ✅ Linked O(n²) | 0 | |
| 02 | Merge Sort | §2.3 | ✅ sorted ∧ perm | ⚠️ Separate O(n lg n) | 0 | |
| 04 | Binary Search | §2.3 | ✅ found⟹match, ¬found⟹∉ | ✅ Linked O(lg n) | 0 | |
| 04 | MaxSubarray.Kadane | — | ✅ result=spec | ✅ Linked O(n) | 0 | ✅ Renamed (not CLRS) |
| 04 | MaxSubarray D&C | §4.1 | ⚠️ 1 axiom | ⚠️ Separate O(n lg n) | 1 | Pure F* only |
| 06 | Heapsort | §6.4 | ✅ sorted ∧ perm | ⚠️ Separate O(n lg n) | 0 | |
| 07 | Partition (Lomuto) | §7.1 | ✅ partitioned ∧ perm | ✅ Linked O(n) | 0 | |
| 07 | Quicksort | §7.1 | ✅ sorted ∧ perm | ⚠️ Separate O(n²) | 0 | |
| 08 | CountingSort | §8.2 | ✅ sorted ∧ perm | ⚠️ Separate O(n+k) | 0 | In-place (not CLRS 4-phase) |
| 08 | CountingSort.Stable | §8.2 | ⚠️ assumed postcond | ⚠️ Separate | 3 | CLRS 4-phase, stability unproven |
| 08 | RadixSort (d=1) | §8.3 | ✅ sorted ∧ perm | ⚠️ Separate Θ(d(n+k)) | 0 | d=1 only |
| 08 | RadixSort.MultiDigit | §8.3 | ⚠️ partial | — | 4 | Pure F* only |
| 08 | BucketSort | §8.4 | ⚠️ no perm proof | — | 1 | |
| 09 | MinMax | §9.1 | ✅ correct min/max | ✅ Linked O(n) | 0 | |
| 09 | PartialSelectionSort | — | ✅ perm ∧ prefix sorted | ⚠️ Separate O(nk) | 5 | ✅ Renamed (not CLRS) |
| 09 | Quickselect | §9.2 | ✅ perm ∧ result=s[k] | ⚠️ Separate O(n²) | 0 | |
| 10 | Stack | §10.1 | ✅ ghost list LIFO | ⚠️ Separate O(1) | 0 | |
| 10 | Queue | §10.1 | ✅ ghost list FIFO | ⚠️ Separate O(1) | 0 | |
| 10 | DLL | §10.2 | ✅ DLS segment pred | ✅ Linked | 0 | ✅ Fixed |
| 11 | HashTable | §11.4 | ✅ key_in_table | ✅ Linked O(n) | 0 | |
| 12 | BST Search/Min/Max | §12.2 | ✅ correct search | ✅ Linked O(h) | 0 | |
| 12 | BST Insert | §12.3 | ⚠️ membership only | ⚠️ Separate O(h) | 3 | ⚠️ Doesn't walk BST path |
| 12 | BST Delete | §12.3 | ✅ key_set \ {k} | ✅ Linked O(h) | 0 | FiniteSet algebra |
| 13 | RBTree (Pulse) | §13.1–4 | ❌ BROKEN | — | 0 | No fixup/rotations/BST path |
| 13 | RBTree.Spec (pure) | §13.1–4 | ✅ Okasaki balance | ✅ Linked O(lg n) | 0 | Correct but not Pulse |
| 15 | LCS | §15.4 | ✅ result=spec | ✅ Linked O(mn) | 0 | |
| 15 | MatrixChain | §15.2 | ✅ result=spec | ⚠️ Separate O(n³) | 0 | |
| 15 | RodCutting | §15.1 | ✅ optimal_revenue | ✅ Linked O(n²) | 0 | 1 assume val in Spec |
| 16 | ActivitySelection | §16.1 | ✅ greedy correct | ✅ Linked O(n) | 9 | Optimality unproven |
| 16 | Huffman.Complete | §16.3 | ⚠️ partial | ✅ Linked (cost) | 2 | ✅ Base case proven, assumes→admits |
| 16 | Huffman.Spec (pure) | §16.3 | ✅ htree, wpl | — | 0 | Disconnected from Pulse |
| 21 | Union-Find | §21.3 | ✅ find=root, union | ⚠️ Separate O(mn) | 5 | One-step compress |
| 22 | IterativeBFS | — | ⚠️ reachability only | — | 0 | ✅ Renamed (not CLRS) |
| 22 | QueueBFS | §22.2 | ⚠️ no shortest path | ✅ Linked O(n²) | 4 | d[v]=δ(s,v) not proven |
| 22 | IterativeDFS | — | ⚠️ reachability only | — | 0 | ✅ Renamed (not CLRS) |
| 22 | StackDFS | §22.3 | ⚠️ thms admitted | ✅ Linked O(n²) | 24 | Parenthesis thm admitted |
| 22 | KahnTopologicalSort | — | ✅ topo order ∧ distinct | ✅ Linked O(n²) | 4 | ✅ Renamed (not CLRS) |
| 22 | BFS/DFS specs | §22 | ⚠️ partial | — | 13 | Distance, timestamps, white-path |
| 23 | Kruskal | §23.2 | ⚠️ forest, not MST | ✅ Linked O(n³) | 21 | Cut property admitted |
| 23 | Prim | §23.2 | ✅ basic props | ✅ Linked O(n²) | 7 | ✅ Vacuous admit removed |
| 23 | MST.Spec | §23.1 | ⚠️ admitted | — | 5 | |
| 24 | Dijkstra | §24.3 | ⚠️ upper bound only | ✅ Linked O(n²) | 2 | ✅ 3→2 admits, infrastructure added |
| 24 | Bellman-Ford | §24.1 | ⚠️ upper bound only | ⚠️ Separate O(V³) | 3 | |
| 25 | Floyd-Warshall | §25.2 | ✅ result=spec | ✅ Linked O(n³) | 0 | |
| 26 | MaxFlow | §26.2 | ❌ STUB | — | 0 | Stretch goal |
| 28 | MatrixMultiply | §28.1 | ✅ C=A·B | ✅ Linked O(n³) | 0 | |
| 28 | Strassen | §28.2 | ✅ quadrant algebra proven | ⚠️ Separate | 0 | Pure F* |
| 31 | GCD | §31.2 | ✅ result=gcd(a,b) | ✅ Linked O(lg b) | 0 | |
| 31 | ExtendedGCD | §31.2 | ✅ Bézout identity | — | 0 | Pure F* |
| 31 | ModExp | §31.6 | ✅ (b^e)%m | ✅ Linked O(lg e) | 0 | |
| 32 | NaiveStringMatch | §32.1 | ✅ all matches | ✅ Linked O(nm) | 0 | |
| 32 | KMP | §32.4 | ✅ prefix + matcher | ✅ Linked O(n+m)* | 7 | *Amortized admits |
| 32 | RabinKarp | §32.2 | ✅ rolling hash | ⚠️ Separate O(nm) | 3 | Sum hash, not polynomial |
| 33 | Segments | §33.1 | ✅ intersection | ⚠️ Separate O(1) | 0 | |
| 35 | VertexCover | §35.1 | ✅ valid cover | ⚠️ Separate O(V²) | 1 | 2-approx: 1 admit |

### Admit Distribution

| Chapter | Admits | Top files |
|---------|--------|-----------|
| ch22 (graphs) | 45 | StackDFS(11+13), QueueBFS(4+6), DFS.Spec(5), BFS.DistSpec(5), WhitePath(3), KahnTopoSort(4) |
| ch23 (MST) | 33 | Kruskal.Spec(15), Prim.Spec(6), MST.Spec(5), Kruskal.Cmplx(3), EdgeSort(2), Prim.Cmplx(1), main(1) |
| ch08 (sorting) | 21 | RadixSort.FullSort(7), RS.MultiDigit(4), RS.Stability(4), CS.Stable(3), RS.Spec(2), BucketSort(1) |
| ch16 (greedy) | 11 | ActivitySelection.Spec(9), Huffman.Complete(2) |
| ch32 (strings) | 10 | KMP.Complexity(7), RabinKarp.Spec(3) |
| ch09 (select) | 5 | PartialSelectionSort.Correctness(5) |
| ch24 (SSSP) | 5 | BellmanFord.Spec(3), Dijkstra.TriIneq(2) |
| ch21 (UF) | 5 | UnionFind.Spec(4), RankBound(1) |
| ch12 (BST) | 3 | BST.Insert.Spec(3) |
| Other | 7 | MaxSubarray.DC(1), RodCutting.Spec(1), VertexCover.Spec(1), Huffman.Complete(2), Prim.Cmplx(1), Kruskal(1) |
| **Total** | **147** | |

---

## Action Plan

### Phase A: Rename Non-CLRS Algorithms ✅
Keep all code and proofs. Rename to clarify what they actually implement.

- [x] A1: `MaxSubarray.fst` → `MaxSubarray.Kadane.fst` (ch04)
- [x] A2: `BFS.fst` → `IterativeBFS.fst` (ch22)
- [x] A3: `DFS.fst` → `IterativeDFS.fst` (ch22)
- [x] A4: `TopologicalSort.fst` → `KahnTopologicalSort.fst` (ch22)
- [x] A5: `Select.fst` → `PartialSelectionSort.fst` (ch09)

### Phase B: Critical Implementations (Highest Priority)

- [ ] B1: **RBTree in Pulse** — Pointer-based with Okasaki-style balance matching RBTree.Spec.fst.
  Insert with fixup, search, BST ordering + RB invariants maintained.
  Spec already verified (0 admits): `rbtree`, `balance` (4 rotations), `insert_is_rbtree`, `height_bound_theorem`.

- [ ] B2: **Dijkstra d[v]=δ(s,v)** — Prove CLRS Theorem 24.6 (exact shortest paths).
  Currently only upper bound. At extract-min, extracted vertex has exact distance.
  Files: Dijkstra.TriangleInequality.fst (2 admits, was 3), Dijkstra.Correctness.fst.
  Progress: Proved `relax_from_u_establishes_triangle_from_u` + infrastructure lemmas.
  Remaining: Need Dijkstra invariant (processed=optimal) for preservation proof.

- [ ] B3: **BST Insert path** — Walk comparison path, not append at next slot.
  Prove `keys(new) = keys(old) ∪ {k}`. BST.Insert.Spec.fst (3 admits).

### Phase C: Implement Missing CLRS Algorithms

- [ ] C1: DFS-based TopologicalSort (ch22) — sort by StackDFS finish times (after A4)
- [ ] C2: D&C MaxSubarray in Pulse (ch04) — from DivideConquer.fst pure spec (after A1)
- [ ] C3: Multi-digit RadixSort in Pulse (ch08) — stable CountingSort d times
- [ ] C4: Huffman tree construction (ch16) — tree merge loop + optimality

### Phase D: Missing CLRS Theorems

- [ ] D1: BFS shortest paths d[v]=δ(s,v) (Thm 22.5) — 5 admits
- [ ] D2: DFS parenthesis theorem (Thm 22.7) — 15+5 admits
- [ ] D3: MST cut property (Thm 23.1) — 5+15 admits. Very hard.
- [ ] D4: ActivitySelection optimality (Thm 16.1) — 9 admits
- [ ] D5: VertexCover 2-approximation (Thm 35.1) — 1 admit

### Phase E: Link Separate Complexity Proofs to Pulse

17 algorithms have pure F* complexity proofs not connected via ghost ticks.

- [ ] E1: Easy: CountingSort O(n+k), BellmanFord O(V³), MatrixChain O(n³)
- [ ] E2: Medium: MergeSort O(n lg n), Heapsort O(n lg n), Quicksort O(n²)
- [ ] E3: Remaining: RadixSort, Quickselect, Select, Stack/Queue, BST, UF, RabinKarp, Segments, VtxCover

### Phase F: Admit Elimination — Categorized by Approach

#### Tier 1: Automatable (Z3 with hints / simple lemma calls) — ~~16~~ 15 admits remaining
These were initially classified as automatable. After systematic attempts, only 1 was actually
closeable (`radix-full-269` ✅). The other 15 are blocked due to:
- Z3 quantifier instantiation failures (sorted_up_to_digit, is_sorted, is_permutation)
- Pulse while-loop encoding limitations (condition truth not in body)
- Missing upstream definitions (max_compatible_count, rank bound)
- Complex modular arithmetic needing substantial infrastructure

| File | Line(s) | Admits | Status |
|------|---------|--------|--------|
| Prim.Complexity | 130 | 1 | ❌ Blocked: Pulse loop invariant needs `v≤n` not `v≤n+1` |
| Kruskal.Complexity | 371, 390 | 2 | ❌ Blocked: Pulse admits + bound fails for n<3 + upstream assume_ at 333 |
| Kruskal.Spec | 452, 378 | 2 | ❌ Blocked: Not arithmetic—needs build_components induction + cut property |
| RadixSort.Stability | 150, 208 | 2 | ❌ Blocked: Z3 incomplete quantifiers on nested ∃/∀ in sorted_up_to_digit |
| **RadixSort.FullSort** | **269** | **1** | **✅ DONE: proved with SeqP.index_tail + explicit quantifier trigger** |
| RadixSort.FullSort | 183 | 1 | ❌ Blocked: Needs digit-shift + euclidean division chain |
| PartialSelect | 117 | 1 | ❌ Blocked: Z3 can't bridge count_occ/tail/sorted quantifiers |
| UnionFind.RankBound | 190 | 1 | ❌ Blocked: Needs FiniteSet cardinality reasoning |
| UnionFind.Spec | 92 | 1 | ❌ Blocked: Needs rank<n from RankBound (itself admitted) |
| Prim.Spec | 209, 270 | 2 | ❌ Blocked: Needs find_min_edge_aux trace, non-trivial helper |
| RabinKarp.Spec | 162 | 1 | ❌ Blocked: Horner evaluation modular arithmetic |
| ActivitySelection.Spec | 305 | 1 | ❌ Blocked: max_compatible_count (line 176) is itself admitted |

#### Tier 2: Helper lemmas (provable separately, then plugged in) — 70 admits
These need a standalone lemma proved first, then called at the admit site. Each lemma is
self-contained but requires careful F* proof engineering (induction, case analysis, etc.).

| File | Line(s) | Admits | Helper lemma needed |
|------|---------|--------|---------------------|
| **StackDFS.fst** | 192,364,369-371,432,435,440,540 | 9 | **Stack validity invariant**: peeked values < n, stack depth ≤ n, scan positions bounded. Single invariant addition to outer loop propagates to all sites. |
| **StackDFS.Complexity** | 219,479,485-488,557-559,672 | 9 | Same stack validity invariant as above, plus tick-count monotonicity lemmas. |
| **QueueBFS.fst** | 320 | 1 | **Queue-colored invariant**: all enqueued vertices are non-WHITE. Add to loop invariant; discover_vertex colors GRAY before enqueue. |
| **QueueBFS.fst** | 172 | 1 | **Queue cardinality**: each vertex enqueued at most once ⟹ `vtail < n`. Needs ghost set tracking discovered vertices. |
| **QueueBFS.fst** | 372, 379 | 2 | **Loop invariant restoration**: show `maybe_discover` preserves source properties and distance soundness for non-modified vertices. Frame reasoning. |
| **QueueBFS.Complexity** | 167,324,327,384,391,403 | 6 | Mirror of QueueBFS.fst: same invariants + tick arithmetic. |
| **RadixSort.Stability** | 179, 222 | 2 | **Stable-sort preservation**: equal-key elements maintain relative order ⟹ lower-digit ordering preserved. Needs pair-extraction from stability definition. |
| **RadixSort.Spec** | 342 | 1 | Same as Stability.179 but at spec level. |
| **RadixSort.FullSort** | 227 | 1 | **Digit dominance**: differing digit at position d₀ contributes ≥ base^d₀, overwhelming all lower digits. Geometric series bound. |
| **RadixSort.FullSort** | 352,356,377,381 | 4 | **Bridge admits**: reference results from RadixSort.Stability module. Resolve by completing that module first, then import. |
| **Kruskal.Spec** | 39,45,51,96,102,349,356,446,458,466 | 10 | Graph path lemmas: reversal, concatenation, component membership, decidability, spanning tree characterization. Each is 5-15 lines with path induction. |
| **Prim.Spec** | 195, 359, 380 | 3 | Prim step verification: trace `find_min_edge_aux`, inductive safety invariant, base case. |
| **BFS.DistanceSpec** | 219, 297 | 2 | L219: visited ⟹ path exists (parent-pointer reconstruction). L297: path concatenation (reachable transitivity). |
| **BellmanFord.Spec** | 452 | 1 | Negative cycle detection: post-(n-1)-round distance change ⟹ path with n+ edges ⟹ cycle. |
| **Dijkstra.TriIneq** | 311 | 1 | Combine `relax_from_u_establishes_all_from_u` + preservation for processed set to extend triangle. |
| **KahnTopologicalSort** | 372 | 1 | Output contains all n vertices: maintain visited-set invariant + pigeonhole. |
| **PartialSelect.Correctness** | 255, 297 | 2 | Count-based uniqueness: if `count_lt s v == k` and `count_le s v ≥ k+1`, then `v` is the k-th element. |
| **UnionFind.Spec** | 310, 320 | 2 | Path tracing after parent update / union: forest topology reasoning. |
| **ActivitySelection.Spec** | 112,319,491,521,550,637 | 6 | Exchange argument helpers: sorted compatibility, seq-to-list preservation, greedy optimality by list reasoning. |
| **RabinKarp.Spec** | 365, 394 | 2 | Hash no-false-negatives (depends on Tier 1 rolling hash proof) + combined correctness. |
| **MaxSubarray.DC** | 346 | 1 | D&C and Kadane equivalence: both compute max over all subarrays. |
| **BucketSort** | 359 | 1 | Sorted bucket concatenation: buckets with key₁ < key₂ maintain global order when concatenated. |
| **CountingSort.Stable** | 258 | 1 | Cumulative count bounds: after prefix sum + decrements, `1 ≤ C[v] ≤ len`. |
| **RodCutting.Spec** | 224 | 1 | `accum_max` equivalence with explicit recursion. α-equivalent functions in different scopes; needs restructuring. |

#### Tier 3: Expert guidance required (deep structural / new invariants) — 60 admits
These require fundamental proof architecture changes: new ghost state, new invariants
threaded through entire algorithms, or deep mathematical theorems.

| File | Line(s) | Admits | Why expert guidance is needed |
|------|---------|--------|------------------------------|
| **StackDFS.fst** | 455, 691 | 2 | Full DFS correctness postcondition: all vertices BLACK, valid discovery/finish times. Requires DFS tree formalization. |
| **StackDFS.Complexity** | 566,581,842,859 | 4 | Final complexity postconditions depend on full DFS correctness (Tier 3 above). |
| **CountingSort.Stable** | 282, 283 | 2 | Stability proof: backward traversal preserves relative order. Needs full loop invariant tracking position assignments. Permutation proof: each input element placed exactly once. |
| **RadixSort.FullSort** | 296 | 1 | Chain of 3 non-trivial lemmas: sorted_up_to_digit on all digits → pairwise ≤ → sorted. |
| **RadixSort.Spec** | 366 | 1 | Inductive radix sort correctness: permutation composition across d stable sorts. |
| **RadixSort.MultiDigit** | 395,416,499,535 | 4 | Full multi-digit radix sort correctness: stability reasoning + positional notation arithmetic. |
| **PartialSelect.Correctness** | 55, 65 | 2 | Entire partition and quickselect specs admitted as axioms. Needs ground-up implementation. |
| **BST.Insert.Spec** | 203,227,310 | 3 | Mutually-recursive structural induction on array-based tree. SMT struggles with `subtree_in_range` unfolding. |
| **DFS.Spec** | 590,654,685,704,721 | 5 | CLRS Theorems 22.7-22.8: parenthesis theorem, reachability, white-path theorem, cycle detection, topological sort property. Each requires induction over entire DFS execution. |
| **DFS.WhitePath** | 168,249,280 | 3 | White path transitivity + DFS ancestor equivalence. Needs DFS tree structure formalization. |
| **BFS.DistanceSpec** | 67,236,251 | 3 | L67: axiomatic definition. L236: hard direction of BFS correctness (no shorter path). L251: combines both directions. |
| **KahnTopologicalSort** | 439 | 1 | Topological order correctness: maintain `strong_order_inv` through main loop. |
| **Kruskal.Spec** | 283,410,435 | 3 | L283: acyclicity preservation (reachability/cycle equivalence). L410: spanning tree from n-1 edges + connectivity. L435: MST optimality by safe-edge induction. |
| **Kruskal.EdgeSorting** | 138, 173 | 2 | Insertion sort stability: position tracking through swap operations. |
| **Kruskal.fst** | 81 | 1 | Union-find cycle detection ⟹ forest acyclicity. Needs UF component invariant. |
| **Kruskal.Complexity** | 333 | 1 | Inner loop invariant restoration with complexity tracking. |
| **MST.Spec** | 253,270,302,340,358 | 5 | Core MST theory: cycle characterization, cut-crossing topology, MST exchange lemma (Theorem 23.1), generic MST correctness. |
| **Prim.Spec** | 410 | 1 | Result connects all vertices (spanning tree characterization). |
| **BellmanFord.Spec** | 235, 405 | 2 | L235: relaxation upper bound preservation (triangle inequality algebra). L405: CLRS Lemma 24.2 (path relaxation property). |
| **Dijkstra.TriIneq** | 288 | 1 | Triangle preservation for processed vertices: needs Dijkstra invariant coupling (processed = optimal distance). |
| **KMP.Complexity** | 191,265,294,301,435,474,480 | 7 | Amortized complexity: formal potential function + per-iteration progress. Stretch goal. |
| **ActivitySelection.Spec** | 176, 420 | 2 | L176: ghost supremum definition (cardinality over predicates). L420: full greedy optimality induction. |
| **Huffman.Complete** | 654, 824 | 2 | Multiset/permutation formalization + CLRS Theorem 16.3 (Huffman optimality). |
| **UnionFind.Spec** | 342 | 1 | Rank logarithmic bound: needs subtree_size ≥ 2^rank invariant formalization. |
| **VertexCover.Spec** | 506 | 1 | 2-approximation: ghost state tracking disjoint edge selection + matching lower bound. |

### Stretch Goals (Deferred)

- [ ] S1: MaxFlow Ford-Fulkerson (ch26) — full Edmonds-Karp. Currently stub.
- [ ] S2: Union-Find O(m·α(n)) amortized (ch21)
- [ ] S3: KMP O(n+m) amortized (ch32) — 3 admits
- [ ] S4: Max-flow min-cut theorem (ch26)
