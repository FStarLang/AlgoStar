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

## Current Status (2025-02-15)

**167 F* files, ~49K lines, 155 admits across 38 files, `make -j128` clean (0 warnings, 0 errors)**

### Per-Algorithm Status Table

| Ch | Algorithm | CLRS § | Func. Spec | Complexity | Admits | Notes |
|----|-----------|--------|------------|------------|--------|-------|
| 02 | Insertion Sort | §2.1 | ✅ sorted ∧ perm | ✅ Linked O(n²) | 0 | |
| 02 | Merge Sort | §2.3 | ✅ sorted ∧ perm | ⚠️ Separate O(n lg n) | 0 | |
| 04 | Binary Search | §2.3 | ✅ found⟹match, ¬found⟹∉ | ✅ Linked O(lg n) | 0 | |
| 04 | MaxSubarray (Kadane) | — | ✅ result=spec | ✅ Linked O(n) | 0 | ⚠️ Not CLRS; rename pending |
| 04 | MaxSubarray D&C | §4.1 | ⚠️ 1 axiom | ⚠️ Separate O(n lg n) | 1 | Pure F* only |
| 06 | Heapsort | §6.4 | ✅ sorted ∧ perm | ⚠️ Separate O(n lg n) | 0 | |
| 07 | Partition (Lomuto) | §7.1 | ✅ partitioned ∧ perm | ✅ Linked O(n) | 0 | |
| 07 | Quicksort | §7.1 | ✅ sorted ∧ perm | ⚠️ Separate O(n²) | 0 | |
| 08 | CountingSort | §8.2 | ✅ sorted ∧ perm | ⚠️ Separate O(n+k) | 0 | In-place (not CLRS 4-phase) |
| 08 | CountingSort.Stable | §8.2 | ⚠️ assumed postcond | ⚠️ Separate | 4 | CLRS 4-phase, stability unproven |
| 08 | RadixSort (d=1) | §8.3 | ✅ sorted ∧ perm | ⚠️ Separate Θ(d(n+k)) | 0 | d=1 only |
| 08 | RadixSort.MultiDigit | §8.3 | ⚠️ partial | — | 4 | Pure F* only |
| 08 | BucketSort | §8.4 | ⚠️ no perm proof | — | 2 | |
| 09 | MinMax | §9.1 | ✅ correct min/max | ✅ Linked O(n) | 0 | |
| 09 | Select (partial sort) | — | ✅ perm ∧ prefix sorted | ⚠️ Separate O(nk) | 6 | ⚠️ Not CLRS; rename pending |
| 09 | Quickselect | §9.2 | ✅ perm ∧ result=s[k] | ⚠️ Separate O(n²) | 0 | |
| 10 | Stack | §10.1 | ✅ ghost list LIFO | ⚠️ Separate O(1) | 0 | |
| 10 | Queue | §10.1 | ✅ ghost list FIFO | ⚠️ Separate O(1) | 0 | |
| 10 | DLL | §10.2 | ✅ DLS segment pred | ✅ Linked | 1 | O(1) delete-node: ghost admit |
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
| 16 | Huffman (cost only) | §16.3 | ❌ no tree built | ✅ Linked (cost) | 2 | No tree/PQ |
| 16 | Huffman.Spec (pure) | §16.3 | ✅ htree, wpl | — | 0 | Disconnected from Pulse |
| 21 | Union-Find | §21.3 | ✅ find=root, union | ⚠️ Separate O(mn) | 5 | One-step compress |
| 22 | BFS (iterative) | — | ⚠️ reachability only | — | 0 | ⚠️ Not queue-based; rename pending |
| 22 | QueueBFS | §22.2 | ⚠️ no shortest path | ✅ Linked O(n²) | 4 | d[v]=δ(s,v) not proven |
| 22 | DFS (iterative) | — | ⚠️ reachability only | — | 0 | ⚠️ Not stack-based; rename pending |
| 22 | StackDFS | §22.3 | ⚠️ thms admitted | ✅ Linked O(n²) | 26 | Parenthesis thm admitted |
| 22 | TopologicalSort | — | ✅ topo order ∧ distinct | ✅ Linked O(n²) | 3 | ⚠️ Kahn's; rename pending |
| 22 | BFS/DFS specs | §22 | ⚠️ partial | — | 13 | Distance, timestamps, white-path |
| 23 | Kruskal | §23.2 | ⚠️ forest, not MST | ✅ Linked O(n³) | 22 | Cut property admitted |
| 23 | Prim | §23.2 | ⚠️ not MST | ✅ Linked O(n²) | 9 | MST correctness admitted |
| 23 | MST.Spec | §23.1 | ⚠️ admitted | — | 5 | |
| 24 | Dijkstra | §24.3 | ⚠️ upper bound only | ✅ Linked O(n²) | 3 | d[v]=δ(s,v) not proven |
| 24 | Bellman-Ford | §24.1 | ⚠️ upper bound only | ⚠️ Separate O(V³) | 3 | |
| 25 | Floyd-Warshall | §25.2 | ✅ result=spec | ✅ Linked O(n³) | 0 | |
| 26 | MaxFlow | §26.2 | ❌ STUB | — | 0 | Stretch goal |
| 28 | MatrixMultiply | §28.1 | ✅ C=A·B | ✅ Linked O(n³) | 0 | |
| 28 | Strassen | §28.2 | ⚠️ 1 structural admit | ⚠️ Separate | 1 | Pure F* |
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
| ch22 (graphs) | 53 | StackDFS(11+15), QueueBFS(4+7), DFS.Spec(5), BFS.DistSpec(5), WhitePath(3), TopSort(3) |
| ch23 (MST) | 36 | Kruskal.Spec(15), Prim.Spec(6), MST.Spec(5), Kruskal.Cmplx(4), EdgeSort(2), Prim.Cmplx(2), main(2) |
| ch08 (sorting) | 24 | RadixSort.FullSort(8), CS.Stable(4), RS.MultiDigit(4), RS.Stability(4), BucketSort(2), RS.Spec(2) |
| ch16 (greedy) | 11 | ActivitySelection.Spec(9), Huffman.Complete(2) |
| ch32 (strings) | 6 | KMP.Complexity(3), RabinKarp.Spec(3) |
| ch24 (SSSP) | 6 | BellmanFord.Spec(3), Dijkstra.TriIneq(3) |
| ch09 (select) | 6 | Select.Correctness(6) |
| ch21 (UF) | 5 | UnionFind.Spec(4), RankBound(1) |
| ch12 (BST) | 3 | BST.Insert.Spec(3) |
| Other | 5 | MaxSubarray.DC(1), DLL(1), RodCutting.Spec(1), Strassen(1), VertexCover.Spec(1) |
| **Total** | **155** | |

---

## Action Plan

### Phase A: Rename Non-CLRS Algorithms
Keep all code and proofs. Rename to clarify what they actually implement.

- [ ] A1: `MaxSubarray.fst` → `MaxSubarray.Kadane.fst` (ch04)
- [ ] A2: `BFS.fst` → `IterativeBFS.fst` (ch22)
- [ ] A3: `DFS.fst` → `IterativeDFS.fst` (ch22)
- [ ] A4: `TopologicalSort.fst` → `KahnTopologicalSort.fst` (ch22)
- [ ] A5: `Select.fst` → `PartialSelectionSort.fst` (ch09)

### Phase B: Critical Implementations (Highest Priority)

- [ ] B1: **RBTree in Pulse** — Pointer-based with Okasaki-style balance matching RBTree.Spec.fst.
  Insert with fixup, search, BST ordering + RB invariants maintained.
  Spec already verified (0 admits): `rbtree`, `balance` (4 rotations), `insert_is_rbtree`, `height_bound_theorem`.

- [ ] B2: **Dijkstra d[v]=δ(s,v)** — Prove CLRS Theorem 24.6 (exact shortest paths).
  Currently only upper bound. At extract-min, extracted vertex has exact distance.
  Files: Dijkstra.TriangleInequality.fst (3 admits), Dijkstra.Correctness.fst.

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

### Phase F: Admit Elimination

- [ ] F1: StackDFS bounds (ch22, 26 admits) — strengthen loop invariant
- [ ] F2: QueueBFS (ch22, 11 admits) — loop invariant framing
- [ ] F3: CountingSort.Stable (ch08, 4 admits) — cumulative count reasoning
- [ ] F4: RadixSort (ch08, 18 admits) — stability + digit arithmetic
- [ ] F5: Select.Correctness (ch09, 6 admits) — permutation reasoning
- [ ] F6: UnionFind.Spec (ch21, 5 admits) — union correctness + rank bound
- [ ] F7: BST.Insert.Spec (ch12, 3 admits) — structural BST reasoning (linked to B3)
- [ ] F8: RabinKarp.Spec (ch32, 3 admits) — hash correctness
- [ ] F9: DFS.Spec (ch22, 5 admits) — timestamp properties
- [ ] F10: BucketSort (ch08, 2 admits) — permutation proof

### Stretch Goals (Deferred)

- [ ] S1: MaxFlow Ford-Fulkerson (ch26) — full Edmonds-Karp. Currently stub.
- [ ] S2: Union-Find O(m·α(n)) amortized (ch21)
- [ ] S3: KMP O(n+m) amortized (ch32) — 3 admits
- [ ] S4: Max-flow min-cut theorem (ch26)
