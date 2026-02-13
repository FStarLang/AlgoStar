# AutoCLRS: Progress Plan — Full Functional Correctness & Complexity Analysis

**Goal:** For every algorithm, prove (1) functional correctness against a clean pure spec, and (2) complexity bounds via ghost tick counters in the postcondition.

**Complexity proof convention:** Each algorithm takes a `ghost_ctr: GR.ref nat` input. The postcondition asserts `GR.pts_to ghost_ctr (c0 + bound)` where `bound` is a formula on the input size (e.g., `n * (n - 1) / 2`).

**Functional correctness convention:** The imperative code is proven equivalent to a pure, total, recursive specification function. E.g., `result == sort_spec input` or `dist_seq == dijkstra_spec weights n source`.

---

## Phase 0: Critical Failures — Fix Broken Algorithms

### P0.1 Max Flow (Ch26) — Currently a no-op
- [ ] P0.1.1: Define pure spec for residual graph: `residual_capacity cap flow u v = cap[u][v] - flow[u][v] + flow[v][u]`
- [ ] P0.1.2: Define pure BFS spec on residual graph: `bfs_path residual n s t` returning `option (list nat)`
- [ ] P0.1.3: Define pure spec `bottleneck path flow cap` returning minimum residual capacity along path
- [ ] P0.1.4: Define pure spec `augment flow path bn` updating flow along augmenting path
- [ ] P0.1.5: Implement BFS on residual graph in Pulse (using queue from Ch10 or array-based)
- [ ] P0.1.6: Implement augmentation loop: while BFS finds s-t path, augment flow
- [ ] P0.1.7: Prove loop invariant: `respects_capacities flow cap n` maintained after each augmentation
- [ ] P0.1.8: Prove loop invariant: `flow_conservation flow n source sink` maintained after each augmentation
- [ ] P0.1.9: Prove termination: integer flow value strictly increases each iteration (for integer capacities)
- [ ] P0.1.10: Prove postcondition: final flow satisfies capacity constraints + conservation
- [ ] P0.1.11: Add ghost tick counter; prove O(VE²) complexity for Edmonds-Karp (BFS-based)
- [ ] P0.1.12: (Stretch) Prove max-flow min-cut theorem

### P0.2 BFS (Ch22) — Currently iterative relaxation, not BFS
- [ ] P0.2.1: Define pure spec for shortest unweighted distance: `bfs_dist adj n source v = min steps for path s→v`
- [ ] P0.2.2: Implement proper queue-based BFS (use Ch10 Queue or array-based circular buffer)
- [ ] P0.2.3: Maintain `dist[]` and `pred[]` (predecessor) arrays
- [ ] P0.2.4: Prove invariant: when vertex v is dequeued, `dist[v] = δ(s,v)` (shortest path distance)
- [ ] P0.2.5: Prove postcondition: `dist[v] == bfs_dist adj n source v` for all v
- [ ] P0.2.6: Prove postcondition: source visited, all reachable vertices visited
- [ ] P0.2.7: Add ghost tick counter; prove O(V + E) complexity (or O(V²) for adjacency matrix)

### P0.3 DFS (Ch22) — Currently identical to BFS
- [ ] P0.3.1: Define pure spec for DFS visit order with timestamps: `dfs_spec adj n source` returning `(discovery, finish, pred)` sequences
- [ ] P0.3.2: Implement recursive DFS (or iterative with explicit stack from Ch10)
- [ ] P0.3.3: Maintain `color[]` (white/gray/black), `d[]` (discovery time), `f[]` (finish time), `pred[]`
- [ ] P0.3.4: Prove parenthesis theorem: for all u,v, intervals [d[u],f[u]] and [d[v],f[v]] are either nested or disjoint
- [ ] P0.3.5: Prove white-path theorem: v is a descendant of u in DFS tree iff at time d[u] there is a white path from u to v
- [ ] P0.3.6: Classify edges (tree, back, forward, cross) based on colors at discovery time
- [ ] P0.3.7: Add ghost tick counter; prove O(V + E) complexity (or O(V²) for adjacency matrix)

### P0.4 Red-Black Tree (Ch13) — Missing RB invariants and fixup
- [ ] P0.4.1: Define pure spec for RB tree as inductive type: `rbtree = Leaf | Node color left key right`
- [ ] P0.4.2: Define RB invariants: (a) root is black, (b) red nodes have black children, (c) all paths have equal black-height, (d) BST ordering
- [ ] P0.4.3: Define pure `rb_insert_spec tree key` returning the balanced tree after insertion
- [ ] P0.4.4: Implement proper BST insert (find correct position by walking tree)
- [ ] P0.4.5: Implement RB-INSERT-FIXUP with all 6 cases (3 + 3 symmetric)
- [ ] P0.4.6: Prove RB invariants maintained after insert+fixup
- [ ] P0.4.7: Prove BST ordering maintained after insert+fixup
- [ ] P0.4.8: Prove black-height is O(log n); height ≤ 2·lg(n+1)
- [ ] P0.4.9: Add ghost tick counter; prove O(log n) for search and insert
- [ ] P0.4.10: (Stretch) Implement RB-DELETE and RB-DELETE-FIXUP

---

## Phase 1: Fix Major Shortcuts

### P1.1 Select (Ch09) — Replace selection sort with quickselect
- [ ] P1.1.1: Define pure spec: `select_spec s k = Seq.index (sort s) k`
- [ ] P1.1.2: Implement RANDOMIZED-SELECT using partition from Ch07
- [ ] P1.1.3: Prove postcondition: result == select_spec input k
- [ ] P1.1.4: Prove invariant: after partition, target is in one of the two halves
- [ ] P1.1.5: Add ghost tick counter; prove O(n) expected time (or O(n²) worst-case for deterministic)
- [ ] P1.1.6: (Stretch) Implement median-of-medians SELECT with O(n) worst case

### P1.2 Radix Sort (Ch08) — Implement multi-digit version *(d=1 documented)*
- [ ] P1.2.1: Define pure spec for digit extraction: `digit k d base = (k / base^d) % base`
- [ ] P1.2.2: Define stable sort spec: elements with equal keys maintain relative order
- [ ] P1.2.3: Implement RADIX-SORT with d passes of counting sort, least-significant digit first
- [ ] P1.2.4: Prove each pass maintains relative order of elements with equal digit values (stability)
- [ ] P1.2.5: Prove final array is sorted by full key value
- [ ] P1.2.6: Prove permutation of input
- [ ] P1.2.7: Add ghost tick counter; prove O(d(n+k)) complexity
- [x] P1.2.8: Updated documentation to honestly describe d=1 limitation and CLRS multi-pass structure

### P1.3 Huffman Coding (Ch16) — Implement actual tree construction
- [ ] P1.3.1: Define inductive Huffman tree type: `htree = Leaf freq char | Internal freq left right`
- [ ] P1.3.2: Define pure spec for Huffman cost: weighted path length
- [ ] P1.3.3: Implement priority-queue-based Huffman tree construction (CLRS §16.3)
- [ ] P1.3.4: Prove tree is a valid binary tree with all characters at leaves
- [ ] P1.3.5: Prove weighted path length equals accumulated cost
- [ ] P1.3.6: Prove greedy choice property: merging two minimum-frequency trees is optimal
- [ ] P1.3.7: Prove optimal substructure: subtrees of optimal tree are optimal for their character sets
- [ ] P1.3.8: Add ghost tick counter; prove O(n log n) with binary heap, or O(n²) with linear scan

### P1.4 BST Insert (Ch12) — Fix insert to maintain BST property *(Partial)*
- [x] P1.4.1: Added `subtree_in_range` (recursive BST with bounds) and `key_in_subtree` specs
- [x] P1.4.2: Proved BST stepping lemmas (key_not_in_right_if_less, key_not_in_left_if_greater)
- [ ] P1.4.3: Prove BST property maintained after insert (needs ghost bounds in loop invariant)
- [ ] P1.4.4: Prove set of keys is `old_keys ∪ {new_key}`
- [ ] P1.4.5: Add ghost tick counter; prove O(h) where h is tree height
- [ ] P1.4.6: Implement TREE-DELETE (CLRS §12.3)
- [ ] P1.4.7: Prove BST property maintained after delete

### P1.5 KMP Matcher (Ch32) — Complete the search
- [x] P1.5.1: Define pure spec for KMP match positions: `matches_at`, `check_match_at`, `count_matches_spec`
- [x] P1.5.2: Implement KMP-MATCHER using the existing prefix function (inner failure-link loop + match counting)
- [ ] P1.5.3: Strengthen postcondition to prove match count equals `count_matches_spec`
- [ ] P1.5.4: Add ghost tick counter; prove O(n + m) complexity

---

## Phase 2: Strengthen Existing Proofs — Functional Correctness

### P2.1 Bellman-Ford (Ch24) — Prove from relaxation invariants
- [ ] P2.1.1: Define pure shortest-path spec: `sp_dist weights n s v = minimum weight path from s to v` (or infinity)
- [ ] P2.1.2: Prove upper-bound property: `dist[v] ≥ δ(s,v)` at all times (Lemma 24.11)
- [ ] P2.1.3: Prove convergence: after i rounds, dist[v] correct for all v reachable in ≤ i edges (Lemma 24.2)
- [ ] P2.1.4: Prove triangle inequality as consequence of relaxation (not post-verification pass)
- [ ] P2.1.5: Remove the separate triangle-inequality verification pass
- [ ] P2.1.6: Prove postcondition: `no_neg_cycle ⟹ dist[v] == sp_dist weights n s v`
- [ ] P2.1.7: Prove negative-cycle detection correctness

### P2.2 Dijkstra (Ch24) — Prove from greedy invariants
- [ ] P2.2.1: Define pure spec (same `sp_dist` as Bellman-Ford, restricted to non-negative weights)
- [ ] P2.2.2: Prove greedy choice invariant: when u is extracted from queue, `dist[u] == δ(s,u)` (CLRS Theorem 24.6)
- [ ] P2.2.3: Prove triangle inequality from relaxation
- [ ] P2.2.4: Remove separate triangle-inequality verification pass
- [ ] P2.2.5: Prove postcondition: `dist[v] == sp_dist weights n s v`

### P2.3 Kruskal (Ch23) — Prove MST property
- [ ] P2.3.1: Define pure MST spec: spanning tree T of G with minimum total weight
- [ ] P2.3.2: Sort edges by weight (implement or assume pre-sorted)
- [ ] P2.3.3: Prove safe-edge property (cut property): lightest edge crossing a cut is in some MST
- [ ] P2.3.4: Prove postcondition: result is a spanning tree
- [ ] P2.3.5: Prove postcondition: result has minimum total weight among spanning trees
- [ ] P2.3.6: Add ghost tick counter; prove O(E log E) (or O(E α(V)) with union-by-rank + path compression)

### P2.4 Prim (Ch23) — Prove MST property
- [ ] P2.4.1: Prove safe-edge property: minimum-weight edge connecting tree to non-tree vertex is safe
- [ ] P2.4.2: Prove postcondition: result is a spanning tree
- [ ] P2.4.3: Prove postcondition: result has minimum total weight
- [ ] P2.4.4: Add ghost tick counter; prove O(V²) for adjacency matrix

### P2.5 Topological Sort (Ch22) — Prove ordering property *(Documented)*
- [ ] P2.5.1: Define pure spec: `is_topological_order adj n order ⟺ ∀ (u,v) ∈ E, pos(u) < pos(v)`
- [ ] P2.5.2: Prove Kahn's algorithm produces a valid topological order
- [x] P2.5.3: Documented postcondition limitations and proof strategy (visited array, distinctness, ordering)
- [ ] P2.5.4: Add ghost tick counter; prove O(V + E)
- [ ] P2.5.5: (Stretch) Implement DFS-based topological sort and prove equivalence

### P2.6 Activity Selection (Ch16) — Prove optimality *(Greedy Choice done)*
- [x] P2.6.1: Defined `is_valid_selection` predicate for compatible activity selections
- [x] P2.6.2: Proved greedy choice property: replacing first activity with earliest-finishing yields valid selection (CLRS Theorem 16.1)
- [ ] P2.6.3: Prove optimal substructure: after removing first choice, remaining problem has optimal substructure
- [ ] P2.6.4: Prove full optimality: `|selected| == max_compatible_set start finish n`

### P2.7 Vertex Cover (Ch35) — Prove approximation ratio
- [ ] P2.7.1: Define pure spec: `min_vertex_cover adj n` = minimum cardinality vertex cover
- [ ] P2.7.2: Prove output is a valid vertex cover (already done)
- [ ] P2.7.3: Prove `|cover| ≤ 2 * min_vertex_cover adj n` (CLRS Theorem 35.1)
- [ ] P2.7.4: Key lemma: the algorithm picks a maximal matching; each matching edge contributes 2 vertices, each optimal cover must include ≥ 1 vertex per matching edge

### P2.8 Union-Find (Ch21) — Add path compression and rank *(Partially Completed)*
- [x] P2.8.1: Added `find_compress` with one-step path compression (parent[x] = root)
- [x] P2.8.2: Fixed union-by-rank: rank increment on equal-rank merge (CLRS line 5-6)
- [ ] P2.8.3: Prove rank invariants: rank[x] ≤ rank[parent[x]] when x is not root
- [ ] P2.8.4: Prove tree height ≤ rank ≤ ⌊log n⌋
- [ ] P2.8.5: (Stretch) Full path compression (all nodes on path → root); requires acyclicity proof
- [ ] P2.8.6: (Stretch) Prove amortized O(α(n)) per operation

### P2.9 Hash Table (Ch11) — Strengthen functional abstraction
- [ ] P2.9.1: Define pure `map` spec: `ht_spec table = Map from key to option value`
- [ ] P2.9.2: Prove `insert key val; search key == Some val`
- [ ] P2.9.3: Prove `search key == None` when key not inserted
- [ ] P2.9.4: Add ghost tick counter; prove O(n) worst case per operation (O(1) amortized requires load factor analysis)

### P2.10 Linked List (Ch10) — Add delete operation
- [ ] P2.10.1: Implement LIST-DELETE (CLRS §10.2)
- [ ] P2.10.2: Prove list contents after delete = list contents before delete minus the deleted element
- [ ] P2.10.3: Add ghost tick counter; prove O(n) for search, O(1) for insert/delete

---

## Phase 3: Add Missing Complexity Proofs

### P3.1 MergeSort O(n log n) *(Pure proof completed)*
- [x] P3.1.1: Pure proof of T(n) ≤ 4n(log₂ n + 1) via recurrence analysis
- [x] P3.1.2: Defined merge_sort_comparisons recurrence and log2_ceil
- [ ] P3.1.3: Thread ghost tick counter through Pulse merge_sort_aux and merge_impl
- [ ] P3.1.4: Connect Pulse implementation to pure recurrence bound

### P3.2 Heapsort O(n log n) *(Pure proof completed)*
- [x] P3.2.1: Pure proof of heapsort_comparisons ≤ 2n(1 + log₂ n)
- [x] P3.2.2: Proved log2_floor monotonicity and tight bounds
- [x] P3.2.3: Proved extract_max_comparisons ≤ 2n·log₂ n
- [ ] P3.2.4: Thread ghost tick counter through Pulse max_heapify and heapsort

### P3.3 Quicksort O(n²) worst case *(Pure proof completed)*
- [x] P3.3.1: Add ghost tick counter to partition (CLRS.Ch07.Partition.Complexity.fst) — proves exactly n comparisons
- [x] P3.3.2: Proved worst_case_comparisons n = n(n-1)/2 (CLRS Theorem 7.4)
- [x] P3.3.3: Proved sum_of_parts_bound: T(a)+T(b) ≤ T(a+b) (convexity)
- [x] P3.3.4: Proved maximality: for ANY partition split k, total ≤ T(n)
- [ ] P3.3.5: Thread tick counter through recursive quicksort Pulse code

### P3.4 Matrix Chain O(n³) ✓ COMPLETED
- [x] P3.4.1: Pure proof: mc_inner_sum computes Σ_{l=2}^{n} (n-l+1)(l-1)
- [x] P3.4.2: Proved term_bound: each (n-l+1)(l-1) ≤ n²
- [x] P3.4.3: Proved mc_iterations_bound: total ≤ (n-1)·n² ≤ n³

### P3.5 GCD — Tighten to O(log min(a,b)) ✓ COMPLETED
- [x] P3.5.1: Proved two-step halving bound (Lamé's theorem): after 2 steps b ≤ b/2
- [x] P3.5.2: Proved lemma_mod_le_half: a%b ≤ a/2 when a ≥ b
- [x] P3.5.3: Proved gcd_steps(a,b) ≤ 2·num_bits(b) + 1 ∈ O(log b)

### P3.6 Rabin-Karp — Add complexity proof ✓ COMPLETED
- [x] P3.6.1: Proved best case O(n+m): rk_best_case ≤ n+1
- [x] P3.6.2: Proved worst case O(nm): rk_worst_case ≤ nm+1
- [x] P3.6.3: Proved best_le_worst (best case never exceeds worst case)

### P3.7 KMP — Add complexity proof ✓ COMPLETED
- [x] P3.7.1: Proved prefix function O(m): ≤ 2(m-1) comparisons via amortized potential
- [x] P3.7.2: Proved matcher O(n): ≤ 2n comparisons
- [x] P3.7.3: Proved total O(n+m): kmp_total ≤ 2(n+m) (CLRS Theorem 32.4)
- [x] P3.7.4: Proved KMP beats naive: ≤ 4n when m ≤ n

### P3.8 Remaining complexity proofs *(All key algorithms completed)*
- [x] P3.8.1: Stack push/pop: O(1), Queue enqueue/dequeue: O(1)
- [x] P3.8.2: LinkedList search: O(n), insert: O(1)
- [x] P3.8.3: Segment intersection test: O(1) (16 ops total)
- [x] P3.8.4: BST search: O(h) where h = ⌊log₂(cap)⌋
- [x] P3.8.5: Counting Sort: Θ(n+k) — exact 2n+k+1 iterations
- [x] P3.8.6: Bellman-Ford: O(V³) — V + (V-1)V² + V² ≤ 2V³
- [x] P3.8.7: Select (partial sort): O(nk) — k rounds × (n-1) comparisons
- [x] P3.8.8: BFS/DFS: O(V²) for adjacency matrix
- [x] P3.8.9: Kruskal: O(V³) — (V-1)×V² iterations
- [x] P3.8.10: Prim: O(V²) — V rounds of 2V operations
- [x] P3.8.11: Floyd-Warshall: fixed z3rlimit to restore O(n³) proof
- [x] P3.8.12: Hash Table: O(n) worst case for insert/search
- [x] P3.8.13: Union-Find: O(n) find, O(1) union
- [x] P3.8.14: Vertex Cover: O(V²) for adjacency matrix
- [x] P3.8.15: Matrix Chain: O(n³) — Σ(n-l+1)(l-1) ≤ n³

**Phase 3 Status: 32 complexity proof files across 21/23 chapters (only broken RBTree and MaxFlow lack proofs)**

---

## Phase 4: Polish and Extensions

### P4.1 Clean up MaxSubarray
- [ ] P4.1.1: Add CLRS's divide-and-conquer maximum subarray as a separate module
- [ ] P4.1.2: Prove O(n lg n) complexity for D&C version
- [ ] P4.1.3: Prove both versions compute the same result

### P4.2 Rabin-Karp hash improvement
- [ ] P4.2.1: Replace simple sum hash with CLRS's modular polynomial hash
- [ ] P4.2.2: Prove rolling hash update formula: h(s+1) = (d·(h(s) - T[s]·d^{m-1}) + T[s+m]) mod q

### P4.3 Simultaneous Min-Max (Ch09)
- [ ] P4.3.1: Implement 3⌊n/2⌋ comparison simultaneous min-max
- [ ] P4.3.2: Prove comparison count ≤ 3⌊n/2⌋

### P4.4 Missing CLRS algorithms (not currently in project)
- [ ] P4.4.1: Bucket Sort (Ch08) — implement and prove O(n) average case
- [ ] P4.4.2: Fibonacci Heap operations (Ch19) — if feasible
- [ ] P4.4.3: Strassen's Matrix Multiplication (Ch28) — O(n^{2.81})
- [ ] P4.4.4: Extended Euclidean Algorithm (Ch31) — prove Bézout coefficients

### P4.5 Documentation and README ✓ COMPLETED
- [x] P4.5.1: Updated README.md with per-chapter verification status table
- [x] P4.5.2: Removed false claims (Bucket Sort, Ford-Fulkerson 2-hop comment)
- [x] P4.5.3: Added verification status table with correctness, complexity, and CLRS fidelity columns
- [x] P4.5.4: Updated module-level documentation for Select, Huffman, RBTree, MaxFlow, RadixSort

---

## Summary: Task Counts by Phase

| Phase | Description | Total | Done | Remaining |
|-------|-------------|-------|------|-----------|
| P0 | Critical failures (MaxFlow, BFS, DFS, RBTree) | 41 | 3 | 38 |
| P1 | Major shortcuts (Select, RadixSort, Huffman, BST, KMP) | 31 | 6 | 25 |
| P2 | Strengthen proofs (SSSP, MST, TopSort, greedy optimality) | 41 | 5 | 36 |
| P3 | Add complexity proofs | 40 | 34 | 6 |
| P4 | Polish and extensions | 19 | 4 | 15 |
| **Total** | | **172** | **52** | **120** |

**Complexity proof coverage: 32 files across 21/23 chapters (91% chapter coverage, 4,704 lines)**
**Documentation: README, RESEARCH_DOC.md, PROGRESS_PLAN.md all up to date**

---

## Status Key

- `[ ]` — Not started
- `[~]` — In progress
- `[x]` — Complete
- `[!]` — Blocked (see notes)
