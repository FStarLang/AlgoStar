# AutoCLRS Comprehensive Audit — 2025-02-15

**Scope**: Every algorithm implementation audited against CLRS 3e on three axes:
1. **CLRS Fidelity** — Does the code match the textbook algorithm and data structures?
2. **Functional Spec Precision** — Are postconditions precise and complete?
3. **Complexity Linkage** — Is the O(·) bound proven, and is it linked to the Pulse code via ghost ticks?

**Methodology**: Exhaustive file-by-file review of all 167 F* files across 22 chapters.

**Codebase stats**: 155 admits across 38 files, ~49K lines of F* code.

---

## Table of Contents
- [Chapter 02: Sorting (Insertion Sort, Merge Sort)](#chapter-02-getting-started)
- [Chapter 04: Divide & Conquer (Binary Search, Max Subarray)](#chapter-04-divide-and-conquer)
- [Chapter 06: Heapsort](#chapter-06-heapsort)
- [Chapter 07: Quicksort](#chapter-07-quicksort)
- [Chapter 08: Linear-Time Sorting](#chapter-08-linear-time-sorting)
- [Chapter 09: Order Statistics](#chapter-09-order-statistics)
- [Chapter 10: Elementary Data Structures](#chapter-10-elementary-data-structures)
- [Chapter 11: Hash Tables](#chapter-11-hash-tables)
- [Chapter 12: Binary Search Trees](#chapter-12-binary-search-trees)
- [Chapter 13: Red-Black Trees](#chapter-13-red-black-trees)
- [Chapter 15: Dynamic Programming](#chapter-15-dynamic-programming)
- [Chapter 16: Greedy Algorithms](#chapter-16-greedy-algorithms)
- [Chapter 21: Disjoint Sets (Union-Find)](#chapter-21-disjoint-sets)
- [Chapter 22: Elementary Graph Algorithms](#chapter-22-elementary-graph-algorithms)
- [Chapter 23: Minimum Spanning Trees](#chapter-23-minimum-spanning-trees)
- [Chapter 24: Single-Source Shortest Paths](#chapter-24-single-source-shortest-paths)
- [Chapter 25: All-Pairs Shortest Paths](#chapter-25-all-pairs-shortest-paths)
- [Chapter 26: Maximum Flow](#chapter-26-maximum-flow)
- [Chapter 28: Matrix Operations](#chapter-28-matrix-operations)
- [Chapter 31: Number Theory](#chapter-31-number-theory)
- [Chapter 32: String Matching](#chapter-32-string-matching)
- [Chapter 33: Computational Geometry](#chapter-33-computational-geometry)
- [Chapter 35: Approximation Algorithms](#chapter-35-approximation-algorithms)
- [Cross-Cutting Summary](#cross-cutting-summary)

---

## Chapter 02: Getting Started

### InsertionSort
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful. Backward-shift inner loop matches CLRS §2.1. |
| **Functional Spec** | ✅ Precise: `sorted s ∧ permutation s0 s`. |
| **Complexity** | ✅ **LINKED**. Ghost ticks in Pulse prove ≤ n(n-1)/2 comparisons (O(n²)). |
| **Admits** | 0 |

### MergeSort
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful. Top-down recursive divide + merge, matches CLRS §2.3. |
| **Functional Spec** | ✅ Precise: `sorted s' ∧ permutation s s'`. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* proves T(n) ≤ 4n⌈lg n⌉ + 4n but NOT linked to Pulse code. No ghost ticks. |
| **Admits** | 0 |

---

## Chapter 04: Divide and Conquer

### BinarySearch
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful. Classic binary search matching CLRS §4.5. |
| **Functional Spec** | ✅ Precise: if found returns index where `s0[result] == key`; if not found returns n and proves `∀i. s0[i] ≠ key`. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove ≤ ⌊lg n⌋ + 1 comparisons. |
| **Admits** | 0 |

### MaxSubarray (Kadane's)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ❌ **Wrong algorithm.** Implements Kadane's O(n) greedy, NOT the CLRS §4.1 divide-and-conquer algorithm. |
| **Functional Spec** | ⚠️ Weak. Postcondition `result == max_subarray_spec s0` where spec IS the Kadane recurrence — proves it matches itself, not that it computes the maximum contiguous subarray sum from first principles. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove exactly n operations. But this is O(n) for Kadane's, not O(n lg n) for CLRS. |
| **Admits** | 0 |

### MaxSubarray.DivideConquer
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful. Pure F* implementation of FIND-MAX-CROSSING-SUBARRAY + FIND-MAXIMUM-SUBARRAY from CLRS §4.1. |
| **Functional Spec** | ⚠️ Partial. Proves structural properties but 1 admit remains for DC–Kadane equivalence axiom. |
| **Complexity** | ❌ **SEPARATE**. Pure F*. States O(n lg n) recurrence but no Pulse implementation exists. |
| **Admits** | 1 |

---

## Chapter 06: Heapsort

### Heapsort
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful. BUILD-MAX-HEAP + extract-max loop with MAX-HEAPIFY (sift-down), matching CLRS §6.4–6.5. |
| **Functional Spec** | ✅ Precise: `sorted s' ∧ permutation s s'`. Max-heap predicates well-defined. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* proves 2n + 2n·lg n = O(n lg n), but NOT linked to Pulse code via ghost ticks. |
| **Admits** | 0 |

---

## Chapter 07: Quicksort

### Partition (two variants)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Both Lomuto (CLRS §7.1) and two-pointer partition implemented. |
| **Functional Spec** | ✅ Precise: `is_partitioned s pivot split ∧ permutation s s_out`. |
| **Complexity (Partition)** | ✅ **LINKED**. Ghost ticks in Pulse for Partition.Complexity. |
| **Admits** | 0 |

### Quicksort
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful recursive quicksort with partition matching CLRS §7.1. |
| **Functional Spec** | ✅ Precise: `sorted s ∧ between_bounds s lb rb`. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* proves worst-case T(n) = n(n-1)/2 = O(n²). Not linked to Pulse. |
| **Admits** | 0 |

---

## Chapter 08: Linear-Time Sorting

### CountingSort (in-place)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ Optimized. Uses 2-phase (count + write-back) instead of CLRS 4-phase (count, cumulative, place backwards). Valid but NOT the textbook version. Inherently **unstable**. |
| **Functional Spec** | ✅ Precise: `sorted s ∧ permutation s0 s`. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* states O(n+k) but no ghost ticks. |
| **Admits** | 0 |

### CountingSort.Stable
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful 4-phase version: init, count, cumulative sum, backwards pass. Separate input/output arrays. |
| **Functional Spec** | ⚠️ Partial. Postcondition `sorted ∧ permutation` but both are **assumed** (2 assume_). Stability not proven. |
| **Complexity** | ⚠️ **SEPARATE**. |
| **Admits** | 4 (cumulative counts proof, position bounds, sorted/permutation postconditions) |

### RadixSort
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ **d=1 only.** Calls CountingSort once. CLRS §8.3 requires d passes for d-digit numbers. |
| **Functional Spec** | ✅ For d=1: `sorted s ∧ permutation s0 s`. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* proves Θ(d(n+k)). |
| **Admits** | 0 (but d=1 only) |

### RadixSort.MultiDigit (pure spec)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Pure F* implements multi-digit passes (digit 0 to d-1). |
| **Functional Spec** | ⚠️ Partial. 4 admits for stability and digit→value arithmetic. No Pulse implementation. |
| **Complexity** | ❌ No complexity proof for multi-digit version. |
| **Admits** | 4 |

### BucketSort
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Structural: buckets via filtering, insertion sort per bucket, concatenation. |
| **Functional Spec** | ⚠️ Partial: `sorted ys ∧ length ys == length xs` but **no permutation proof**. 1 admit for bucket monotonicity. |
| **Complexity** | ❌ Pure cost function only, not a proof. |
| **Admits** | 2 |

---

## Chapter 09: Order Statistics

### MinMax
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful linear scan (CLRS §9.1). |
| **Functional Spec** | ✅ Precise: `∃ k. s0[k] == result ∧ ∀ k. result ≤ s0[k]`. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n). |
| **Admits** | 0 |

### Select (partial sort)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ **Wrong algorithm.** O(nk) partial selection sort, NOT CLRS's O(n) RANDOMIZED-SELECT (§9.2) or median-of-medians SELECT (§9.3). |
| **Functional Spec** | ✅ Precise: `permutation s0 s_final ∧ sorted_prefix s_final k ∧ prefix_leq_suffix s_final k`. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* proves O(nk). Not CLRS O(n). |
| **Admits** | 0 (main), 6 in Select.Correctness (auxiliary) |

### Quickselect
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful partition-based selection matching CLRS §9.2 (deterministic pivot, not randomized). |
| **Functional Spec** | ✅ Precise: `permutation s0 s_final ∧ result == s_final[k]`. Missing explicit k-th order statement but recoverable from partition invariant. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* proves O(n²) worst-case. |
| **Admits** | 0 |

---

## Chapter 10: Elementary Data Structures

### Stack
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful array-backed PUSH/POP/PEEK (CLRS §10.1). |
| **Functional Spec** | ✅ Precise: ghost list tracks contents; push appends, pop returns last. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* states O(1) but no ghost ticks in Pulse. |
| **Admits** | 0 |

### Queue
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful circular buffer queue (CLRS §10.1). |
| **Functional Spec** | ✅ Precise: ghost list tracks contents; enqueue appends, dequeue returns first. Modular arithmetic proven. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* states O(1) but no ghost ticks. |
| **Admits** | 0 |

### Doubly-Linked List
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful with prev+next pointers (CLRS §10.2). LIST-INSERT, LIST-SEARCH, LIST-DELETE implemented. |
| **Functional Spec** | ✅ Precise: `dll hd' tl' (x :: l)` after insert; membership after search; `remove_first k l` after delete. |
| **Complexity** | ✅ **LINKED** for DLL operations (DoublyLinkedList.Complexity.fst has ghost ticks). Separate pure file also exists. |
| **Admits** | 1 (O(1) delete-node ghost split predicate) |

---

## Chapter 11: Hash Tables

### HashTable (Open Addressing, Linear Probing)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful: h(k,i) = (k mod size + i) mod size, sentinel values for empty/deleted (CLRS §11.4). |
| **Functional Spec** | ⚠️ Partial: insert proves `key_in_table`; search proves `s[result] == key` on success. Missing: no-duplicate guarantee on insert, complete not-found characterization. |
| **Complexity** | ✅ **LINKED**. Ghost ticks in Pulse prove worst-case O(n) probes per insert/search. |
| **Admits** | 0 |

---

## Chapter 12: Binary Search Trees

### BST Search / Min / Max / Delete
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ Array-based (index-based parent-child: left=2i+1, right=2i+2), not pointer-based. Search follows BST path correctly. Min/Max follow leftmost/rightmost. Delete uses simplified node marking (not full TRANSPLANT). |
| **Functional Spec** | ✅ Search: `found ⟹ keys match`. Delete.Spec (pointer-based pure spec): proves `key_set(delete(t,k)) = key_set(t) \ {k}` via FiniteSet algebra. Array-based Delete only proves node becomes invalid. |
| **Complexity** | ⚠️ **SEPARATE** (BST.Complexity.fst: pure, no ticks). BST.Spec.Complexity.fst: ✅ **LINKED** with ghost ticks for pure spec operations. |
| **Admits** | 0 (Delete.Spec), 0 (BST.fst) |
| **Missing** | TREE-SUCCESSOR, TREE-PREDECESSOR not implemented. |

### BST Insert
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ Array-based insert appends at next free slot, NOT walking the BST comparison path as CLRS specifies. |
| **Functional Spec** | ⚠️ Partial. Attempts to prove `key_in_subtree` (membership) but does NOT prove `keys(new) = keys(old) ∪ {k}`. |
| **Complexity** | See above. |
| **Admits** | 3 (structural reasoning about BST property and disjoint subtrees in array representation) |

---

## Chapter 13: Red-Black Trees

### RBTree (Pulse implementation)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ❌ **BROKEN.** Array-backed BST WITHOUT any Red-Black operations. No LEFT-ROTATE, RIGHT-ROTATE, RB-INSERT-FIXUP (0/6 cases), RB-DELETE (not implemented), RB-DELETE-FIXUP (not implemented). Colors exist as fields but are never set or maintained. Insert appends at next free slot — doesn't even follow BST comparison path. |
| **Functional Spec** | ❌ Weak: only proves "key exists somewhere after insert". No BST ordering. No RB invariants. |
| **Complexity** | N/A — implementation is non-functional. |
| **Admits** | 0 (trivially, since it doesn't prove anything meaningful) |

### RBTree.Spec (Pure functional spec)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Correct inductive `rbtree` type. Okasaki-style balance/insert with 4 rotation patterns. |
| **Functional Spec** | ✅ Proves BST ordering, no-red-red, same-black-height, root-black. Height bound theorem: h ≤ 2·lg(n+1) (CLRS Theorem 13.1). |
| **Complexity** | ✅ **LINKED** to pure functional spec: `search_ticks ≤ height+1`, `insert_ticks ≤ height+2`. Combined with height bound → O(lg n). |
| **Admits** | 0 |
| **Gap** | Pure spec is correct but Pulse implementation does NOT match it. No connection between the two. |

---

## Chapter 15: Dynamic Programming

### LCS
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful bottom-up DP table (CLRS §15.4). |
| **Functional Spec** | ✅ Precise: `result == lcs_length x y m n`. Optimality inherited from CLRS DP recurrence. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove exactly (m+1)·(n+1) ticks = O(mn). |
| **Admits** | 0 |

### MatrixChain
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful bottom-up (CLRS §15.2). |
| **Functional Spec** | ✅ Precise: `result == mc_outer(init_table, dims, n, 2)`. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F*. States O(n³) but no ghost ticks in Pulse. |
| **Admits** | 0 |

### RodCutting
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful bottom-up (CLRS §15.1). |
| **Functional Spec** | ✅ Precise: `result == optimal_revenue prices n`. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n²). |
| **Admits** | 0 (main), 1 assume val in RodCutting.Spec |

---

## Chapter 16: Greedy Algorithms

### ActivitySelection
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful greedy by earliest finish time (CLRS §16.1). |
| **Functional Spec** | ✅ Proves: ≥1 selected, ≤n selected, first (earliest finish) always selected, pairwise compatible. ❌ **Optimality NOT proven** (CLRS Theorem 16.1 exchange argument deferred — 9 admits in Spec.fst). |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n). |
| **Admits** | 0 (main), 9 in Spec (exchange argument for optimality) |

### Huffman
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ❌ **Only cost computation.** No tree construction, no priority queue, no merge loop. Linear-scan find_min, not heap-based. |
| **Functional Spec** | ❌ Weak: only proves `cost ≥ 0; cost > 0 when n > 1`. No tree structure, no prefix-free property, no optimality. |
| **Complexity** | ✅ **LINKED** for cost computation (ghost ticks). But the computed "cost" is not meaningful without tree construction. |
| **Admits** | 0 (main), 2 in Complete (theoretical properties) |
| **Spec** | ✅ Pure Huffman.Spec has correct `htree` type, `cost`, `weighted_path_length`, and `wpl_equals_cost` lemma. But disconnected from Pulse code. |

---

## Chapter 21: Disjoint Sets

### Union-Find
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ MAKE-SET ✅, UNION-BY-RANK ✅ (all 3 cases correct). PATH COMPRESSION: main `find_compress` does **one-step only** (not full CLRS compression). Separate `FullCompress.fst` does full two-pass compression but is not the default. |
| **Functional Spec** | ✅ FIND returns root with `parent[root] == root`. UNION: roots connected after union. ⚠️ `pure_union_correctness` (find(x)==find(y) after union) is **admitted** in Spec. Rank invariant (`rank[x] < rank[parent[x]]`) fully proven. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* states O(m·n) naive bound only. CLRS's main result O(m·α(n)) amortized is **completely missing**. Inverse Ackermann not defined. |
| **Admits** | 0 (main), 1 (RankBound), 4 (Spec — union correctness, rank logarithmic bound) |

---

## Chapter 22: Elementary Graph Algorithms

### BFS (simple — iterative relaxation)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ **NOT queue-based.** Uses level-by-level iterative relaxation (n rounds). Same result but different algorithm structure from CLRS §22.2. |
| **Functional Spec** | ⚠️ Partial: proves `dist[source] = 0`, all reachable visited, `reachable_in(source, v, dist[v])`. ❌ Does NOT prove **shortest-path property** d[v] = δ(s,v) (CLRS Theorem 22.5). |
| **Complexity** | ❌ No complexity proof. |
| **Admits** | 0 |

### QueueBFS
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful FIFO queue-based BFS with 3-coloring (WHITE/GRAY/BLACK), matches CLRS §22.2. |
| **Functional Spec** | ⚠️ Same partial spec as simple BFS. ❌ Shortest-path property NOT proven. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n²) (adjacency matrix). |
| **Admits** | 4 assume_ (loop invariant framing) |

### BFS.DistanceSpec
| **Admits** | 5 (shortest-path distance reasoning — genuinely hard graph theory) |

### DFS (simple — iterative relaxation)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ **NOT recursive/stack-based.** Uses relaxation rounds. No discovery/finish times. |
| **Functional Spec** | ⚠️ Partial: proves source visited, all reachable discovered. No DFS-specific properties. |
| **Complexity** | ❌ No complexity proof. |
| **Admits** | 0 |

### StackDFS
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful iterative DFS with explicit stack, 3-coloring (WHITE/GRAY/BLACK), discovery/finish times, matches CLRS §22.3. |
| **Functional Spec** | ⚠️ Partial. Discovery/finish times computed. ❌ **Parenthesis theorem** (d[u] < d[v] < f[v] < f[u]) is **admitted**. ❌ **White-path theorem** not proven. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n²) (adjacency matrix). |
| **Admits** | 11 assume_ (bounds), 15 in Complexity (invariants + parenthesis theorem) |

### DFS.Spec
| **Admits** | 5 (strong valid state invariant, timestamp properties) |

### DFS.WhitePath
| **Admits** | 3 (white-path theorem — genuinely hard) |

### TopologicalSort
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ Uses **Kahn's algorithm** (in-degree based BFS), NOT the CLRS DFS-based version (§22.4: sort by decreasing finish time). Equivalent result, different algorithm. |
| **Functional Spec** | ✅ Proves: output length = n, all distinct, is topological order (for all edges (u,v), u before v). |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n²) (adjacency matrix). |
| **Admits** | 2 (main), 1 (Complexity) |

---

## Chapter 23: Minimum Spanning Trees

### Kruskal
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Sorts edges by weight, greedily adds if no cycle (via union-find). Matches CLRS §23.2. |
| **Functional Spec** | ⚠️ Partial: proves `edge_count ≤ n-1`, valid endpoints, acyclicity (`is_forest`). ❌ **NOT proven to be MINIMUM** — weight optimality missing. `lemma_kruskal_maintains_forest` is assume val. Cut property admitted in MST.Spec. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n³) (adjacency matrix, linear scan for min edge). |
| **Admits** | 1 (main: forest lemma), 15 (Spec: cut property, safe edge), 4 (Complexity), 2 (EdgeSorting) |

### Prim
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Array-based priority queue (linear scan extract-min), edge relaxation. Matches CLRS §23.3 (array version). |
| **Functional Spec** | ⚠️ Partial: proves `key[source] = 0`, all keys bounded. ❌ **MST correctness admitted** (line 77). Weight optimality not proven. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n²). |
| **Admits** | 1 (main: MST correctness), 6 (Spec), 2 (Complexity) |

### MST.Spec (shared theory)
| **Admits** | 5 (cut property, cycle property — deep graph theory) |

---

## Chapter 24: Single-Source Shortest Paths

### Dijkstra
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Array-based priority queue, extract-min, relax. Matches CLRS §24.3. Non-negative weights required. |
| **Functional Spec** | ⚠️ Partial: proves `dist[source] = 0`, triangle inequality, **upper bound** `dist[v] ≤ δ(s,v)`. ❌ Does NOT prove **equality** `dist[v] = δ(s,v)` (CLRS Theorem 24.6). Only proves upper bound conditional on triangle inequality holding. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n²). |
| **Admits** | 0 (main), 3 (TriangleInequality spec) |

### Bellman-Ford
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ |V|-1 relaxation passes + negative cycle detection. Matches CLRS §24.1. |
| **Functional Spec** | ⚠️ Same as Dijkstra: proves triangle inequality and upper bound. ❌ Does NOT prove exact shortest paths `dist[v] = δ(s,v)`. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* states O(V³) (adjacency matrix). No ghost ticks. |
| **Admits** | 0 (main), 3 (Spec) |

---

## Chapter 25: All-Pairs Shortest Paths

### Floyd-Warshall
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Triple-nested DP loop (k, i, j) with `d_ij = min(d_ij, d_ik + d_kj)`. Matches CLRS §25.2 exactly. |
| **Functional Spec** | ✅ Precise: `contents' == fw_outer(input, n, 0)`. Functional equivalence to pure spec proven. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove exactly n³ relaxation operations = O(n³). |
| **Admits** | 0 |

---

## Chapter 26: Maximum Flow

### MaxFlow (Ford-Fulkerson / Edmonds-Karp)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ❌ **STUB.** Initializes flow to zero and returns. No BFS augmenting paths, no residual graph, no iterative augmentation. Comment explicitly says "full Ford-Fulkerson is future work." |
| **Functional Spec** | ❌ Trivial: proves zero flow satisfies capacity constraints and flow conservation. Flow value = 0, not maximum. |
| **Complexity** | ❌ Stub. MaxFlow.Complexity.fst exists but is non-functional. |
| **Admits** | 0 (trivially — no algorithm to admit) |
| **Spec** | MaxFlow.Spec.fst defines `valid_flow`, `augment_preserves_valid`, `max_flow_min_cut_theorem` but all are assume val / stubs. |

---

## Chapter 28: Matrix Operations

### MatrixMultiply
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Standard O(n³) triple-nested loop (CLRS §28.1). |
| **Functional Spec** | ✅ Precise: `C[i][j] = Σ_{k} A[i][k] * B[k][j]` via `mat_mul_correct` predicate. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove exactly n³ multiply-add operations. |
| **Admits** | 0 |

### Strassen
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Pure F* (nested sequences). Computes 7 products P1–P7, assembles C11/C12/C21/C22 from sums. Matches CLRS §28.2. |
| **Functional Spec** | ⚠️ Partial: algebraic identities for C quadrants proven. 1 admit for structural property (quadrants are square and pow2). |
| **Complexity** | ❌ No ghost ticks. States O(n^{lg 7}) ≈ O(n^{2.807}) in comments but not formally proven in Pulse. |
| **Admits** | 1 |

---

## Chapter 31: Number Theory

### GCD (Euclid's Algorithm)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Iterative `gcd(a,b) = gcd(b, a mod b)` matching CLRS §31.1. |
| **Functional Spec** | ✅ Precise: `result == gcd_spec(a_init, b_init)`. |
| **Complexity** | ✅ **LINKED**. Ghost ticks + Lamé's theorem prove O(lg b). |
| **Admits** | 0 |

### ExtendedGCD
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Pure F* extended Euclid (CLRS §31.2). |
| **Functional Spec** | ✅ Precise: Bézout identity `a*x + b*y == d` where `d == gcd(a,b)`. |
| **Complexity** | ❌ Pure F* only. No Pulse implementation, no ghost ticks. |
| **Admits** | 0 |

### ModExp (Repeated Squaring)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Binary exponentiation via `e/2`, matches CLRS §31.6. |
| **Functional Spec** | ✅ Precise: `result == (b^e) % m`. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(lg e) squarings. |
| **Admits** | 0 |

---

## Chapter 32: String Matching

### NaiveStringMatch
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ O(nm) brute force (CLRS §32.1). |
| **Functional Spec** | ✅ Precise: `result == count_matches_up_to(text, pattern, n-m+1)`. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O((n-m+1)·m) comparisons. |
| **Admits** | 0 |

### KMP (Knuth-Morris-Pratt)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Both COMPUTE-PREFIX-FUNCTION and KMP-MATCHER implemented in Pulse (CLRS §32.3–32.4). |
| **Functional Spec** | ✅ Precise: prefix function proves `pi_correct` (longest proper prefix-suffix). Matcher finds and counts all occurrences. |
| **Complexity** | ⚠️ **LINKED but 3 admits**. Ghost ticks in Pulse, but amortized O(n+m) invariants use 3 admits for complex amortized counting arguments. Plus 4 more in KMP.StrengthenedSpec/Complexity. |
| **Admits** | 0 (main KMP.fst), 3+4 in Complexity/Spec files |

### RabinKarp
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ **Simplified hash.** Uses character sum hash instead of CLRS polynomial rolling hash `Σ P[i]·d^{m-1-i} mod q`. Rolling update correctly implemented. |
| **Functional Spec** | ✅ Precise: `result == count_matches_up_to(...)`. Rolling hash lemmas proven. All occurrences found. |
| **Complexity** | ⚠️ **SEPARATE**. RabinKarp.Complexity.fst has no ghost ticks. |
| **Admits** | 0 (main), 3 (Spec) |

---

## Chapter 33: Computational Geometry

### Segments (Intersection Test)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Cross-product, direction, on-segment, segments-intersect all matching CLRS §33.1. Handles general + 4 collinear cases. |
| **Functional Spec** | ✅ Precise: each function proves `result == *_spec(...)`. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* states O(1) per operation. No ghost ticks. |
| **Admits** | 0 |

---

## Chapter 35: Approximation Algorithms

### VertexCover (2-Approximation)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful greedy edge-selection (CLRS §35.1). |
| **Functional Spec** | ✅ Proves `is_cover` (all edges covered). ⚠️ 2-approximation ratio `|C_alg| ≤ 2·OPT` has 1 admit (needs ghost execution trace to extract witness matching). |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* states O(V²). No ghost ticks. |
| **Admits** | 0 (main), 1 (Spec: approximation ratio theorem) |

---

## Cross-Cutting Summary

### Complexity Proof Classification

**LINKED (ghost ticks embedded in Pulse code — 24 files):**
InsertionSort, BinarySearch, MaxSubarray(Kadane), Partition, MinMax, DLL, HashTable, BST.Spec, RBTree(pure), LCS, RodCutting, ActivitySelection, Huffman(cost only), QueueBFS, StackDFS, TopologicalSort, Kruskal, Prim, Dijkstra, FloydWarshall, MaxFlow(stub), MatrixMultiply, GCD, ModExp, NaiveStringMatch, KMP

**SEPARATE (pure F*, NOT linked to Pulse — 17 files):**
MergeSort, Heapsort, Quicksort, CountingSort, RadixSort, Quickselect, Select, Stack/Queue/DataStructures, BST(array), MatrixChain, UnionFind, Graph, MST, BellmanFord, RabinKarp, Segments, VertexCover

### Algorithm Fidelity Issues

| Issue | Severity | Files |
|-------|----------|-------|
| ❌ MaxFlow is a stub (zero flow) | **Critical** | ch26 |
| ❌ RBTree Pulse has no fixup/rotations | **Critical** | ch13 |
| ⚠️ MaxSubarray uses Kadane's not CLRS D&C | Medium | ch04 |
| ⚠️ Select uses O(nk) not CLRS O(n) | Medium | ch09 |
| ⚠️ BFS/DFS simple versions use relaxation | Medium | ch22 |
| ⚠️ TopologicalSort uses Kahn's not DFS-based | Low | ch22 |
| ⚠️ RadixSort main is d=1 only | Medium | ch08 |
| ⚠️ CountingSort.Stable has assumed postconditions | Medium | ch08 |
| ⚠️ Huffman only computes cost, no tree | Medium | ch16 |
| ⚠️ RabinKarp uses sum hash not polynomial | Low | ch32 |
| ⚠️ Union-Find: one-step compression (default) | Low | ch21 |
| ⚠️ BST Insert appends, doesn't walk BST path | Medium | ch12 |

### Key Spec Gaps (missing CLRS theorems)

| Missing Theorem | CLRS Reference | Status |
|----------------|----------------|--------|
| BFS shortest paths: d[v] = δ(s,v) | Theorem 22.5 | ❌ Not proven |
| DFS parenthesis theorem | Theorem 22.7 | ⚠️ Admitted |
| DFS white-path theorem | Theorem 22.9 | ❌ Not proven |
| MST cut property | Theorem 23.1 | ⚠️ Admitted |
| SSSP exact shortest paths | Theorem 24.6 | ❌ Only upper bound |
| Activity Selection optimality | Theorem 16.1 | ⚠️ 9 admits |
| Union-Find O(m·α(n)) amortized | Theorem 21.14 | ❌ Missing |
| Huffman optimality | Theorem 16.3 | ❌ Missing |
| Vertex Cover 2-approx ratio | Theorem 35.1 | ⚠️ 1 admit |
| RB-Tree height bound (imperative) | Theorem 13.1 | ❌ Spec only (not Pulse) |

### Admit Breakdown by Category

| Category | Count | Examples |
|----------|-------|---------|
| Graph theory (MST cut, DFS timestamps) | ~59 | ch22, ch23 |
| Sorting stability & arithmetic | ~24 | ch08 |
| Greedy optimality (exchange arguments) | ~11 | ch16 |
| Algorithmic correctness (select, SSSP) | ~12 | ch09, ch24 |
| Structural reasoning (BST arrays, trees) | ~8 | ch12 |
| Loop invariant framing (bounds checks) | ~26 | ch22 |
| Other (complexity bounds, rank bounds) | ~15 | ch21, ch32 |
| **Total** | **155** | |
