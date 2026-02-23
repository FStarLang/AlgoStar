# AutoCLRS Comprehensive Audit — 2025-02-23

**Scope**: Every algorithm and data structure audited against CLRS 3e on four axes:
1. **CLRS Fidelity** — Does the code match the textbook algorithm and data structures?
2. **Functional Spec Strength** — Are postconditions precise, complete, and meaningful?
3. **Complexity Linkage** — Is the O(·) bound proven, and is it linked to the Pulse code via ghost ticks?
4. **Remaining Admits** — Honest accounting of every unproven obligation.

**Additionally**: Documentation (doc/*.rst) audited against code for accuracy.

**Methodology**: Exhaustive file-by-file review of all 180 F*/Pulse files across 22 chapters,
plus all 24 .rst documentation files.

**Codebase stats (2025-02-23)**:
- 180 F*/Pulse files, ~59,500 lines
- 148 files with zero unproven obligations (42,600 lines)
- 32 files with unproven obligations (16,900 lines)
- **97 unproven obligations** across production code: 67 admit(), 16 assume(), 2 assume val, 12 assume_
  (excludes ISSUE_*.fst test files)

**Change since AUDIT_0215 (2025-02-15)**:
- Total admits: 155 → 97 (−58, a 37% reduction)
- RBTree (Ch13): Fully rewritten — now pointer-based with rotations, zero admits (**was: BROKEN**)
- ActivitySelection (Ch16): Exchange argument fully proven, zero admits (**was: 9 admits**)
- RodCutting.Spec: Dead assume val removed (**was: 1 assume val**)
- StackDFS/QueueBFS main: Zero admits each (**was: 4 assume_ each**)
- UnionFind.RankBound/FindTermination: Fully proven
- RabinKarp.Spec: Fully proven (CLRS polynomial hash)
- MatrixChain.Spec: Fully proven (sentinel bridge + table filling)
- Dijkstra.Correctness: New file proves d[v]=δ(s,v) with zero admits

---

## Table of Contents
- [Chapter 02: Sorting](#chapter-02-getting-started)
- [Chapter 04: Divide & Conquer](#chapter-04-divide-and-conquer)
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
- [Documentation Audit](#documentation-audit)
- [Cross-Cutting Summary](#cross-cutting-summary)

---

## Chapter 02: Getting Started

### InsertionSort
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful. Backward-shift inner loop matches CLRS §2.1. |
| **Functional Spec** | ✅ **Strong**: `sorted s ∧ permutation s0 s`. Complete — both sortedness and content preservation proven. |
| **Complexity** | ✅ **LINKED**. Ghost ticks in Pulse prove ≤ n(n-1)/2 comparisons (O(n²)). Tight worst-case bound. |
| **Admits** | 0 |

### MergeSort
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful. Top-down recursive divide + merge, matches CLRS §2.3. |
| **Functional Spec** | ✅ **Strong**: `sorted s' ∧ permutation s s'`. Same strength as InsertionSort. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* proves T(n) ≤ 4n⌈lg n⌉ + 4n but NOT linked to Pulse code. No ghost ticks. The 4× constant is loose. |
| **Admits** | 0 |

---

## Chapter 04: Divide and Conquer

### BinarySearch
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful classic binary search. |
| **Functional Spec** | ✅ **Strong**: if found returns index where `s0[result] == key`; if not found returns n and proves `∀i. s0[i] ≠ key`. ⚠️ Minor gap: does not explicitly guarantee "if key exists, it MUST be found" (completeness is implicit from the not-found branch). |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove ≤ ⌊lg n⌋ + 1 comparisons. |
| **Admits** | 0 |

### MaxSubarray (Kadane's)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ❌ **Wrong algorithm.** Implements Kadane's O(n) greedy, NOT the CLRS §4.1 divide-and-conquer algorithm. ✅ Correctly renamed to `MaxSubarray.Kadane` to avoid confusion. |
| **Functional Spec** | ⚠️ **Weak (self-referential)**. Postcondition `result == max_subarray_spec s0` where `max_subarray_spec` IS the Kadane recurrence — proves the implementation equals its own specification. Does not independently prove "result is the maximum contiguous subarray sum over all subarrays". |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove exactly n operations (O(n)). |
| **Admits** | 0 |

### MaxSubarray.DivideConquer
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful. Pure F* implementation of FIND-MAX-CROSSING-SUBARRAY + FIND-MAXIMUM-SUBARRAY from CLRS §4.1. |
| **Functional Spec** | ⚠️ Partial. 1 assume val remains for DC–Kadane equivalence axiom. |
| **Complexity** | ❌ **SEPARATE**. Pure F* only. No Pulse implementation exists. |
| **Admits** | 1 (assume val: `axiom_dc_kadane_equivalence`) |

---

## Chapter 06: Heapsort

### Heapsort
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful. BUILD-MAX-HEAP + extract-max loop with MAX-HEAPIFY (sift-down), matching CLRS §6.4–6.5. |
| **Functional Spec** | ✅ **Strong**: `sorted s' ∧ permutation s s'`. Max-heap predicates well-defined. |
| **Complexity** | ⚠️ **SEPARATE**. Two pure F* files prove O(n lg n). Enhanced file proves detailed CLRS Theorems 6.3–6.4. NOT linked to Pulse via ghost ticks. |
| **Admits** | 0 |

---

## Chapter 07: Quicksort

### Partition (two variants)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Both Lomuto (CLRS §7.1) and two-pointer (Hoare) partition implemented. |
| **Functional Spec** | ✅ **Strong**: `is_partitioned s pivot split ∧ permutation s s_out`. Lomuto additionally proves pivot at returned index. |
| **Complexity (Partition)** | ✅ **LINKED**. Ghost ticks prove exactly n comparisons (linear). |
| **Admits** | 0 |

### Quicksort
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful recursive quicksort with partition matching CLRS §7.1. |
| **Functional Spec** | ✅ **Strong**: `sorted s ∧ between_bounds s lb rb ∧ permutation`. |
| **Complexity** | ✅ **LINKED** (Enhanced file). Ghost ticks prove worst-case ≤ n(n-1)/2 = O(n²). Also has separate pure O(n²) file. |
| **Admits** | 0 |

---

## Chapter 08: Linear-Time Sorting

### CountingSort (in-place, 2-phase)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ **Optimized variant**. Uses 2-phase (count + write-back) instead of CLRS 4-phase. Valid but NOT the textbook version. Inherently **unstable**. |
| **Functional Spec** | ✅ **Strong**: `sorted s ∧ permutation s0 s`. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* states O(n+k) = 2n+k+1 iterations. No ghost ticks. |
| **Admits** | 0 |

### CountingSort.Stable (CLRS 4-phase)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful 4-phase version: init, count, cumulative sum, backwards pass. Separate input/output arrays. |
| **Functional Spec** | ❌ **Weak (assumed)**. Postcondition `sorted ∧ permutation` but both are **assumed** (2 assume_). Position bounds also assumed (1 assume_). Stability not proven. |
| **Complexity** | ⚠️ **SEPARATE**. |
| **Admits** | 3 assume_ (position bounds, sorted postcondition, permutation postcondition) |

**Critical gap**: The CLRS-faithful CountingSort.Stable is the one needed for RadixSort stability,
but its key postconditions are assumed, not proven. This cascades to all RadixSort proofs.

### RadixSort (d=1 wrapper)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ **d=1 only.** Calls CountingSort once. CLRS §8.3 requires d passes for d-digit numbers. |
| **Functional Spec** | ✅ For d=1: `sorted s ∧ permutation s0 s`. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* proves Θ(d(n+k)). |
| **Admits** | 0 (but d=1 trivializes the algorithm) |

### RadixSort.MultiDigit / FullSort / Stability / Spec (pure specs)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Pure F* implements multi-digit passes (digit 0 to d-1). Correct LSD-first order. |
| **Functional Spec** | ⚠️ **Partial**. Digit decomposition and lexicographic ordering proven (significant progress). 10 admits remain across 4 files for: stability preservation, permutation composition, sorted_up_to_digit induction. |
| **Complexity** | ❌ No linked complexity proof for multi-digit version. |
| **Admits** | 10 total: FullSort(4), Stability(2), Spec(2), MultiDigit(2) |

### BucketSort
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Structural: buckets via filtering, insertion sort per bucket, concatenation. |
| **Functional Spec** | ⚠️ Partial: `sorted ys ∧ length ys == length xs` but **no permutation proof**. 1 admit for sorted concatenation of buckets. |
| **Complexity** | ❌ No formal complexity proof. |
| **Admits** | 1 |

---

## Chapter 09: Order Statistics

### MinMax
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful linear scan (CLRS §9.1). |
| **Functional Spec** | ✅ **Strong**: min/max value exists in array AND satisfies ordering. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove exactly n-1 comparisons. |
| **Admits** | 0 |

### SimultaneousMinMax
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful CLRS exercise: pair-based comparison (CLRS §9.1). |
| **Functional Spec** | ✅ **Strong**: returns (min, max) both in array with correct ordering. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove exactly 2(n-1) comparisons. |
| **Admits** | 0 |

### PartialSelectionSort
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ **Not a CLRS algorithm.** O(nk) partial selection sort. Correctly renamed. |
| **Functional Spec** | ✅ **Strong**: `permutation s0 s_final ∧ sorted_prefix s_final k ∧ prefix_leq_suffix s_final k ∧ result == s_final[k-1]`. Also has SortedPerm lemma proving uniqueness of sorted permutations. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* proves O(nk). |
| **Admits** | 0 (main). Some admits in Correctness(2), Complexity.Test(1) auxiliary files. |

### Quickselect
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful partition-based selection matching CLRS §9.2 (deterministic pivot). |
| **Functional Spec** | ✅ **Strong**: `permutation s0 s_final ∧ result == s_final[k]`. Partition ordering proven. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* proves O(n²) worst-case. |
| **Admits** | 0 |

---

## Chapter 10: Elementary Data Structures

### Stack
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful array-backed PUSH/POP/PEEK (CLRS §10.1). |
| **Functional Spec** | ✅ **Strong**: Ghost list tracks contents; LIFO: `stack_pop(stack_push s x) == (x, s)`. Array-backed with `stack_inv` linking array to ghost list. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* states O(1). No ghost ticks. |
| **Admits** | 0 |

### Queue
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful circular buffer queue (CLRS §10.1). |
| **Functional Spec** | ✅ **Strong**: Ghost list tracks contents; FIFO with modular arithmetic proven. `queue_inv` links circular buffer to ghost list. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* states O(1). No ghost ticks. |
| **Admits** | 0 |

### Singly-Linked List
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful pointer-based with separation logic predicate `is_dlist`. |
| **Functional Spec** | ✅ **Strong**: INSERT prepends, SEARCH returns mem, DELETE removes first occurrence. All linked to ghost list `l: list int`. |
| **Complexity** | No explicit complexity proof. |
| **Admits** | 0 |

### Doubly-Linked List
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful with prev+next pointers (CLRS §10.2). LIST-INSERT, LIST-SEARCH, LIST-DELETE. |
| **Functional Spec** | ✅ **Strong**: DLS segment predicate (separation logic) with ghost list. |
| **Complexity** | ✅ **LINKED** for DLL operations (ghost ticks in Complexity files). |
| **Admits** | 0 |

---

## Chapter 11: Hash Tables

### HashTable (Open Addressing, Linear Probing)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful: h(k,i) = (k mod size + i) mod size, sentinel values for empty(-1)/deleted(-2) (CLRS §11.4). |
| **Functional Spec** | ⚠️ **Partial**: Insert proves `key_in_table`; search proves `s[result] == key` on success. Pure Spec module has association-list model with insert/search/delete lemmas. Missing: no-duplicate guarantee on insert, complete not-found characterization. |
| **Complexity** | ✅ **LINKED**. Ghost ticks in Pulse prove worst-case O(n) probes per insert/search. |
| **Admits** | 0 |

---

## Chapter 12: Binary Search Trees

### BST Search / Min / Max / Delete
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ **Array-based** (index-based parent-child: left=2i+1, right=2i+2), not pointer-based as in CLRS. Search follows BST path correctly. Min/Max follow leftmost/rightmost. Delete uses simplified node marking (not full TRANSPLANT). |
| **Functional Spec** | ✅ Search: `found ⟹ keys match`. Delete.Spec (pure, pointer-based): proves `key_set(delete(t,k)) = key_set(t) \ {k}` via FiniteSet algebra. Array-based Delete only proves node becomes invalid. |
| **Complexity** | ⚠️ **SEPARATE** for array-based (BST.Complexity: pure, no ticks). ✅ **LINKED** for pure spec (BST.Spec.Complexity: tick functions prove O(h)). |
| **Admits** | 0 |

### BST Insert
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ Array-based insert. Does NOT walk the BST comparison path as CLRS specifies. |
| **Functional Spec** | ⚠️ **Weak**. Insert.Spec attempts to prove BST property preservation but has 3 admits for structural reasoning about array-based tree invariants. |
| **Complexity** | See above. |
| **Admits** | 3 (BST.Insert.Spec: subtree range preservation, disjoint subtree invariance, key set membership) |

---

## Chapter 13: Red-Black Trees

### RBTree (Pulse implementation) — **MAJOR IMPROVEMENT since AUDIT_0215**
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ **Fully rewritten.** Pointer-based (box-allocated nodes) with recursive separation logic predicate `is_rbtree`. Implements search, insert with Okasaki-style balance (4 rotation cases: LL, LR, RL, RR), and make_black. Real pointer rewiring for rotations. |
| **Functional Spec** | ✅ **Strong**: `is_rbtree y (S.insert 'ft k)` — Pulse implementation proven equivalent to pure functional spec. Search proven equivalent to pure `S.search`. |
| **Complexity** | ✅ **LINKED** to pure spec: `search_ticks ≤ 2·lg(n+1)+1`, `insert_ticks ≤ 2·lg(n+1)+2`. Combined with height bound → O(lg n). |
| **Admits** | 0 |

### RBTree.Spec (Pure functional spec)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Correct inductive `rbtree` type. Okasaki-style balance/insert with 4 rotation patterns. |
| **Functional Spec** | ✅ **Strong**: Proves BST ordering, no-red-red, same-black-height, root-black. **CLRS Theorem 13.1**: `height ≤ 2·lg(n+1)` fully proven. Insert preserves all RB invariants. Balance classifier for all 4 cases. |
| **Complexity** | ✅ **LINKED**: `search_ticks ≤ height+1`, `insert_ticks ≤ height+2`. |
| **Admits** | 0 |

**Note on CLRS fidelity**: Uses Okasaki-style balance (pattern-matching on tree structure) rather than CLRS's imperative LEFT-ROTATE/RIGHT-ROTATE + RB-INSERT-FIXUP with 6 cases. The Okasaki encoding is equivalent but more elegant for functional programming. Still missing: DELETE operation and its 8 fixup cases.

---

## Chapter 15: Dynamic Programming

### RodCutting
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful bottom-up (CLRS §15.1). Also has Extended version (CLRS EXTENDED-BOTTOM-UP-CUT-ROD). |
| **Functional Spec** | ✅ **Strong**: `result == optimal_revenue prices n`. Spec.fst proves **full optimality** via optimal substructure (CLRS Eq. 15.2). Extended proves `cuts_are_optimal`. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove exactly n(n+1)/2 = O(n²). |
| **Admits** | 0 |

### LCS
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful bottom-up DP table (CLRS §15.4). |
| **Functional Spec** | ✅ **Strong**: `result == lcs_length x y m n`. ⚠️ The spec is a recursive definition matching CLRS recurrence — it proves functional equivalence to the recurrence but does NOT independently prove "result is the length of a longest common subsequence" (i.e., no explicit proof that the recurrence actually computes LCS). |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove exactly (m+1)·(n+1) = O(mn). |
| **Admits** | 0 |

### MatrixChain — **MAJOR IMPROVEMENT since AUDIT_0215**
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful bottom-up (CLRS §15.2). |
| **Functional Spec** | ✅ **Strong**: `result == mc_result dims n`. Spec.fst proves **full optimality**: DP table equals recursive `mc_cost` (CLRS Eq. 15.7) via `dp_correct_upto` predicate and sentinel bridge proofs. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F*. States O(n³) but no ghost ticks in Pulse. |
| **Admits** | 0 |

---

## Chapter 16: Greedy Algorithms

### ActivitySelection — **MAJOR IMPROVEMENT since AUDIT_0215**
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful greedy by earliest finish time (CLRS §16.1). |
| **Functional Spec** | ✅ **Strong**: Proves ≥1 selected, ≤n selected, first (earliest finish) always selected, pairwise compatible, earliest_compatible property, AND **`count == max_compatible_count`** (optimality). Full exchange argument proven (CLRS Theorem 16.1). |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n). |
| **Admits** | 0 (both implementation and Spec/Lemmas) |

### Huffman
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ❌ **Pulse code only computes cost.** No tree construction in main Pulse code. Linear-scan find_min, not heap-based. Huffman.Complete has tree construction but with admits. |
| **Functional Spec** | ⚠️ **Partial**: Huffman.Spec defines correct `htree` type, proves `wpl_equals_cost` (WPL = sum of internal frequencies). But `greedy_choice_property` (CLRS Lemma 16.2) and `optimal_substructure_property` are **assumed**. |
| **Complexity** | ✅ **LINKED** for cost computation only (ghost ticks). Meaningless without tree construction. |
| **Admits** | 2 admit() in Complete + 4 assume() in Spec = 6 total |

---

## Chapter 21: Disjoint Sets

### Union-Find
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ MAKE-SET ✅, UNION-BY-RANK ✅. PATH COMPRESSION: main `find_compress` does **one-step only** (parent[x] = root). FullCompress.fst does full two-pass compression (CLRS §21.3) but is not the default. |
| **Functional Spec** | ✅ FIND returns root with `parent[root] == root`. UNION: roots connected after union. Rank invariant (`rank[x] < rank[parent[x]]`) fully proven. FindTermination and RankBound both proven (zero admits). |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* states O(m·n) naive bound only. CLRS's main result O(m·α(n)) amortized is **completely missing**. Inverse Ackermann not defined. |
| **Admits** | 1 assume (Spec: `ranks_bounded` precondition to avoid circular dependency) |

---

## Chapter 22: Elementary Graph Algorithms

### IterativeBFS (renamed, not CLRS)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ **NOT queue-based.** Uses level-by-level iterative relaxation (n rounds). Correctly renamed. |
| **Functional Spec** | ⚠️ Partial: proves source visited, all reachable discovered. No shortest-path property. |
| **Complexity** | ❌ No complexity proof. |
| **Admits** | 0 |

### QueueBFS — **IMPROVED since AUDIT_0215**
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful FIFO queue-based BFS with 3-coloring (WHITE/GRAY/BLACK), matches CLRS §22.2. |
| **Functional Spec** | ⚠️ Partial: proves source visited, dist[source]=0, all reachable visited, distance soundness. ❌ **Shortest-path property NOT proven** (d[v] = δ(s,v), CLRS Theorem 22.5). BFS.DistanceSpec has 2 admits for the hard direction. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n²) (adjacency matrix). |
| **Admits** | 0 in main (was 4 assume_). 6 assume_ remain in QueueBFS.Complexity. |

### IterativeDFS (renamed, not CLRS)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ **NOT recursive/stack-based.** Uses relaxation rounds. Correctly renamed. |
| **Functional Spec** | ⚠️ Partial: proves source visited, all reachable discovered. |
| **Complexity** | ❌ No complexity proof. |
| **Admits** | 0 |

### StackDFS — **IMPROVED since AUDIT_0215**
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful iterative DFS with explicit stack, 3-coloring, discovery/finish times, matches CLRS §22.3. |
| **Functional Spec** | ⚠️ Partial. Proves: all vertices BLACK at end, d[u]>0, f[u]>0, **d[u]<f[u]** (basic parenthesis). ❌ **Full parenthesis theorem** (interval nesting, CLRS Theorem 22.7) NOT in postcondition. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n²) (adjacency matrix). |
| **Admits** | 0 in main (was 4 assume_). 6 assume_ remain in StackDFS.Complexity. |

### BFS.DistanceSpec
| **Admits** | 2 (hard direction: "no shorter path exists" + combining both directions) |

### DFS.Spec
| **Admits** | 5 admit() + 2 assume() (parenthesis theorem, reachability, white-path theorem, cycle detection) |

### DFS.WhitePath
| **Admits** | 3 (white-path transitivity, DFS ancestor equivalence) |

### KahnTopologicalSort (renamed, not CLRS DFS-based) — **FULLY VERIFIED since AUDIT_0215**
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ⚠️ Uses **Kahn's algorithm** (in-degree based BFS), NOT CLRS DFS-based §22.4. Correctly renamed. Equivalent result, different algorithm. Split into Defs module (pure predicates/lemmas) + main Pulse module. |
| **Functional Spec** | ✅ **Strong**: output length == n, all distinct, valid indices, **is_topological_order** (for all edges (u,v), u before v in output). Proven via indeg_correct maintenance, pn_completeness, and pigeonhole via count_occurrences. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n²) (adjacency matrix). Complexity module also zero admits. |
| **Admits** | **0** across all files (KahnTopologicalSort, Defs, Defs.fsti, Complexity, Spec, Lemmas, Verified). Was 2 admits in AUDIT_0215. |

---

## Chapter 23: Minimum Spanning Trees

### Kruskal
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Sorts edges by weight, greedily adds if no cycle (via union-find). Matches CLRS §23.2. |
| **Functional Spec** | ⚠️ **Weak**: proves `edge_count ≤ n-1`, valid endpoints, `is_forest` (acyclicity). ❌ **NOT proven to be MINIMUM** — weight optimality missing. Forest acyclicity via union-find is assumed (`assume val lemma_kruskal_maintains_forest`). |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n³) (adjacency matrix, linear scan for min edge). |
| **Admits** | 1 assume val (forest lemma), 9 admit in Spec, 2 in EdgeSorting, 1 assume in SortedEdges, 2+1 in Complexity = **16 total across chapter** |

### Prim
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Array-based priority queue (linear scan extract-min), edge relaxation. Matches CLRS §23.3. |
| **Functional Spec** | ⚠️ **Weak**: proves `key[source] = 0`, all keys bounded. ❌ **MST correctness not proven**. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n²). |
| **Admits** | 6 in Prim.Spec (cut property, optimality, spanning) |

### MST.Spec (shared theory)
| **Admits** | 4 (cycle characterization, cut-crossing topology, generic MST correctness). Exchange lemma PROVEN. |

---

## Chapter 24: Single-Source Shortest Paths

### Dijkstra — **MAJOR IMPROVEMENT since AUDIT_0215**
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Array-based priority queue, extract-min, relax. Matches CLRS §24.3. Non-negative weights required. |
| **Functional Spec** | ⚠️ **Mixed**. Main Pulse code proves triangle inequality + **upper bound** `dist[v] ≤ sp_dist(s,v)`. New Dijkstra.Correctness.fst proves **`dist[u] == sp_dist(s,u)`** (CLRS Theorem 24.6) with **zero admits**, but this is a standalone pure proof, not directly in the Pulse postcondition. The chain from Pulse → Correctness → exact equality passes through 2 admits in TriangleInequality. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O(n²). |
| **Admits** | 0 (main Pulse), 0 (Correctness.fst), 2 (TriangleInequality: combining relaxation with processed-set invariant) |

**Assessment**: The Dijkstra exact-shortest-path proof is structurally complete (Correctness.fst) but the connection to the Pulse implementation goes through TriangleInequality which still has 2 admits. The end-to-end proof is NOT fully closed.

### Bellman-Ford
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ |V|-1 relaxation passes + negative cycle detection. Matches CLRS §24.1. |
| **Functional Spec** | ⚠️ Same as Dijkstra main: proves triangle inequality and **upper bound** `dist[v] ≤ sp_dist(s,v)`. ❌ Does NOT prove exact shortest paths. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* states O(V³) (adjacency matrix). No ghost ticks. |
| **Admits** | 0 (main Pulse), 3 in Spec (upper bound preservation, path relaxation, negative cycle detection) |

### ShortestPath.Spec (shared pure spec)
| Criterion | Assessment |
|-----------|-----------|
| **Functional Spec** | ✅ **Strong** definitions: path type, path_weight, sp_dist (shortest path distance), path validity. Zero admits. Used by both Dijkstra and Bellman-Ford. |
| **Admits** | 0 |

---

## Chapter 25: All-Pairs Shortest Paths

### Floyd-Warshall
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Triple-nested DP loop (k, i, j) with `d_ij = min(d_ij, d_ik + d_kj)`. Matches CLRS §25.2 exactly. |
| **Functional Spec** | ✅ **Strong**: `contents' == fw_outer(input, n, 0)`. Functional equivalence to pure spec proven. ⚠️ Note: proves equivalence to pure FW recurrence, but does not independently prove the recurrence computes all-pairs shortest paths. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove exactly n³ relaxation operations = O(n³). |
| **Admits** | 0 |

---

## Chapter 26: Maximum Flow

### MaxFlow (Ford-Fulkerson / Edmonds-Karp)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ❌ **STUB.** Initializes flow to zero and returns. No BFS augmenting paths, no residual graph, no iterative augmentation. |
| **Functional Spec** | ❌ **Trivial**: proves zero flow satisfies capacity constraints and flow conservation. Flow value = 0, not maximum. |
| **Complexity** | ❌ Stub. |
| **Admits** | 0 in main (trivially). 8 assume across Proofs(4) + Spec(2) + Complexity(2). |

---

## Chapter 28: Matrix Operations

### MatrixMultiply
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Standard O(n³) triple-nested loop (CLRS §28.1). |
| **Functional Spec** | ✅ **Strong**: `C[i][j] = Σ_{k} A[i][k] * B[k][j]` via `mat_mul_correct` predicate. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove exactly n³ multiply-add operations. |
| **Admits** | 0 |

### Strassen
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Pure F* (nested sequences). Computes 7 products P1–P7, assembles C11/C12/C21/C22. Matches CLRS §28.2. |
| **Functional Spec** | ⚠️ Partial: algebraic identities for C quadrants proven. 1 admit for structural property (quadrants are square and pow2). |
| **Complexity** | ❌ No complexity proof. O(n^{lg 7}) stated in comments only. |
| **Admits** | 1 |

---

## Chapter 31: Number Theory

### GCD (Euclid's Algorithm)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Iterative `gcd(a,b) = gcd(b, a mod b)` matching CLRS §31.1. |
| **Functional Spec** | ✅ **Strong**: `result == gcd_spec(a_init, b_init)`. |
| **Complexity** | ✅ **LINKED**. Ghost ticks + Lamé's theorem prove O(lg b): ≤ 2·log₂(b)+1 iterations. |
| **Admits** | 0 |

### ExtendedGCD
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Pure F* extended Euclid (CLRS §31.2). |
| **Functional Spec** | ✅ **Strong**: Full Bézout identity `a*x + b*y == d` where `d == gcd(a,b)`, plus `divides d a`, `divides d b`, and greatest-divisor property. |
| **Complexity** | ❌ Pure F* only. No Pulse implementation, no ghost ticks. |
| **Admits** | 0 |

### ModExp (Repeated Squaring)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Binary exponentiation via `e/2`, matches CLRS §31.6. |
| **Functional Spec** | ✅ **Strong**: `result == (b^e) % m`. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove ≤ log₂(e)+1 squarings. |
| **Admits** | 0 |

---

## Chapter 32: String Matching

### NaiveStringMatch
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ O(nm) brute force (CLRS §32.1). |
| **Functional Spec** | ✅ **Strong**: `result == count_matches_up_to(text, pattern, n-m+1)`. |
| **Complexity** | ✅ **LINKED**. Ghost ticks prove O((n-m+1)·m) comparisons. |
| **Admits** | 0 |

### KMP (Knuth-Morris-Pratt)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Both COMPUTE-PREFIX-FUNCTION and KMP-MATCHER implemented in Pulse (CLRS §32.3–32.4). |
| **Functional Spec** | ⚠️ **Mixed**: Prefix function proves `pi_correct` (longest proper prefix-suffix) — **strong**. Matcher proves count in [0, n+1] — **weak** (does not prove `count == count_matches_spec`). KMP.StrengthenedSpec documents what would be needed but is not implemented. |
| **Complexity** | ⚠️ **LINKED but 7 admits**. Ghost ticks in Pulse, but amortized O(n+m) bound has 7 admits for complex potential-function arguments. |
| **Admits** | 0 (main KMP.fst), 7 in KMP.Complexity |

### RabinKarp — **IMPROVED since AUDIT_0215**
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ **CLRS-faithful polynomial rolling hash** `Σ P[i]·d^{m-1-i} mod q`. Big-endian, matching CLRS §32.2. |
| **Functional Spec** | ✅ **Strong**: `result == count_matches_up_to(...)`. Rolling hash correctness fully proven (hash_inversion + rolling_hash_step_correct). No false positives, no false negatives. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* proves O(n+m) best-case, O(nm) worst-case. No ghost ticks. |
| **Admits** | 0 |

---

## Chapter 33: Computational Geometry

### Segments (Intersection Test)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Cross-product, direction, on-segment, segments-intersect all matching CLRS §33.1. |
| **Functional Spec** | ✅ **Strong**: each function proves `result == *_spec(...)`. |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* states O(1) per operation. No ghost ticks. |
| **Admits** | 0 |

---

## Chapter 35: Approximation Algorithms

### VertexCover (2-Approximation)
| Criterion | Assessment |
|-----------|-----------|
| **CLRS Fidelity** | ✅ Faithful greedy edge-selection (CLRS §35.1). |
| **Functional Spec** | ✅ Proves `is_cover` (all edges covered) and `2-approximation ratio` in postcondition: `count_cover ≤ 2 * opt`. ⚠️ 1 admit in Spec for matching extraction (connecting cover size to matching size requires ghost execution trace). |
| **Complexity** | ⚠️ **SEPARATE**. Pure F* states O(V²). No ghost ticks. |
| **Admits** | 0 (main), 1 (Spec: `approximation_ratio_theorem`) |

---

## Documentation Audit

### Overall Assessment

The documentation (24 .rst files) was audited against the code for accuracy.

**Strengths**:
- ✅ All zero-admit claims verified correct — no false claims of full verification
- ✅ Admits counts in all .rst files match actual code (spot-checked every chapter)
- ✅ All 22 code chapters have corresponding .rst files (except Ch26)
- ✅ All chapters included in `index.rst`
- ✅ 105 .fst files have SNIPPET markers for literalinclude references
- ✅ intro.rst accurately describes project status, process, and gaps

**Issues Found**:

| Issue | Severity | Details |
|-------|----------|--------|
| **Ch26 (MaxFlow) undocumented** | HIGH | Code exists in ch26-max-flow/ (6 files, 1,553 lines) but no ch26_max_flow.rst exists. intro.rst references it in the summary table but there's no chapter document. |
| **README overstatement** | MEDIUM | README.md claims "Zero admits across ~18,000 lines of verified code" but the repo has 97 unproven obligations. The ~18K refers to zero-admit files only, but this is misleading without qualification. The 42,600 zero-admit lines are the accurate number. |
| **Huffman admit classification** | LOW | Doc says "5 admits for Huffman" but actual breakdown is 2 admit() in Complete + 4 assume() in Spec = 6 total. Terminology slightly loose. |
| **Dijkstra exact-path claim** | LOW | doc/ch24_sssp.rst should clarify that Dijkstra.Correctness.fst proves d[v]=δ(s,v) but the chain to the Pulse implementation goes through 2 admits in TriangleInequality. |
| **LCS optimality claim** | LOW | Doc implies LCS is "fully proven" but it proves functional equivalence to the recurrence, not that the recurrence actually computes longest common subsequence length from first principles. Same pattern as Floyd-Warshall. |

---

## Cross-Cutting Summary

### Complexity Proof Classification

**LINKED (ghost ticks embedded in Pulse code — 28 algorithms):**
InsertionSort, BinarySearch, MaxSubarray(Kadane), Partition, Quicksort(Enhanced), MinMax, SimultaneousMinMax, DLL, HashTable, BST.Spec, RBTree(Spec+Pulse), LCS, RodCutting, ActivitySelection, Huffman(cost only), QueueBFS, StackDFS, KahnTopologicalSort, Kruskal, Prim, Dijkstra, FloydWarshall, MatrixMultiply, GCD, ModExp, NaiveStringMatch, KMP(with admits)

**SEPARATE (pure F*, NOT linked to Pulse — 17 algorithms):**
MergeSort, Heapsort, CountingSort, RadixSort, Quickselect, PartialSelectionSort, Stack, Queue, BST(array), MatrixChain, Quicksort(basic), UnionFind, BellmanFord, RabinKarp, Segments, VertexCover, Strassen

### Algorithm Fidelity Issues

| Issue | Severity | Status since 0215 |
|-------|----------|-------------------|
| ❌ MaxFlow is a stub (zero flow) | **Critical** | UNCHANGED |
| ❌ Huffman Pulse only computes cost | **Medium** | UNCHANGED |
| ⚠️ CountingSort.Stable postconditions assumed | Medium | UNCHANGED |
| ⚠️ RadixSort main is d=1 only | Medium | UNCHANGED |
| ⚠️ BST Insert doesn't walk BST path | Medium | UNCHANGED |
| ⚠️ Union-Find one-step compression (default) | Low | UNCHANGED |
| ⚠️ RabinKarp hash was wrong → NOW FIXED | ✅ RESOLVED | Was sum hash, now CLRS polynomial |
| ❌ RBTree was broken → NOW FIXED | ✅ RESOLVED | Fully rewritten, pointer-based |
| ⚠️ MaxSubarray.Kadane renamed | ✅ RESOLVED | Renamed, D&C version exists |
| ⚠️ BFS/DFS relaxation versions renamed | ✅ RESOLVED | Renamed to Iterative* |
| ⚠️ TopologicalSort renamed | ✅ RESOLVED | Renamed to KahnTopologicalSort |

### Key Spec Gaps (missing CLRS theorems)

| Missing Theorem | CLRS Reference | Status | Change since 0215 |
|----------------|----------------|--------|-------------------|
| BFS shortest paths: d[v] = δ(s,v) | Theorem 22.5 | ❌ 2 admits | UNCHANGED |
| DFS parenthesis theorem (full) | Theorem 22.7 | ⚠️ 5+2 admits | UNCHANGED |
| DFS white-path theorem | Theorem 22.9 | ❌ 3 admits | UNCHANGED |
| MST cut property | Theorem 23.1 | ⚠️ 4 admits | UNCHANGED |
| Kruskal MST optimality | Theorem 23.1 | ⚠️ 9 admits | UNCHANGED |
| Prim MST optimality | Theorem 23.1 | ⚠️ 6 admits | UNCHANGED |
| Dijkstra exact shortest paths | Theorem 24.6 | ⚠️ 2 admits remain in chain | **IMPROVED** (Correctness.fst zero admits) |
| Bellman-Ford exact shortest paths | Theorem 24.6 | ❌ 3 admits | UNCHANGED |
| Activity Selection optimality | Theorem 16.1 | ✅ **PROVEN** | **RESOLVED** (was 9 admits) |
| Huffman optimality | Theorem 16.3 | ❌ 6 admits | UNCHANGED |
| Union-Find O(m·α(n)) amortized | Theorem 21.14 | ❌ Missing | UNCHANGED |
| Vertex Cover 2-approx ratio | Theorem 35.1 | ⚠️ 1 admit | UNCHANGED |
| RB-Tree height bound (Pulse) | Theorem 13.1 | ✅ **PROVEN** | **RESOLVED** |
| MatrixChain optimality | §15.2 | ✅ **PROVEN** | **RESOLVED** |
| KMP amortized O(n+m) | §32.4 | ⚠️ 7 admits | UNCHANGED |

### Admit Breakdown by Category

| Category | Count | Examples |
|----------|-------|---------|
| Graph theory (MST cut, DFS timestamps, BFS distance) | ~32 | ch22, ch23 |
| Sorting stability & arithmetic (RadixSort) | ~14 | ch08 |
| Shortest path theory (SSSP exact paths) | ~5 | ch24 |
| Huffman optimality | ~6 | ch16 |
| Amortized complexity (KMP) | ~7 | ch32 |
| Max-flow infrastructure | ~8 | ch26 |
| BST array structural | ~3 | ch12 |
| Complexity file invariants | ~13 | ch22 (assume_), ch23 |
| Other (Strassen, VertexCover, UF, MaxSubarray) | ~5 | ch28, ch35, ch21, ch04 |
| **Total (production code)** | **~97** | |

### Strongest Chapters (zero admits, strong specs, linked complexity)

1. **Ch31 Number Theory**: GCD + ExtendedGCD + ModExp — all zero admits, Bézout identity, Lamé's theorem
2. **Ch15 Dynamic Programming**: RodCutting + LCS + MatrixChain — all zero admits, optimality proofs, linked complexity
3. **Ch02 Sorting**: InsertionSort + MergeSort — zero admits, sorted∧permutation
4. **Ch07 Quicksort**: Partition + Quicksort — zero admits, full spec, linked complexity
5. **Ch13 Red-Black Trees**: Pulse + Spec — zero admits, CLRS Theorem 13.1, O(lg n)
6. **Ch25 Floyd-Warshall**: Zero admits, exact spec, linked O(n³)
7. **Ch28 Matrix Multiply**: Zero admits, exact spec, linked O(n³)
8. **Ch32 NaiveStringMatch + RabinKarp**: Zero admits, exact match count, CLRS-faithful hash

### Weakest Chapters (most admits, weakest specs)

1. **Ch26 MaxFlow**: Stub implementation — 8 assumes, no real algorithm
2. **Ch23 MST**: 26 total admits across Kruskal+Prim+MST.Spec — no weight optimality proven
3. **Ch22 Graphs**: 24 total admits — no BFS shortest-path, partial DFS parenthesis, DFS spec heavily admitted
4. **Ch08 Linear Sorting**: 14 admits — CountingSort.Stable assumed, RadixSort multi-digit stability unproven
5. **Ch32 KMP Complexity**: 7 admits — amortized analysis skeleton only
6. **Ch16 Huffman**: 6 admits — optimality not proven, only cost computation in Pulse
