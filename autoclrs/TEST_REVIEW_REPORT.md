# AutoCLRS ImplTest Review Report

This is a report summarizing the results of automating the testing of verified
libraries in AutoCLRS.

The main idea can be seen from a variety of angles:

* API Client Samples: For every verified library (algorithm or data structure),
  implement a client program to check that the library is actually usable, i.e.,
  its preconditions can be satisfied and its postconditions are strong enough to
  prove the expected results. Such client programs are also instructive API
  usage samples. 

* Two-sided Specifications: An old idea, popularized in the last decade
  especially by the [DeepSpec project](https://deepspec.org/page/Research/), is
  for specifications of verified components to be "two-sided". That is, a
  component sppecification should not only be strong enough to prove the
  correctness of the implementation, but also be strong enough to conduct proofs
  of clients of that component.  In other words, specifications of components
  should be "precise" enough to be used in client proofs.

* Intent formalization: Shuvendu Lahiri's work on [intent
  formalization](https://arxiv.org/abs/2406.09757) and [this
  repository](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs)
  in particular, is especially relevant. Lahiri proposes a framework for
  classifying the precision of specifications, and used agents to to apply it to
  the AutoCLRS proofs. The tests in this repository derive from Lahiri's
  framework.

The rest of this report is an AI authored summary of test results.

> Comprehensive review of all `ImplTest.fst` and `ImplTest.md` files across the AutoCLRS project.
> Generated 2025-03-17.

## Purpose of ImplTests

Each `ImplTest.fst` file serves as a **spec-precision validation test**: it constructs a small concrete input, calls the verified implementation, and proves that the postcondition uniquely determines (or tightly constrains) the output. The companion `.md` file documents findings and proof techniques. All tests target **zero admits and zero assumes**.

---

## Master Summary Table

| Ch | Algorithm | Spec Type | Precision | Coverage | #Tests | Admits | Key Spec Gaps |
|----|-----------|-----------|-----------|----------|--------|--------|---------------|
| 02 | Insertion Sort | Deterministic | ✅ Precise | Minimal | 1 (n=3) | 0 | None |
| 02 | Merge Sort | Deterministic | ✅ Precise | Minimal | 1 (n=3) | 0 | None |
| 04 | Binary Search | Deterministic | ✅ Precise | Minimal | 2 (found+not-found) | 0 | Duplicate-key behavior unspecified |
| 04 | Max Subarray (Kadane) | Deterministic | ✅ Precise | Minimal | 1 (n=3) | 0 | Returns only sum, not subarray indices |
| 04 | Matrix Multiply | Deterministic | ✅ Precise | Minimal | 1 (n=2) | 0 | None |
| 06 | Heapsort | Deterministic | ✅ Precise | Minimal | 1 (n=3) | 0 | None |
| 07 | Partition | **Relational** | ✅ Precise | Minimal | 1 (n=3) | 0 | None — correctly relational |
| 07 | Quicksort | Deterministic | ✅ Precise | Minimal | 1 (n=3) | 0 | None |
| 08 | Counting Sort (2 variants) | Deterministic | ✅ Precise | Moderate | 2 fns tested | 0 | `counting_sort_by_digit` untested; stability unverified |
| 09 | Min / Max | Deterministic | ✅ Precise | Minimal | 1 (n=3) | 0 | None — existence+universality is strongest |
| 09 | Simultaneous MinMax | Deterministic | ✅ Precise | Minimal | 1 (n=3) | 0 | None |
| 09 | Quickselect | Deterministic | ✅ Precise | Minimal | 2 (k=0, k=2) | 0 | None — `result==select_spec` is strongest |
| 09 | Partial Selection Sort | Relational (precise) | ✅ Precise | Minimal | 1 (k=1) | 0 | Opaque `permutation` requires completeness lemma |
| 10 | Stack | Deterministic | ✅ Precise | **Comprehensive** | Multi-op lifecycle | 0 | None |
| 10 | Queue | Deterministic | ✅ Precise | **Comprehensive** | Multi-op + wraparound | 0 | None |
| 10 | Doubly Linked List | Deterministic | ✅ Precise | **Comprehensive** | Multi-op lifecycle | 0 | `list_delete_last`, `list_delete_node` untested |
| 10 | Singly Linked List | Deterministic | ✅ Precise | **Comprehensive** | Full lifecycle | 0 | None |
| 11 | Hash Table | Relational/Precise | ⚠️ Weak insert | **Comprehensive** | 7 tests | 0 | Insert postcondition doesn't guarantee success |
| 12 | BST (Pointer) | Deterministic | ✅ Precise | **Comprehensive** | 14 pure + Pulse | 0 | None |
| 12 | BST (Array) | Relational/Existential | ❌ **Too weak** | Minimal | Partial | 0 | No reachability; insert→search broken |
| 13 | RB-Tree (Okasaki) | Deterministic | ✅ Precise | **Comprehensive** | 14 pure + Pulse | 0 | None |
| 13 | RB-Tree (CLRS) | Deterministic | ✅ Precise | **Comprehensive** | 14 pure + Pulse | 0 | None |
| 15 | Rod Cutting | Deterministic | ✅ Precise | Minimal | 1 (n=4) | 0 | None |
| 15 | Matrix Chain | Deterministic | ✅ Precise | Minimal | 1 (n=3) | 0 | None |
| 15 | LCS | Deterministic | ✅ Precise | Minimal | 1 (m=n=3) | 0 | None |
| 16 | Activity Selection | **Precise Relational** | ✅ Precise | **Comprehensive** | Count + indices + optimality | 0 | None — relational with earliest-compatible |
| 16 | Huffman Tree | **Precise Relational** | ✅ Precise | **Comprehensive** | Cost + multiset + optimality | 0 | None — optimality proven |
| 16 | Huffman Codec | Deterministic | ✅ Precise | **Comprehensive** | Encode + Decode | 0 | No round-trip (encode∘decode) test |
| 21 | Union-Find | Relational | ⚠️ Moderate | Minimal | 1 union on 3 elts | 0 | Rank bound not preserved in postcondition |
| 22 | BFS | **Relational/Imprecise** | ⚠️ **Weak** | Minimal | 1 (3-vertex chain) | 0 | **No shortest-path optimality in postcondition** |
| 22 | DFS | Relational | ⚠️ **Weak** | Minimal | 1 (3-vertex chain) | 0 | **Spec↔Impl disconnect**; theorems not exposed |
| 22 | Topological Sort | **Relational** | ✅ Precise | Moderate | 1 (3-vertex DAG) | 0 | None — correctly relational |
| 23 | Kruskal | Relational | ⚠️ **Weak** | Minimal | 1 (3-vertex triangle) | 0 | **No spanning tree or MST property** |
| 23 | Prim | Functional but weak | ❌ **Critical** | Minimal | 1 (3-vertex triangle) | 0 | **Postcondition admits incorrect outputs** |
| 24 | Bellman-Ford | Relational/Conditional | ⚠️ Moderate | Adequate | 1 (3-vertex, neg wts) | 0 | Correctness conditional on runtime boolean |
| 24 | Dijkstra | Deterministic | ✅ Precise | Minimal | 1 (3-vertex) | 0 | Predecessor array not verified |
| 25 | Floyd-Warshall | Deterministic | ✅ Precise | **Comprehensive** | All 9 entries + complexity | 0 | None |
| 26 | Max Flow (Edmonds-Karp) | Deterministic + Optimality | ✅ Precise | Minimal | 1 (2-vertex trivial) | 0 | Test graph too trivial |
| 31 | GCD | Deterministic | ✅ Precise | Minimal | 1 (gcd(12,8)) | 0 | None |
| 31 | ModExp (R-to-L) | Deterministic | ✅ Precise | Minimal | 1 (2¹⁰ mod 1000) | 0 | None |
| 31 | ModExp (L-to-R) | Deterministic | ✅ Precise | Minimal | 1 (3⁵ mod 7) | 0 | None |
| 32 | Naive String Match | Deterministic | ✅ Precise | Minimal | 1 (n=5, m=3) | 0 | None |
| 32 | KMP | Deterministic | ✅ Precise | Minimal | 1 (n=5, m=3) | 0 | Failure function not directly tested |
| 32 | Rabin-Karp | Deterministic | ✅ Precise | Minimal | 1 (n=5, m=3) | 0 | Hash collision handling not tested |
| 33 | Segments (primitives) | Deterministic | ✅ Precise | **Comprehensive** | 10 tests (all orientations) | 0 | Degenerate cases (zero-length segments) |
| 33 | Graham Scan | Deterministic | ✅ Precise | Minimal | 3 sub-functions | 0 | No interior-point pruning test |
| 33 | Jarvis March | Deterministic | ✅ Precise | Moderate | 3 fns + full march | 0 | No non-convex input test |
| 35 | Vertex Cover (2-approx) | **Relational** | ✅ Precise | **Comprehensive** | All valid covers enumerated | 0 | None — correctly relational |

**Legend:** ✅ = precise/strong, ⚠️ = has notable weakness, ❌ = critically weak

---

## Spec Classification

### Deterministic/Functional Specs (output uniquely determined)

These specs fully determine the output for any concrete input. The postcondition is of the form `result == f(input)` or equivalent constraints (sorted + permutation for sorting algorithms).

| Algorithm | Postcondition Pattern |
|-----------|----------------------|
| All sorting (Insertion, Merge, Heap, Quick, Counting) | `sorted(s) ∧ permutation(s₀, s)` |
| Binary Search | `s₀[result] == key` or `result == len` |
| Kadane Max Subarray | `result == max_subarray_spec s₀` |
| Matrix Multiply | `∀i,j. C[i,j] == Σₖ A[i,k]·B[k,j]` |
| Min / Max / SimultaneousMinMax | `∃ in array ∧ ≤ all others` |
| Quickselect | `result == select_spec s₀ k` |
| BST (Pointer), RB-Trees | Ghost tree determines exact structure |
| All DP (Rod, MatrixChain, LCS) | `result == dp_spec(input)` |
| Huffman Codec | `decode(bits, tree) == message` |
| Dijkstra, Floyd-Warshall | `dist[v] == sp_dist(source, v)` |
| GCD, ModExp, ModExpLR | `result == math_spec(args)` |
| All String Matching | `result == count_matches_spec(text, pattern)` |
| Segments primitives | `result == cross_product_spec(...)` |

### Precise Relational Specs (multiple correct outputs, all valid)

These specs allow multiple correct outputs by design — the algorithm has legitimate non-determinism or the problem has multiple optimal solutions. The postcondition constrains which outputs are valid without selecting one.

| Algorithm | Why Relational | Constraining Properties |
|-----------|---------------|------------------------|
| Partition (Ch07) | Pivot choice not prescribed | Left ≤ pivot < right, permutation preserved |
| Activity Selection (Ch16) | Multiple maximum-cardinality selections exist | Count is optimal, selected set is compatible, earliest-compatible |
| Huffman Tree (Ch16) | Multiple trees with same optimal WPL | Multiset preserved, WPL is optimal |
| Topological Sort (Ch22) | Multiple valid orderings for most DAGs | `is_topological_order`, all elements distinct |
| Vertex Cover (Ch35) | Approximation allows multiple valid covers | `is_cover`, binary vector, `count ≤ 2·OPT` |
| Partial Selection Sort (Ch09) | Permutation is opaque | `sorted_prefix ∧ prefix_leq_suffix ∧ permutation` |

### Specs with Gaps That Should Be Strengthened

These specs have postconditions that are weaker than what the algorithm actually guarantees, potentially admitting incorrect implementations.

#### ❌ Critical (postcondition admits wrong outputs)

| Algorithm | Gap | Impact | Suggested Fix |
|-----------|-----|--------|---------------|
| **Prim (Ch23)** | Only proves `key[source]==0`, `parent[source]==source`, `all keys ≤ 65535` | Admits `key=[0,65535,65535]` as valid output | Add `key[v] == weight(parent[v],v)`, parent validity, spanning tree structure |
| **BST Array (Ch12)** | Insert postcondition only guarantees `∃ idx. keys[idx]==key`; no reachability from root | Cannot prove insert→search composition | Add `key_in_subtree keys valid cap 0 key` to insert postcondition |

#### ⚠️ Significant (important properties missing from postcondition)

| Algorithm | Gap | Impact | Suggested Fix |
|-----------|-----|--------|---------------|
| **BFS (Ch22)** | No shortest-path optimality | Postcondition admits non-shortest distances on multi-path graphs | Add `∀w,k. reachable_in(w,k) ⟹ dist[w] ≤ k` |
| **DFS (Ch22)** | Spec↔Impl disconnect: pure spec proves parenthesis/white-path theorems but `Impl.fsti` doesn't expose them | Cannot use DFS theorems from implementation interface | Bridge 2D-spec to flat-impl representation; expose edge classification |
| **Kruskal (Ch23)** | Postcondition was opaque; even after `elim` lemma only proves forest (acyclic), not spanning tree or MST | Cannot prove spanning tree (n-1 edges, connected) or minimality | Add spanning tree constraint + MST optimality (cut property) |
| **Hash Table (Ch11)** | `hash_insert` doesn't guarantee success even when table has empty slots | Cannot prove insert returns `true` on non-full table | Add `success ⟺ ¬table_full` or guarantee success when slots available |
| **Union-Find (Ch21)** | `rank[i] < n` not preserved in postcondition of `union` | Breaks chaining of multiple `union` calls | Re-establish rank bound in union postcondition |
| **Bellman-Ford (Ch24)** | Correctness conditional on runtime boolean `no_neg_cycle` | Less direct than Dijkstra's unconditional postcondition | Consider exposing the math proof of no-neg-cycle as a lemma |

#### Minor Gaps (spec is correct but incomplete coverage)

| Algorithm | Gap |
|-----------|-----|
| Counting Sort (Ch08) | `counting_sort_by_digit` function untested; stability property unverified |
| Dijkstra (Ch24) | Predecessor array allocated but postcondition doesn't verify path reconstruction |
| DLL (Ch10) | `list_delete_last` and `list_delete_node` operations untested |
| Huffman Codec (Ch16) | No round-trip test (`encode ∘ decode == id`) |
| KMP (Ch32) | Failure function correctness not directly tested |
| Rabin-Karp (Ch32) | Hash collision handling not tested |
| Graham Scan (Ch33) | No test with interior points (pruning behavior) |
| Jarvis March (Ch33) | No test with non-convex input (interior points) |
| Binary Search (Ch04) | Behavior with duplicate keys unspecified |
| Max Subarray (Ch04) | Returns only sum value, not subarray indices |

---

## Test Coverage Analysis

### Comprehensive Tests (multi-operation lifecycle or multiple scenarios)

These tests go beyond single-input validation to test composition, lifecycle, or multiple behaviors:

| Test | What Makes It Comprehensive |
|------|-----------------------------|
| Stack (Ch10) | Push 3 values, pop all, peek mid-stack, verify empty |
| Queue (Ch10) | FIFO ordering + circular wraparound scenario |
| DLL (Ch10) | Head insert, tail insert, forward/backward search, delete, empty |
| Singly Linked List (Ch10) | Full insert/search/delete/empty lifecycle |
| Hash Table (Ch11) | 7 tests: empty search, insert→search, absent search, delete→search, insert_no_dup (2 cases), lifecycle |
| BST Pointer (Ch12) | 14 pure assertions + full Pulse lifecycle (3 inserts, 5 searches, delete, 3 more searches, free) |
| RB-Tree Okasaki (Ch13) | 14 pure assertions, rotations verified, full lifecycle |
| RB-Tree CLRS (Ch13) | Same as Okasaki but with CLRS-style rotations; demonstrates coloring difference |
| Activity Selection (Ch16) | Count + exact indices + optimality proof + greedy properties + complexity |
| Huffman Tree (Ch16) | Cost + multiset invariance + WPL optimality + complexity |
| Huffman Codec (Ch16) | Both encode and decode with manual tree construction |
| Floyd-Warshall (Ch25) | All 9 matrix entries + exact n³ complexity count |
| Segments (Ch33) | 10 tests covering all orientation cases (CCW, CW, collinear) + on_segment + intersection |
| Vertex Cover (Ch35) | All valid covers enumerated (4 of 8), invalid covers excluded, 2-approx bound verified |

### Minimal Tests (single small input, spec-precision check only)

Most tests follow this pattern: allocate a 3-element array, call the function, prove the output matches expected values via helper lemmas.

| Category | Algorithms |
|----------|-----------|
| Sorting (n=3, input=[3,1,2]) | Insertion Sort, Merge Sort, Heapsort, Quicksort, Counting Sort |
| Selection (n=3, input=[5,2,8]) | MinMax, SimultaneousMinMax, Quickselect, PartialSelectionSort |
| DP (small instances) | Rod Cutting (n=4), Matrix Chain (n=3), LCS (m=n=3) |
| Number Theory | GCD (12,8), ModExp (2¹⁰ mod 1000), ModExpLR (3⁵ mod 7) |
| String Matching (n=5, m=3) | Naive, KMP, Rabin-Karp |
| Graph Algorithms (n=3) | BFS, DFS, TopSort, Kruskal, Prim, Union-Find, Bellman-Ford, Dijkstra |
| Max Flow (n=2) | Edmonds-Karp |
| Convex Hull (3 points) | Graham Scan, Jarvis March |

---

## Proof Technique Patterns

### Pattern 1: Sorted-Permutation Uniqueness
Used by all sorting algorithms. A shared lemma `std_sort3` proves that `sorted(s) ∧ permutation([3,1,2], s)` uniquely determines `s = [1,2,3]` via element counting.

### Pattern 2: Pure Spec Normalization (`assert_norm`)
Used by DP algorithms, number theory, and BSTs. The pure spec function is evaluated at compile time via `assert_norm (spec(concrete_input) == expected_value)`.

### Pattern 3: Completeness Lemmas
When postconditions use opaque predicates (e.g., `SP.permutation`), a "completeness lemma" bridges the opaque predicate to concrete values using `reveal_opaque` and count-based reasoning.

### Pattern 4: Bridge Lemmas (Pure → Pulse)
BSTs and RB-Trees use helper lemmas to lift pure-spec assertions into Pulse (separation logic) contexts, bridging ghost-state reasoning with imperative code.

### Pattern 5: Optimality Arguments
Activity Selection and Max Flow use postcondition optimality clauses (`no_augmenting_path`, `max_compatible_count`) to prove the output is not just valid but optimal.

---

## Verification Health Summary

### Overall Statistics
- **Total ImplTest files**: 40 `.fst` files (+ 2 `.fsti` interface files for SSSP)
- **Total algorithms tested**: 38
- **Zero admits across all tests**: ✅ Yes (one platform assumption `SZ.fits_u64` in Prim is legitimate)
- **Zero assumes across all tests**: ✅ Yes

### By Spec Quality

| Quality Level | Count | Algorithms |
|---------------|-------|-----------|
| ✅ Precise & Complete | 28 | InsSort, MergeSort, Heapsort, Quicksort, Partition, BinSearch, Kadane, MatMul, MinMax, SimMinMax, Quickselect, PartSelSort, Stack, Queue, DLL, SLL, BST(Ptr), RBTree×2, RodCut, MatChain, LCS, ActSel, Huffman×2, TopSort, FW, Dijkstra, GCD, ModExp×2, NaiveMatch, KMP, RabinKarp, Segments, GrahamScan, JarvisMarch, VertexCover |
| ⚠️ Moderate gaps | 5 | HashTable, UnionFind, BellmanFord, MaxFlow, DFS |
| ❌ Critical gaps | 3 | Prim, BSTArray, BFS |

### By Test Coverage

| Coverage Level | Count | Algorithms |
|----------------|-------|-----------|
| Comprehensive | 14 | Stack, Queue, DLL, SLL, HashTable, BST(Ptr), RBTree×2, ActSel, Huffman×2, FW, Segments, VertexCover |
| Moderate | 4 | CountingSort, TopSort, JarvisMarch, BellmanFord |
| Minimal | 22 | All sorting (n=3), all selection, all DP, all number theory, all string matching, all graph (except TopSort/FW), MatMul, BinSearch, BSTArray, GrahamScan, MaxFlow |

---

## Priority Recommendations

### 1. Fix Critical Spec Gaps (High Priority)

These specs should be strengthened before they can be considered trustworthy:

1. **Prim (Ch23)**: Postcondition is almost vacuous. Needs key/parent relationship, spanning tree structure, MST optimality.
2. **BST Array (Ch12)**: Insert postcondition lacks reachability. Needs `key_in_subtree` guarantee to compose with search.
3. **BFS (Ch22)**: Missing shortest-path optimality defeats the purpose. Add `∀w,k. reachable(w,k) ⟹ dist[w] ≤ k`.

### 2. Bridge Spec↔Impl Gaps (Medium Priority)

4. **DFS (Ch22)**: Pure spec proves CLRS theorems (parenthesis, white-path, edge classification) but implementation interface doesn't expose them. Bridge the 2D/flat representation gap.
5. **Kruskal (Ch23)**: Strengthen from "forest" to "minimum spanning tree" (connectivity + minimality).

### 3. Strengthen Moderate Gaps (Medium Priority)

6. **Hash Table (Ch11)**: Add success guarantee when table not full.
7. **Union-Find (Ch21)**: Preserve rank bound through union postcondition.
8. **Counting Sort (Ch08)**: Test `counting_sort_by_digit`; verify stability.

### 4. Expand Test Coverage (Lower Priority)

Most minimal tests (n=3) are sufficient for proving spec precision but don't stress edge cases. Future work could add:
- Edge cases: empty inputs, single elements, all-equal, already-sorted, reverse-sorted
- Larger inputs to validate scaling behavior
- Adversarial inputs (all-negative for Kadane, disconnected graphs, negative cycles for Bellman-Ford)
- Duplicate handling (Binary Search, Hash Table)

---

## Appendix: Relational Specs Deep Dive

The following algorithms have **intentionally relational** specs — they correctly model problems where multiple valid outputs exist:

### Partition (Ch07)
The Lomuto partition spec says: left partition elements ≤ pivot, right partition elements > pivot, and output is a permutation. For `[3,1,2]`, three valid pivot choices exist. The spec does not prescribe which element becomes the pivot — this is correct since different partition strategies (Lomuto, Hoare, randomized) make different choices.

### Activity Selection (Ch16)
Multiple maximum-cardinality compatible subsets may exist. The spec constrains the output to be compatible, maximum-cardinality, and to satisfy the "earliest compatible" greedy property. This is tight enough to determine the exact output for the test case while remaining relational in general.

### Huffman Tree (Ch16)
Multiple tree structures can achieve the same optimal weighted path length. The spec requires multiset preservation (all frequencies accounted for) and WPL optimality — correctly relational.

### Topological Sort (Ch22)
Most DAGs admit multiple valid topological orderings. The spec requires `is_topological_order` (all edges respected) + distinctness + completeness. For the 3-vertex linear chain, the ordering is unique, but the spec correctly allows any valid ordering.

### Vertex Cover (Ch35)
As a 2-approximation algorithm, different edge-processing orders produce different valid covers. The spec requires `is_cover` + `binary` + `count ≤ 2·OPT`. For K₃, the test exhaustively enumerates all 4 valid covers out of 8 possible binary vectors.

### Partial Selection Sort (Ch09)
The permutation predicate is opaque (not directly computable by Z3), requiring a completeness lemma with count-based reasoning. The spec is mathematically precise (`sorted_prefix ∧ prefix_leq_suffix ∧ permutation` uniquely determines the result) but demands more proof effort than Quickselect's direct `result == select_spec s₀ k`.
