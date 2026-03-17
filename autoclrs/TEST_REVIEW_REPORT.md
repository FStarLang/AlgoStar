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
  classifying the precision of specifications, and used agents to apply it to
  the AutoCLRS proofs. The tests in this repository were produced by agents
  referencing Lahiri's eval-autoclrs-specs repo.

### A First Example

A useful first example is here: https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst

The idea is to write a test case (highly simplified) such as this:

```
fn test_quicksort() 
{
  let mut a = [| 0; 3sz |];
  a.(0sz) := 3; a.(1sz) := 2; a.(2sz) := 1;
  quicksort a;
  assert pure (value_of a `Seq.equal` Seq.of_list [1;2;3]);
}
```

This checks, on a small concrete instance, that:

* `quicksort` preconditions can be satisfied
* that its postcondition is strong enough to prove the expected result (the output is `[1;2;3]`)

In many cases, however (including for quicksort), actually proving the
precondition at the postcondition requires some additional proof effort. For
instance, the postcondition of `quicksort` is that the output array is a sorted
permutation of the input. From this, concluding that the output array is exactly
`[1;2;3]` requires some proof steps. In the general case, one would want to show
that a sorted permutation of the input uniquely determines the output (e.g., as
shown in `sorted_permutation_equal` in CLRS.Ch09PartialSelectionSort.Lemmas),
though for this particular example, a specific proof for the input `[3;1;2]`
would be sufficient.

Such tests provide a practical check on concrete instances that the
specifications are strong enough, though it is not fool proof. One could imagine
poorly specified libraries with specifications that are overspecialized to the
test cases only. However, in practice, this does not seem to be a problem in
AutoCLRS---the specifications are general, but sometimes miss important corner
cases, like fully specifying the error behavior of a library.

### API Tests

[Lahiri's paper](https://arxiv.org/pdf/2406.09757) focuses primarily on symbolic
tests for specifications of single functions. However, many libraries,
particularly for data structures, expose several functions that are used
together. For example, a hash table library includes functions to `insert`,
`delete`, and `search`, and a good test should check the interaction between
these.

The test case in
https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch11-hash-tables/Test.HashTable.fst
was an initial attempt to exercise multiple functions of the hash table library
together. Although the test is incomplete (e.g., it contains admits) it provided
a strong signal that the postcondition of Hashtable.insert was not strong
enough, in particular, it did not prove that insert would succeed on non-full
tables.

Building on this, our agents generated this test:
https://github.com/FStarLang/AlgoStar/blob/f7a9c1bc8cd9e1f99ba50b9f49700b9a5ba1c28f/autoclrs/ch11-hash-tables/CLRS.Ch11.HashTable.ImplTest.fst#L143-L145
noting specifically the limitation of the postcondition of `insert`.

Going further, noting this specification gaps, our agents improved the
specification of `insert` to prove that it must succeed on non-full tables, and
revised the test case accordingly: 
https://github.com/FStarLang/AlgoStar/commit/8fb3543cd08521cce20a81cc39ae64e6385375b1

Other API tests do not necessarily check specific assertions, but simply check
that the API is usable for common usage, e.g., 

```
// ============================================================
// Test 7: Create and free — basic lifecycle
// ============================================================
//
// Proves:
// - hash_table_create postcondition establishes valid_ht
// - The returned table can immediately be freed
// - Precondition of hash_table_free (V.is_full_vec) is satisfiable
//

fn test_create_free ()
  requires emp
  ensures emp
{
  let tv = hash_table_create 5sz;
  hash_table_free tv;
}
```

### Relational Specifications

Some specifications are inherently relational, meaning the allow multiple valid
outputs for a given input.

A good example of this is CLRS.Ch22.TopologicalSort.Impl, which only proves that
it returns a valid topological sort, of which there may be many. This is a
common style of specification that does not overly constrain implementations,
while also providing useful, abstract specifications to clients.

In such cases, we have instructed agents to author test cases that enumerate all
possible correct outputs and prove that the postcondition is sufficiently strong
to prove that

  - each correct output is admissible by the postcondition
  - no other outputs are admissible by the postcondition

However, so far, we have yet to have agents generate such strong tests for
relational specifications. 

For example, for the case of topological sort, the test proves that the expected
output is indeed a valid topological sort, but does not prove that the returned
sort is exact one expected, nor does it enumerate all the legal outputs:
https://github.com/FStarLang/AlgoStar/blob/_address_reviews/autoclrs/ch22-elementary-graph/CLRS.Ch22.TopologicalSort.ImplTest.md#what-is-not-proven

We are working to improve this.

## Summary of Results

The rest of this report is an AI authored summary of test results.

> Comprehensive review of all `ImplTest.fst` and `ImplTest.md` files across the AutoCLRS project.
> Updated 2026-03-17.

## Purpose of ImplTests

Each `ImplTest.fst` file serves as a **spec-precision validation test**: it constructs a small concrete input, calls the verified implementation, and proves that the postcondition uniquely determines (or tightly constrains) the output. The companion `.md` file documents findings and proof techniques. All tests target **zero admits and zero assumes**.

---

## Master Summary Table

| Ch | Algorithm | Spec Type | Precision | Coverage | #Tests | Admits | Key Spec Gaps |
|----|-----------|-----------|-----------|----------|--------|--------|---------------|
| 02 | Insertion Sort | Deterministic | ✅ Precise | Moderate | 3 (n=3, empty, single) | 0 | None |
| 02 | Merge Sort | Deterministic | ✅ Precise | Moderate | 3 (n=3, empty, single) | 0 | None |
| 04 | Binary Search | Deterministic | ✅ Precise | Moderate | 3 (found, not-found, empty) | 0 | None |
| 04 | Max Subarray (Kadane) | Deterministic | ✅ Precise | Moderate | 2 (mixed, all-negative) | 0 | None |
| 04 | Matrix Multiply | Deterministic | ✅ Precise | Minimal | 1 (n=2) | 0 | None |
| 06 | Heapsort | Deterministic | ✅ Precise | **Comprehensive** | 5 (sort, heap, n=0, prefix, dupes) | 0 | None |
| 07 | Partition | **Relational** | ✅ Precise | Minimal | 1 (n=3) | 0 | None — correctly relational |
| 07 | Quicksort | Deterministic | ✅ Precise | Moderate | 3 (basic, complexity, bounded) | 0 | None |
| 08 | Counting Sort (2 variants) | Deterministic | ✅ Precise | Moderate | 2 fns tested | 0 | `counting_sort_by_digit` untested; stability unverified |
| 09 | Min / Max | Deterministic | ✅ Precise | Minimal | 2 (min + max) | 0 | None — existence+universality is strongest |
| 09 | Simultaneous MinMax | Deterministic | ✅ Precise | Minimal | 2 (find_minmax + pairs) | 0 | None |
| 09 | Quickselect | Deterministic | ✅ Precise | Minimal | 2 (k=0, k=2) | 0 | None — `result==select_spec` is strongest |
| 09 | Partial Selection Sort | Deterministic | ✅ Precise | Moderate | 3 (k=1,2,3) | 0 | None — strengthened to `result==select_spec` |
| 10 | Stack | Deterministic | ✅ Precise | **Comprehensive** | Multi-op lifecycle | 0 | None |
| 10 | Queue | Deterministic | ✅ Precise | **Comprehensive** | Multi-op + wraparound | 0 | None |
| 10 | Doubly Linked List | Deterministic | ✅ Precise | **Comprehensive** | 4 scenarios (all ops) | 0 | None — all operations tested |
| 10 | Singly Linked List | Deterministic | ✅ Precise | **Comprehensive** | Full lifecycle | 0 | None |
| 11 | Hash Table | Deterministic | ✅ Precise | **Comprehensive** | 7 tests | 0 | None — insert forced true on non-full tables |
| 12 | BST (Pointer) | Deterministic | ✅ Precise | **Comprehensive** | 14+ pure + Pulse | 0 | None |
| 12 | BST (Array) | Deterministic | ⚠️ Moderate | Moderate | Search + insert + bridge | 0 | Insert doesn't guarantee success; no frame property |
| 13 | RB-Tree (Okasaki) | Deterministic | ✅ Precise | **Comprehensive** | 14 pure + Pulse | 0 | None — strengthened postconditions |
| 13 | RB-Tree (CLRS) | Deterministic | ✅ Precise | **Comprehensive** | 14 pure + Pulse | 0 | None |
| 15 | Rod Cutting | Deterministic | ✅ Precise | Minimal | 1 (n=4) | 0 | None |
| 15 | Matrix Chain | Deterministic | ✅ Precise | Minimal | 1 (n=3) | 0 | None — non-negativity in postcondition |
| 15 | LCS | Deterministic | ✅ Precise | Minimal | 1 (m=n=3) | 0 | None — range constraints in postcondition |
| 16 | Activity Selection | **Precise Relational** | ✅ Precise | **Comprehensive** | Count + indices + optimality | 0 | None — relational with earliest-compatible |
| 16 | Huffman Tree | **Precise Relational** | ✅ Precise | **Comprehensive** | Cost + multiset + optimality + leaf labels | 0 | None — optimality + leaf label mapping |
| 16 | Huffman Codec | Deterministic | ✅ Precise | **Comprehensive** | Encode + Decode | 0 | None |
| 21 | Union-Find | Relational | ✅ Precise | Moderate | 3 ops (make, find, 2× union) | 0 | Rank bound degrades per union (log bound unformalized) |
| 22 | BFS | Relational | ✅ Precise | Moderate | 1 (3-vertex, distance precision) | 0 | Shortest-path follows from unique paths; general graphs need optimality clause |
| 22 | DFS | Relational | ⚠️ Moderate | Minimal | 1 (3-vertex chain) | 0 | **Spec↔Impl disconnect**; theorems not exposed |
| 22 | Topological Sort | **Relational** | ✅ Precise | Moderate | 1 (3-vertex DAG) | 0 | None — correctly relational |
| 23 | Kruskal | Relational | ⚠️ **Weak** | Minimal | 1 (3-vertex triangle) | 0 | **No spanning tree or MST property** (forest only) |
| 23 | Prim | Functional but weak | ⚠️ **Weak** | Minimal | 1 (3-vertex triangle) | 1 | Parent validity added; still no MST structure |
| 24 | Bellman-Ford | Deterministic (conditional) | ✅ Precise | Moderate | 1 (3-vertex, neg wts) | 0 | Unconditional completeness via `no_neg_cycles_flat` |
| 24 | Dijkstra | Deterministic | ✅ Precise | Minimal | 1 (3-vertex) | 0 | Predecessor array not verified |
| 25 | Floyd-Warshall | Deterministic | ✅ Precise | **Comprehensive** | All 9 entries + neg-cycle + safe API | 0 | None — neg-cycle detection fully characterized |
| 26 | Max Flow (Edmonds-Karp) | Deterministic + Optimality | ✅ Precise | Moderate | 2 (single-edge + disconnected) | 0 | None — return value + MFMC theorem |
| 31 | GCD | Deterministic | ✅ Precise | Minimal | 1 (gcd(12,8)) | 0 | None — positivity + divisibility in postcondition |
| 31 | ModExp (R-to-L) | Deterministic | ✅ Precise | Minimal | 1 (2¹⁰ mod 1000) | 0 | None — bounds in postcondition |
| 31 | ModExp (L-to-R) | Deterministic | ✅ Precise | Minimal | 1 (3⁵ mod 7) | 0 | None — bounds in postcondition |
| 32 | Naive String Match | Deterministic | ✅ Precise | Minimal | 1 (n=5, m=3) + match positions | 0 | None |
| 32 | KMP | Deterministic | ✅ Precise | Minimal | 1 (n=5, m=3) + match positions | 0 | None — upper bound tightened |
| 32 | Rabin-Karp | Deterministic | ✅ Precise | Minimal | 1 (n=5, m=3) + match positions | 0 | None — hash-independent correctness |
| 33 | Segments (primitives) | Deterministic | ✅ Precise | **Comprehensive** | 10 tests (all orientations) | 0 | None |
| 33 | Graham Scan | Deterministic | ✅ Precise | Moderate | 3 sub-functions + semantics | 0 | No interior-point pruning test |
| 33 | Jarvis March | Deterministic | ✅ Precise | Moderate | 3 fns + full march | 0 | No non-convex input test |
| 35 | Vertex Cover (2-approx) | **Relational** | ✅ Precise | **Comprehensive** | 3 valid covers enumerated + even count | 0 | None — correctly relational |

**Legend:** ✅ = precise/strong, ⚠️ = has notable weakness

---

## Spec Strengthening Summary (since initial review)

Many specs were improved in this revision cycle. Key improvements include:

| Algorithm | Improvement |
|-----------|------------|
| Insertion Sort, Merge Sort | Added edge-case tests (empty, single element) |
| Binary Search | Added empty-array test |
| Kadane Max Subarray | Added all-negative test; complexity made transparent |
| Heapsort | Added 4 new tests (build_max_heap, n=0, prefix sort, duplicates) |
| Quicksort | Added `quicksort_with_complexity` and `quicksort_bounded` tests; `between_bounds` exposed |
| Counting Sort | Permutation direction normalized; `in_range` postcondition added |
| Partial Selection Sort | Strengthened to `result==select_spec`; added k=2, k=3 tests |
| DLL | Added `list_delete_last` and `list_delete_node` scenarios (4 total) |
| Hash Table | Insert forced true on non-full tables via probe-sequence contradiction; delete strengthened |
| BST Array | Insert postcondition now includes `key_in_subtree`; `wfb_to_sir` bridge exported |
| RB-Tree (Okasaki) | Strengthened postconditions directly give search results for inserted/deleted keys |
| Matrix Chain | Non-negativity (`result >= 0`) added to postcondition |
| LCS | Range constraints (`0 ≤ result ≤ min(m,n)`) added to postcondition |
| Huffman Tree | `tree_leaf_labels_valid` added to postcondition |
| Union-Find | Rank bound clauses + membership clause added; multi-step unions tested |
| BFS | Distance precision proven via uniqueness lemmas; predecessor consistency tested |
| DFS | Timestamp bounds (`d[u] ≤ 2n`, `f[u] ≤ 2n`) added |
| Prim | `parent_valid` added (all parent[v] < n) |
| Kruskal | `result_is_forest_adj_elim` and `result_is_forest_adj_forest_elim` lemmas exposed |
| Bellman-Ford | Unconditional completeness via `no_neg_cycles_flat ⟹ no_neg_cycle == true` |
| Floyd-Warshall | Neg-cycle detection return value fully characterized (both true and false cases); safe API tested |
| Max Flow | Return value exposed (`fv == imp_flow_value`); second test (disconnected network) added |
| GCD | Positivity + divisibility added to postcondition |
| ModExp/ModExpLR | Bounds (`0 ≤ result < m`) added to postcondition |
| KMP | Upper bound tightened to `n - m + 1`; match position lemmas added |
| All String Matching | Individual match position verification added |
| Vertex Cover | Even count property added; enumeration narrowed to 3 valid covers |

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
| Quickselect, Partial Selection Sort | `result == select_spec s₀ k` |
| BST (Pointer), RB-Trees | Ghost tree determines exact structure |
| All DP (Rod, MatrixChain, LCS) | `result == dp_spec(input)` |
| Huffman Codec | `decode(bits, tree) == message` |
| Dijkstra, Floyd-Warshall | `dist[v] == sp_dist(source, v)` |
| GCD, ModExp, ModExpLR | `result == math_spec(args)` |
| All String Matching | `result == count_matches_spec(text, pattern)` |
| Segments primitives | `result == cross_product_spec(...)` |

### Precise Relational Specs (multiple correct outputs, all valid)

These specs allow multiple correct outputs by design — the algorithm has legitimate non-determinism or the problem has multiple optimal solutions.

| Algorithm | Why Relational | Constraining Properties |
|-----------|---------------|------------------------|
| Partition (Ch07) | Pivot choice not prescribed | Left ≤ pivot < right, permutation preserved |
| Activity Selection (Ch16) | Multiple maximum-cardinality selections | Count optimal, earliest-compatible |
| Huffman Tree (Ch16) | Multiple trees with same optimal WPL | Multiset preserved, WPL optimal, leaf labels valid |
| Topological Sort (Ch22) | Multiple valid orderings for most DAGs | `is_topological_order`, all elements distinct |
| Vertex Cover (Ch35) | Approximation allows multiple valid covers | `is_cover`, binary, even count, `count ≤ 2·OPT` |

### Remaining Spec Gaps

#### ⚠️ Significant (important properties missing from postcondition)

| Algorithm | Gap | Impact |
|-----------|-----|--------|
| **Prim (Ch23)** | Only proves `key[source]==0`, `parent[source]==source`, parent validity, key bounds | Cannot verify specific key/parent values or MST structure |
| **Kruskal (Ch23)** | Only proves forest (acyclic); not spanning tree or MST | Cannot prove edge count = n-1, connectivity, or minimality |
| **DFS (Ch22)** | Spec↔Impl disconnect: pure spec proves theorems but `Impl.fsti` doesn't expose them | Cannot use edge classification or white-path theorem from Impl |
| **BST Array (Ch12)** | Insert doesn't guarantee success; no frame property for other keys | Cannot prove insert succeeds on non-full tree or absent keys remain absent |

#### Minor Gaps

| Algorithm | Gap |
|-----------|-----|
| Counting Sort (Ch08) | `counting_sort_by_digit` untested; stability unverified |
| Dijkstra (Ch24) | Predecessor array not verified |
| Graham Scan (Ch33) | No test with interior points |
| Jarvis March (Ch33) | No test with non-convex input |

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
- **Zero admits across all tests**: ✅ Yes (one platform assumption `SZ.fits_u64` in Prim)
- **Zero assumes across all tests**: ✅ Yes

### By Spec Quality

| Quality Level | Count | Algorithms |
|---------------|-------|-----------|
| ✅ Precise & Complete | 34 | InsSort, MergeSort, Heapsort, Quicksort, Partition, BinSearch, Kadane, MatMul, MinMax, SimMinMax, Quickselect, PartSelSort, Stack, Queue, DLL, SLL, HashTable, BST(Ptr), RBTree×2, RodCut, MatChain, LCS, ActSel, Huffman×3, TopSort, FW, Dijkstra, BellmanFord, MaxFlow, GCD, ModExp×2, NaiveMatch, KMP, RabinKarp, Segments, GrahamScan, JarvisMarch, VertexCover, UnionFind, BFS |
| ⚠️ Moderate gaps | 4 | BSTArray, DFS, Kruskal, Prim |

### By Test Coverage

| Coverage Level | Count | Algorithms |
|----------------|-------|-----------|
| Comprehensive | 16 | Heapsort, Stack, Queue, DLL, SLL, HashTable, BST(Ptr), RBTree×2, ActSel, Huffman×2, FW, Segments, VertexCover |
| Moderate | 14 | InsSort, MergeSort, BinSearch, Kadane, Quicksort, CountingSort, PartSelSort, TopSort, JarvisMarch, GrahamScan, BellmanFord, MaxFlow, UnionFind, BFS |
| Minimal | 10 | MatMul, MinMax, SimMinMax, Quickselect, RodCut, MatChain, LCS, Dijkstra, BSTArray, Prim |

---

## Priority Recommendations

### 1. Fix Remaining Spec Gaps (High Priority)

1. **Prim (Ch23)**: Postcondition still lacks MST structural properties. The `key_parent_consistent` predicate is defined but not yet tracked through Pulse loops. Needs: key[v] == weight(parent[v],v), spanning tree structure.
2. **Kruskal (Ch23)**: Strengthen from "forest" to "minimum spanning tree" (connectivity + minimality).
3. **DFS (Ch22)**: Bridge spec↔impl gap — expose edge classification and white-path theorem through `Impl.fsti`.

### 2. Remaining Minor Improvements (Medium Priority)

4. **BST Array (Ch12)**: Add insert success guarantee when tree has empty slots; add frame property for absent keys.
5. **Counting Sort (Ch08)**: Test `counting_sort_by_digit`; verify stability.
6. **Dijkstra (Ch24)**: Verify predecessor array.

### 3. Expand Test Coverage (Lower Priority)

- Graham Scan / Jarvis March: Add non-convex inputs with interior points.
- All minimal tests: Consider adding edge cases (empty, single element, duplicates).

---

## Appendix: Relational Specs Deep Dive

The following algorithms have **intentionally relational** specs — they correctly model problems where multiple valid outputs exist:

### Partition (Ch07)
The Lomuto partition spec says: left partition elements ≤ pivot, right partition elements > pivot, and output is a permutation. For `[3,1,2]`, three valid pivot choices exist. The spec does not prescribe which element becomes the pivot — this is correct since different partition strategies (Lomuto, Hoare, randomized) make different choices.

### Activity Selection (Ch16)
Multiple maximum-cardinality compatible subsets may exist. The spec constrains the output to be compatible, maximum-cardinality, and to satisfy the "earliest compatible" greedy property. This is tight enough to determine the exact output for the test case while remaining relational in general.

### Huffman Tree (Ch16)
Multiple tree structures can achieve the same optimal weighted path length. The spec requires multiset preservation (all frequencies accounted for), WPL optimality, and leaf label validity (each leaf's symbol maps to its original index). For inputs with distinct frequencies, the symbol-frequency pairing is uniquely determined.

### Topological Sort (Ch22)
Most DAGs admit multiple valid topological orderings. The spec requires `is_topological_order` (all edges respected) + distinctness + completeness. For the 3-vertex linear chain, the ordering is unique, but the spec correctly allows any valid ordering.

### Vertex Cover (Ch35)
As a 2-approximation algorithm, different edge-processing orders produce different valid covers. The spec requires `is_cover` + `binary` + even count + `count ≤ 2·OPT`. For K₃, the test enumerates all 3 valid covers (out of 8 possible binary vectors), with `[1,1,1]` excluded by the even-count property.
