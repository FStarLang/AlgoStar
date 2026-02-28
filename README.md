# AutoCLRS

Verified implementations of algorithms from *Introduction to Algorithms* (CLRS)
in [Pulse](https://github.com/FStarLang/pulse), a separation-logic language
embedded in [F\*](https://github.com/FStarLang/FStar).

Every algorithm is proven memory-safe and many carry full functional-correctness
specifications. 163 files are fully verified with zero admits (~51,500 lines).
14 files have 45 remaining unproven obligations (~7,800 lines).
32 complexity proof files cover 21 of 23 chapters.

## Building

Requires F\* and Pulse to be installed (expected at `../pulse` relative to this repo).

```bash
make        # verify all chapters
make -j8    # parallel build
make clean  # clean build artifacts
```

## Chapters

| Chapter | Algorithms | Functional Correctness | Complexity Proof |
|---------|-----------|----------------------|-----------------|
| ch02 | Insertion Sort, Merge Sort | sorted ∧ permutation | O(n²), O(n log n) |
| ch04 | Binary Search, Maximum Subarray, Matrix Multiply, Strassen | found ⟺ key ∈ array, C == A × B, Strassen == standard | O(log n), O(n), O(n³), O(n^{lg 7}) |
| ch06 | Heapsort | sorted ∧ permutation | O(n log n) |
| ch07 | Quicksort, Partition | sorted ∧ permutation | O(n²) worst, O(n) partition |
| ch08 | Counting Sort, Counting Sort (Stable), Radix Sort (d=1), Bucket Sort | sorted ∧ permutation | Θ(n+k) |
| ch09 | Min/Max, Select, **Quickselect** | k-th smallest, partition ordering | O(nk), O(n²) worst |
| ch10 | Stack, Queue, Linked List | list abstraction | O(1) push/pop, O(n) search |
| ch11 | Hash Table (open addressing) | functional map spec | O(n) worst case |
| ch12 | Binary Search Tree | key found ⟹ key at index | O(h) search |
| ch13 | Red-Black Tree | Okasaki balance ∧ BST ∧ Thm 13.1 ∧ delete¹ | O(lg n) |
| ch15 | Rod Cutting, Matrix Chain, LCS | result == optimal_spec | O(n²), O(n³), O(mn) |
| ch16 | Activity Selection, Huffman, **Huffman.Spec** | greedy choice, CLRS Eq 16.4 | O(n log n) |
| ch21 | Union-Find (path compression) | find returns root | O(n) find, O(1) union |
| ch22 | BFS, DFS, Topological Sort | distance soundness, reachability | O(V²) |
| ch23 | Kruskal, Prim | valid endpoints only | O(V³), O(V²) |
| ch24 | Bellman-Ford, Dijkstra, **Dijkstra.Correctness** | dist[v] = δ(s,v) proven | O(V³), O(V²) |
| ch25 | Floyd-Warshall | result == fw_spec | O(n³) with ghost ticks |
| ch26 | Max Flow ⚠ | ⚠ returns zero flow | — |
| ch31 | GCD, Extended GCD, Modular Exponentiation | gcd_spec, Bézout's identity, modexp_spec | O(log b), O(log e) |
| ch32 | Naive, Rabin-Karp, KMP | match count == spec | O(nm), O(nm), O(n+m) amortized |
| ch33 | Segment Intersection | cross product spec | O(1) |
| ch35 | 2-Approximation Vertex Cover | valid cover | O(V²) |

⚠ = Known limitations, see RESEARCH_DOC.md for details
¹ = `delete_is_rbtree` admitted (see Known Limitations)

## Functional Correctness Highlights

- **Sorting** (InsertionSort, MergeSort, Heapsort, Quicksort, CountingSort, BucketSort): `sorted ∧ permutation`
- **DP** (Rod Cutting, Matrix Chain, LCS): `result == optimal_spec(input)`
- **Floyd-Warshall**: `result == fw_outer(input)`
- **String Matching** (Naive, Rabin-Karp, KMP): match count equals pure spec
- **Binary Search**: found ⟺ key exists in sorted array
- **Matrix Multiply**: `C[i][j] == Σ_k A[i][k] · B[k][j]`; Strassen == standard multiply
- **GCD**: `result == gcd_spec(a, b)` with O(log b) via Lamé's theorem
- **BFS**: distance soundness — `reachable_in(source, v, dist[v])`

## Known Limitations

- **MaxFlow (Ch26)**: Initializes flow to zero; does not implement augmenting path search
- **Huffman (Ch16)**: Imperative Huffman.Complete has 0 admits; Huffman.Spec uses 4 `assume` axioms for greedy-choice/optimal-substructure (CLRS Lemma 16.2–16.3)
- **Select (Ch09)**: New Quickselect (CLRS §9.2) with partition ordering; old O(nk) selection sort kept for comparison
- **RadixSort (Ch08)**: Multi-digit radix sort has 10 admits in stability proofs; single-digit (d=1) fully verified
- **Kruskal/Prim (Ch23)**: Kruskal is actively being worked on; Prim proves key bounds only, no full MST property
- **DFS theorems (Ch22)**: DFS.Spec (5 admits) and DFS.WhitePath (3 admits) for parenthesis/white-path theorems remain open
- **RB-Tree delete (Ch13)**: `delete_is_rbtree` is admitted — the internal color-dependent invariant for Kahrs-style `del` is complex; membership and BST preservation are fully proven

See `RESEARCH_DOC.md` for comprehensive audit and `PROGRESS_PLAN.md` for improvement roadmap.
