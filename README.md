# AutoCLRS

Verified implementations of algorithms from *Introduction to Algorithms* (CLRS)
in [Pulse](https://github.com/FStarLang/pulse), a separation-logic language
embedded in [F\*](https://github.com/FStarLang/FStar).

Every algorithm is proven memory-safe and many carry full functional-correctness
specifications — all without admits or assumes. Zero admits across ~18,000 lines
of verified code. 32 complexity proof files cover 21 of 23 chapters.

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
| ch04 | Binary Search, Maximum Subarray | found ⟺ key ∈ array | O(log n), O(n) |
| ch06 | Heapsort | sorted ∧ permutation | O(n log n) |
| ch07 | Quicksort, Partition | sorted ∧ permutation | O(n²) worst, O(n) partition |
| ch08 | Counting Sort, Radix Sort (d=1) | sorted ∧ permutation | Θ(n+k) |
| ch09 | Min/Max, Select (partial sort) | k-th smallest element | O(nk) |
| ch10 | Stack, Queue, Linked List | list abstraction | O(1) push/pop, O(n) search |
| ch11 | Hash Table (open addressing) | functional map spec | O(n) worst case |
| ch12 | Binary Search Tree | key found ⟹ key at index | O(h) search |
| ch13 | Red-Black Tree ⚠ | ⚠ no RB invariants | — |
| ch15 | Rod Cutting, Matrix Chain, LCS | result == optimal_spec | O(n²), O(n³), O(mn) |
| ch16 | Activity Selection, Huffman ⚠ | greedy choice property | O(n log n) |
| ch21 | Union-Find (path compression) | find returns root | O(n) find, O(1) union |
| ch22 | BFS, DFS, Topological Sort | distance soundness, reachability | O(V²) |
| ch23 | Kruskal, Prim | valid endpoints only | O(V³), O(V²) |
| ch24 | Bellman-Ford, Dijkstra | triangle inequality (post-check) | O(V³), O(V²) |
| ch25 | Floyd-Warshall | result == fw_spec | O(n³) with ghost ticks |
| ch26 | Max Flow ⚠ | ⚠ returns zero flow | — |
| ch28 | Matrix Multiply | C == A × B (dot product) | O(n³) |
| ch31 | GCD, Modular Exponentiation | gcd_spec, modexp_spec | O(log b), O(log e) |
| ch32 | Naive, Rabin-Karp, KMP | match count == spec | O(nm), O(nm), O(n+m) |
| ch33 | Segment Intersection | cross product spec | O(1) |
| ch35 | 2-Approximation Vertex Cover | valid cover | O(V²) |

⚠ = Known limitations, see RESEARCH_DOC.md for details

## Functional Correctness Highlights

- **Sorting** (InsertionSort, MergeSort, Heapsort, Quicksort, CountingSort): `sorted ∧ permutation`
- **DP** (Rod Cutting, Matrix Chain, LCS): `result == optimal_spec(input)`
- **Floyd-Warshall**: `result == fw_outer(input)`
- **String Matching** (Naive, Rabin-Karp, KMP): match count equals pure spec
- **Binary Search**: found ⟺ key exists in sorted array
- **Matrix Multiply**: `C[i][j] == Σ_k A[i][k] · B[k][j]`
- **GCD**: `result == gcd_spec(a, b)` with O(log b) via Lamé's theorem
- **BFS**: distance soundness — `reachable_in(source, v, dist[v])`

## Known Limitations

- **RBTree (Ch13)**: Array-backed BST without RB invariants, fixup, or correct insert position
- **MaxFlow (Ch26)**: Initializes flow to zero; does not implement augmenting path search
- **Huffman (Ch16)**: Computes cost only; no tree construction or optimality proof
- **Select (Ch09)**: Uses O(nk) partial sort; CLRS RANDOMIZED-SELECT is O(n) expected
- **RadixSort (Ch08)**: Single-digit (d=1) only; wraps counting sort
- **Bellman-Ford/Dijkstra (Ch24)**: Triangle inequality proved via post-verification pass, not from algorithm invariants
- **Kruskal/Prim (Ch23)**: Prove valid endpoints only; no MST property (cut property, spanning tree)

See `RESEARCH_DOC.md` for comprehensive audit and `PROGRESS_PLAN.md` for improvement roadmap.
