# AutoCLRS

Verified implementations of algorithms from *Introduction to Algorithms* (CLRS)
in [Pulse](https://github.com/FStarLang/pulse), a separation-logic language
embedded in [F\*](https://github.com/FStarLang/FStar).

Every algorithm is proven memory-safe and many carry full functional-correctness
specifications — all without admits or assumes.

## Building

Requires F\* and Pulse to be installed (expected at `../pulse` relative to this repo).

```bash
make        # verify all chapters
make -j8    # parallel build
make clean  # clean build artifacts
```

## Chapters

| Chapter | Algorithms |
|---------|-----------|
| ch02 | Insertion Sort, Merge Sort (with permutation + sorted proofs) |
| ch04 | Binary Search (3 patterns), Maximum Subarray (Kadane's) |
| ch06 | Heapsort |
| ch07 | Quicksort |
| ch08 | Counting Sort, Radix Sort, Bucket Sort |
| ch09 | Min/Max, Select (order statistics) |
| ch10 | Stack, Queue, Linked List (with Vec/Box heap allocation) |
| ch11 | Hash Table (open addressing, functional map abstraction) |
| ch12 | Binary Search Tree |
| ch15 | Rod Cutting, Matrix Chain Multiplication, LCS |
| ch16 | Activity Selection, Huffman Coding |
| ch21 | Union-Find (disjoint sets) |
| ch22 | DFS, Topological Sort (Kahn's algorithm) |
| ch23 | Prim's MST |
| ch24 | Bellman-Ford, Dijkstra |
| ch25 | Floyd-Warshall |
| ch26 | Max Flow (Ford-Fulkerson / Edmonds-Karp) |
| ch28 | Matrix Multiply |
| ch31 | GCD, Modular Exponentiation |
| ch32 | Naive String Match, Rabin-Karp, KMP |
| ch33 | Segment Intersection |
| ch35 | 2-Approximation Vertex Cover |

## Functional Correctness Highlights

- **Merge Sort**: result is a permutation of the input and is sorted
- **Hash Table**: operations abstract to a pure map
- **String Matching** (Naive, Rabin-Karp, KMP): proven match-count correctness
- **Rod Cutting**: optimal revenue specification
- **LCS**: DP table correctness via `lcs_length` spec
- **BST Search**: returned index maps to the search key
- **Vertex Cover**: every edge has at least one endpoint in the cover
- **Bellman-Ford / Dijkstra**: `dist[source] ≤ 0` invariant
- **DFS**: source vertex is always visited
