# AlgoStar

This repository contains verified implementations of algorithms and data
structures in [Pulse](https://github.com/FStarLang/pulse), a separation-logic
language embedded in [F\*](https://github.com/FStarLang/FStar).

All the code has been produced by agents driven by prompts and feedback on
specifications from humans. 

## AutoCLRS

This is an agent-generated implementation of algorithms and data structures from
Cormen, Leiserson, Rivest, and Stein's *Introduction to Algorithms* (CLRS)
textbook, available from [MIT
press](https://mitpress.mit.edu/books/introduction-algorithms-third-edition).

## Prerequisites

- **OCaml** (>= 4.14) with [opam](https://opam.ocaml.org/doc/Install.html)
- **Z3** (>= 4.8.5) — install via opam: `opam install z3` or your system package manager
- **GNU Make**, **Git**

## Getting Started

### 1. Clone the repository with submodules

```bash
git clone --recurse-submodules git@github.com:FStarLang/AutoCLRS.git
cd AutoCLRS
```

If you already cloned without `--recurse-submodules`:

```bash
git submodule update --init --recursive
```

### 2. Build F\* and Pulse

```bash
./setup.sh
```

This builds F\* and Pulse from the pinned submodule versions. It takes 10–20
minutes on first run. You can also build them individually:

```bash
./setup.sh fstar   # build only F*
./setup.sh pulse   # build only Pulse (requires F* already built)
```

### 3. Verify all chapters

```bash
make        # verify all chapters
make -j8    # parallel build (recommended)
make clean  # clean build artifacts
```

Each chapter can also be verified independently:

```bash
cd autoclrs/ch02-getting-started && make
```

## Repository Structure

| Directory | CLRS Chapters | Topics |
|-----------|--------------|--------|
| `autoclrs/ch02-getting-started/` | Ch 2 | Insertion Sort, Merge Sort |
| `autoclrs/ch04-divide-conquer/` | Ch 4 | Maximum Subarray |
| `autoclrs/ch06-heapsort/` | Ch 6 | Binary Heaps, Heapsort |
| `autoclrs/ch07-quicksort/` | Ch 7 | Quicksort, Lomuto/Hoare partition |
| `autoclrs/ch08-linear-sorting/` | Ch 8 | Counting Sort, Radix Sort |
| `autoclrs/ch09-order-statistics/` | Ch 9 | Randomized/Deterministic Select |
| `autoclrs/ch10-elementary-ds/` | Ch 10 | Stacks, Queues, Linked Lists |
| `autoclrs/ch11-hash-tables/` | Ch 11 | Chained Hash Tables |
| `autoclrs/ch12-bst/` | Ch 12 | Binary Search Trees |
| `autoclrs/ch13-rbtree/` | Ch 13 | Red-Black Trees |
| `autoclrs/ch15-dynamic-programming/` | Ch 15 | Rod Cutting, Matrix Chain, LCS, Knapsack |
| `autoclrs/ch16-greedy/` | Ch 16 | Activity Selection, Huffman Coding |
| `autoclrs/ch21-disjoint-sets/` | Ch 21 | Union-Find with union by rank + path compression |
| `autoclrs/ch22-elementary-graph/` | Ch 22 | BFS, DFS, Topological Sort |
| `autoclrs/ch23-mst/` | Ch 23 | Kruskal's MST |
| `autoclrs/ch24-sssp/` | Ch 24 | Bellman-Ford, Dijkstra, DAG Shortest Paths |
| `autoclrs/ch25-apsp/` | Ch 25 | Floyd-Warshall |
| `autoclrs/ch26-max-flow/` | Ch 26 | Edmonds-Karp Max Flow |
| `autoclrs/ch31-number-theory/` | Ch 31 | GCD, Modular Exponentiation, Miller-Rabin |
| `autoclrs/ch32-string-matching/` | Ch 32 | Naive, Rabin-Karp, KMP |
| `autoclrs/ch33-comp-geometry/` | Ch 33 | Convex Hull (Graham Scan) |
| `autoclrs/ch35-approximation/` | Ch 35 | Vertex Cover (2-approximation) |
| `autoclrs/common/` | — | Shared utilities |

## Documentation

Detailed per-algorithm documentation (specification reviews, correctness
properties, complexity results, and known gaps) is available in:

- **Per-algorithm reviews**: `autoclrs/<chapter>/<Module>.Review.md` files
- **Chapter READMEs**: `autoclrs/<chapter>/README.md`

