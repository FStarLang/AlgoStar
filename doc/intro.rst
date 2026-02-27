.. _Introduction:

############
Introduction
############

Motivation
----------

*Introduction to Algorithms* (CLRS) is the standard reference for
algorithms and data structures, covering dozens of algorithms with
prose correctness arguments and asymptotic complexity analyses. But
prose arguments can hide subtle bugs. Loop invariants are stated
informally. Complexity bounds are argued by hand with implicit
assumptions.

This project formalizes a substantial subset of the CLRS algorithms in
`F* <https://fstar-lang.org>`_ and its imperative DSL
`Pulse <https://fstar-lang.org/tutorial/pulse>`_. For each algorithm
we aim to provide:

1. **A pure functional specification** — a mathematical definition of
   what the algorithm should compute (e.g., ``sorted s /\ permutation s0 s``
   for sorting).

2. **A verified imperative implementation** — Pulse code that operates on
   mutable arrays and heap-allocated data structures, with a machine-checked
   proof that it satisfies the functional specification.

3. **A verified complexity bound** — a ghost cost counter threaded through
   the Pulse implementation, with a proof that the number of key operations
   is bounded by the claimed asymptotic complexity (e.g., at most
   *n(n−1)/2* comparisons for insertion sort).

Every theorem in this document has been mechanically verified by the F*
typechecker and the Z3 SMT solver, unless explicitly marked with
``admit``, ``assume``, or ``assume_``.

How This Project Was Developed
------------------------------

This project is a collaboration between a human author (Nikhil Swamy,
a principal researcher and the lead developer of F*) and an AI
assistant (GitHub Copilot, powered by Claude). The development process
was iterative:

**What the AI did well:**

- Generating first drafts of algorithm implementations in Pulse,
  including loop invariants and ghost state management.
- Writing boilerplate: permutation lemmas, sequence manipulation
  helpers, and arithmetic infrastructure.
- Systematic audit of unproven obligations across the codebase.
- Attempting proofs via long reasoning chains — trying multiple
  strategies, adding intermediate assertions, and adjusting SMT
  resource limits.

**What required human guidance:**

- **Existing corpus of examples**: Having an existing library of verified
  algorithms in F* and Pulse was crucial---insertion sort, merge sort,
  quicksort, all existing previously and were useful templates for new
  algorithms. 

- **Proof strategy**: Choosing the right invariant structure. The AI
  often proposed invariants that were too strong (making the inductive
  step unprovable) or too weak (insufficient for the postcondition).
  In this development, so far, the human has not provided any
  explicit invariant or proof step to the AI. 
- **Spec bug detection**: Several specifications contained subtle
  errors that made lemmas *false*, not just hard to prove. For
  example, a lexicographic ordering condition in RadixSort checked
  the wrong direction (lower digits instead of higher digits). This
  was detected by the AI after trying and failing to prove key lemmas
  for several iterations. On reporting this, the human encouraged the 
  AI to revise the definition and complete the proofs, which it did successfully.
- **Quantifier management**: F*'s SMT encoding struggles with
  alternating quantifiers (∃∀ patterns). The human guided the use of
  explicit witness construction, ``introduce exists`` / ``introduce
  forall`` notation, and tactics.
- **Complexity methodology**: The human suggested to prove complexity
  results by instrumenting the implementation with a ghost cost counter
  and proving a bound on the counter by writing invariants.
- **Architectural decisions**: Which algorithms to implement, how to
  structure modules, when to use pure F* vs. Pulse, and when to
  defer hard proofs as admits.
- **Prioritization**: After some attempts, the human suggested to 
  defer certain tasks as "stretch goals", including proofs involving
  amortized analysis and graph theoretic properties.

**Tools used:**

- `F* <https://fstar-lang.org>`_: Dependently typed language and proof
  assistant, for pure specifications and proofs.
- `Pulse <https://fstar-lang.org/tutorial/pulse>`_: F*'s DSL for
  verified imperative programming with separation logic.
- `Z3 <https://github.com/Z3Prover/z3>`_: SMT solver used by F* for
  automated proof discharge.
- `GitHub Copilot CLI <https://github.com/github/copilot-cli>`_: AI
  assistant for code generation, proof attempts, and documentation.

Results Overview
----------------

The project currently covers algorithms from 18 chapters of CLRS,
implemented across 186 F* source files totaling approximately 74,600
lines. The table below summarizes the status of each algorithm.

**Legend:**

- ✅ = fully proven (zero ``admit()``, ``assume()``, or ``assume_`` calls)
- ⚠️ = partially proven (admits remain; count and summary given)
- **Spec** = what the postcondition proves
- **Proof** = ✅ if all proof obligations discharged, else ⚠️ with admit count
- **Complexity** = "Linked" if ghost counters are threaded through the Pulse
  implementation; "Pure" if proven separately in F*; "—" if none

.. list-table:: Algorithm Status
   :header-rows: 1
   :widths: 4 18 6 18 18 14

   * - Ch
     - Algorithm
     - CLRS
     - Spec
     - Proof
     - Complexity
   * - 2
     - :ref:`Insertion Sort <Ch02_Sorting>`
     - §2.1
     - sorted ∧ permutation
     - ✅
     - ✅ Linked O(n²)
   * - 2
     - :ref:`Merge Sort <Ch02_Sorting>`
     - §2.3
     - sorted ∧ permutation
     - ✅
     - ✅ Pure O(n lg n)
   * - 4
     - :ref:`Binary Search <Ch04_DivideConquer>`
     - §2.3
     - found ⟹ index matches
     - ✅
     - ✅ Linked O(lg n)
   * - 4
     - :ref:`Kadane (Max Subarray) <Ch04_DivideConquer>`
     - §4.1
     - result = max contiguous sum
     - ✅
     - ✅ Linked O(n)
   * - 4
     - :ref:`Divide & Conquer (Max Sub.) <Ch04_DivideConquer>`
     - §4.1
     - result = max contiguous sum
     - ✅
     - —
   * - 6
     - :ref:`Heapsort <Ch06_Heapsort>`
     - §6.4
     - sorted ∧ permutation
     - ✅
     - ✅ Pure O(n lg n)
   * - 7
     - :ref:`Partition (Hoare) <Ch07_Quicksort>`
     - §7.1
     - elements partitioned ∧ perm
     - ✅
     - ✅ Linked O(n)
   * - 7
     - :ref:`Lomuto Partition <Ch07_Quicksort>`
     - §7.1
     - elements partitioned ∧ perm
     - ✅
     - —
   * - 7
     - :ref:`Quicksort <Ch07_Quicksort>`
     - §7.1
     - sorted ∧ permutation
     - ✅
     - ✅ Linked O(n²)
   * - 8
     - :ref:`Counting Sort <Ch08_LinearSorting>`
     - §8.2
     - sorted ∧ permutation
     - ✅
     - ✅ Pure O(n+k)
   * - 8
     - :ref:`Counting Sort (Stable) <Ch08_LinearSorting>`
     - §8.2
     - sorted ∧ stable ∧ perm
     - ✅
     - —
   * - 8
     - :ref:`Radix Sort <Ch08_LinearSorting>`
     - §8.3
     - sorted ∧ permutation
     - ⚠️ 3: stability proofs
     - ✅ Pure Θ(d(n+k))
   * - 8
     - :ref:`Bucket Sort <Ch08_LinearSorting>`
     - §8.4
     - sorted ∧ permutation
     - ✅
     - —
   * - 9
     - :ref:`Min / Max <Ch09_OrderStats>`
     - §9.1
     - result ∈ array ∧ is min/max
     - ✅
     - ✅ Linked O(n)
   * - 9
     - :ref:`Simultaneous Min-Max <Ch09_OrderStats>`
     - §9.1
     - min ∧ max of array
     - ✅
     - —
   * - 9
     - :ref:`Quickselect <Ch09_OrderStats>`
     - §9.2
     - k-th smallest at position k
     - ✅
     - ✅ Pure O(n²)
   * - 9
     - :ref:`Partial Selection Sort <Ch09_OrderStats>`
     - §9.2
     - first k sorted, k-th correct
     - ✅
     - ✅ Pure O(nk)
   * - 10
     - :ref:`Stack / Queue <Ch10_DataStructures>`
     - §10.1
     - ghost list matches contents
     - ✅
     - ✅ Pure O(1)
   * - 10
     - :ref:`Linked List <Ch10_DataStructures>`
     - §10.2
     - ghost list matches contents
     - ✅
     - —
   * - 10
     - :ref:`Doubly-Linked List <Ch10_DataStructures>`
     - §10.2
     - segment pred ∧ ghost list
     - ✅
     - ✅ Linked O(1)
   * - 11
     - :ref:`Hash Table (Chaining) <Ch11_HashTables>`
     - §11.2
     - key ↦ value lookup
     - ✅
     - ✅ Linked O(n)
   * - 12
     - :ref:`BST Search / Delete <Ch12_BST>`
     - §12.2–3
     - key set operations
     - ✅
     - ✅ Pure O(h)
   * - 12
     - :ref:`BST Insert <Ch12_BST>`
     - §12.3
     - key set updated
     - ✅
     - ✅ Pure O(h)
   * - 13
     - :ref:`Red-Black Tree <Ch13_RBTree>`
     - §13.1–4
     - Okasaki balance ∧ BST
     - ✅
     - ✅ Pure O(lg n)
   * - 15
     - :ref:`Rod Cutting <Ch15_DynamicProg>`
     - §15.1
     - optimal revenue
     - ✅
     - ✅ Linked O(n²)
   * - 15
     - :ref:`Ext. Rod Cutting <Ch15_DynamicProg>`
     - §15.1
     - optimal revenue ∧ valid cuts
     - ✅
     - ✅ Linked O(n²)
   * - 15
     - :ref:`LCS <Ch15_DynamicProg>`
     - §15.4
     - LCS length
     - ✅
     - ✅ Linked O(mn)
   * - 15
     - :ref:`Matrix Chain <Ch15_DynamicProg>`
     - §15.2
     - optimal parenthesization cost
     - ✅
     - ✅ Pure O(n³)
   * - 16
     - :ref:`Activity Selection <Ch16_Greedy>`
     - §16.1
     - greedy = optimal count
     - ✅
     - ✅ Linked O(n)
   * - 16
     - :ref:`Huffman Coding <Ch16_Greedy>`
     - §16.3
     - prefix-free tree construction
     - ⚠️ 3: assume_ (PQ distinctness)
     - ✅ Pure O(n lg n)
   * - 21
     - :ref:`Union-Find <Ch21_DisjointSets>`
     - §21.3
     - find/union maintain forest
     - ⚠️ 1: rank bound assume
     - ✅ Pure O(α(n))
   * - 22
     - :ref:`BFS (Queue) <Ch22_Graphs>`
     - §22.2
     - distances ∧ parent tree
     - ✅
     - ✅ Linked O(V²)
   * - 22
     - :ref:`DFS (Stack) <Ch22_Graphs>`
     - §22.3
     - timestamps ∧ classification
     - ⚠️ 1: white-path backward
     - ✅ Linked O(V²)
   * - 22
     - :ref:`Kahn Topological Sort <Ch22_Graphs>`
     - §22.4
     - valid topological order
     - ✅
     - ✅ Linked O(V²)
   * - 23
     - :ref:`Kruskal MST <Ch23_MST>`
     - §23.2
     - MST of graph
     - ⚠️ 2: forest axiom + acyclicity
     - ✅ Linked O(V·E)
   * - 23
     - :ref:`Prim MST <Ch23_MST>`
     - §23.2
     - MST of graph
     - ✅
     - ✅ Linked O(V²)
   * - 23
     - :ref:`MST Theory <Ch23_MST>`
     - §23.1
     - cut/cycle properties
     - ✅
     - —
   * - 24
     - :ref:`Bellman-Ford <Ch24_SSSP>`
     - §24.1
     - SSSP distances
     - ✅
     - ✅ Linked O(VE)
   * - 24
     - :ref:`Dijkstra <Ch24_SSSP>`
     - §24.3
     - SSSP distances
     - ✅
     - ✅ Linked O(V²)
   * - 25
     - :ref:`Floyd-Warshall <Ch25_APSP>`
     - §25.2
     - APSP distances
     - ✅
     - ✅ Linked O(n³)
   * - 26
     - Ford-Fulkerson (Max Flow)
     - §26.2
     - max flow ∧ valid flow
     - ⚠️ 2: duality/min-cut
     - ✅
   * - 28
     - :ref:`Matrix Multiply <Ch04_MatrixOps>`
     - §28 (App)
     - C = A · B
     - ✅
     - ✅ Linked O(n³)
   * - 28
     - :ref:`Strassen <Ch04_MatrixOps>`
     - §28 (App)
     - Strassen = standard mult
     - ✅
     - —
   * - 31
     - :ref:`GCD / Extended GCD <Ch31_NumberTheory>`
     - §31.2
     - gcd ∧ Bézout coefficients
     - ✅
     - ✅ Linked O(lg n)
   * - 31
     - :ref:`Modular Exponentiation <Ch31_NumberTheory>`
     - §31.6
     - result = b^e mod m
     - ✅
     - ✅ Linked O(lg e)
   * - 32
     - :ref:`Naive String Match <Ch32_StringMatch>`
     - §32.1
     - all match positions
     - ✅
     - ✅ Linked O(nm)
   * - 32
     - :ref:`KMP <Ch32_StringMatch>`
     - §32.4
     - all match positions
     - ✅
     - ✅ Linked O(n+m)
   * - 32
     - :ref:`Rabin-Karp <Ch32_StringMatch>`
     - §32.2
     - all match positions
     - ✅
     - ✅ Pure O(nm)
   * - 33
     - :ref:`Segment Intersection <Ch33_CompGeometry>`
     - §33.1
     - correct intersection test
     - ✅
     - ✅ Pure O(1)
   * - 35
     - :ref:`Vertex Cover (2-approx) <Ch35_Approximation>`
     - §35.1
     - cover ≤ 2 · OPT
     - ✅
     - ✅ Pure O(V+E)

Proof Gaps
----------

As of this writing, the project has **5 unproven ``admit()`` calls**,
**3 ``assume_()``**, **4 ``assume()``**, and **1 ``assume val``**
across **8 files** (total: 13 unproven obligations).
Of the 50 algorithms in the table, **44 have fully proven correctness**
(zero admits) and **42 have fully proven complexity bounds**.

The remaining unproven obligations fall into a few categories:

1. **Sorting stability** (Ch. 8, 3 admits): RadixSort multi-digit stability
   proofs involve ∃∀ quantifier patterns that challenge the SMT solver.

2. **Graph algorithms** (Ch. 22, 1 admit): The backward direction of the
   DFS white-path theorem in ``WhitePath.fst``.

3. **Greedy algorithms** (Ch. 16, 3 assume\_): Huffman priority queue
   distinctness invariants in the PQ extraction loop.

4. **MST** (Ch. 23, 1 assume val + 1 assume): Kruskal forest axiom and
   sorted-edges acyclicity preservation.

5. **Shortest paths** (Ch. 24, 1 admit): The ``sp_dist_k_stabilize``
   lemma in ``ShortestPath.Triangle.fst`` (pigeonhole + cycle removal).

6. **Network flow** (Ch. 26, 2 assume): Max-flow min-cut
   weak duality and min-cut existence.

7. **Disjoint sets** (Ch. 21, 1 assume): Rank bound preservation
   after path compression in ``UnionFind.Spec``.

Each chapter in this document notes any unproven obligations in its
scope.  Fully verified chapters have zero ``admit``, ``assume``, or
``assume_`` calls.

Reading Guide
-------------

This document is designed to be read alongside two other references:

1. **CLRS** (*Introduction to Algorithms*, 4th ed.): We reference CLRS
   sections by number (e.g., "§2.1") for the algorithm descriptions
   and informal correctness arguments. We do not reproduce CLRS content.

2. **Proof-oriented Programming in F*** (`PoP-in-FStar
   <https://fstar-lang.org/tutorial>`_): For background on F* syntax,
   refinement types, dependent types, Pulse, and separation logic.
   We cross-reference specific PoP chapters where relevant.

**What each chapter contains:**

- A brief description of the algorithm (referencing CLRS)
- The main correctness theorem (as verified F* code)
- The complexity theorem (as verified F* code)
- Key auxiliary definitions needed to understand the theorems
- A walkthrough of the proof techniques used
- Notes on what the SMT solver handles automatically and what required
  manual lemmas

**Conventions:**

- All code listings are extracted from verified ``.fst`` files.
  They are not hand-written examples — they are the actual verified code.
- ``sorted``, ``permutation``, etc. are pure F* predicates defined
  in each module.
- Pulse code uses ``#lang-pulse`` and separation logic assertions
  (``requires ... ensures ...`` with ``**`` for separating conjunction).
- Ghost state (erased at runtime) is used for specification values
  and cost counters.
