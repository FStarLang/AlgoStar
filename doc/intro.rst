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
implemented across 174 F* source files totaling approximately 54,000
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
     - Insertion Sort
     - §2.1
     - sorted ∧ permutation
     - ✅
     - ✅ Linked O(n²)
   * - 2
     - Merge Sort
     - §2.3
     - sorted ∧ permutation
     - ✅
     - ✅ Pure O(n lg n)
   * - 4
     - Binary Search
     - §2.3
     - found ⟹ index matches
     - ✅
     - ✅ Linked O(lg n)
   * - 4
     - Kadane (Max Subarray)
     - §4.1
     - result = max contiguous sum
     - ✅
     - ✅ Linked O(n)
   * - 4
     - Divide & Conquer (Max Sub.)
     - §4.1
     - result = max contiguous sum
     - ✅
     - —
   * - 6
     - Heapsort
     - §6.4
     - sorted ∧ permutation
     - ✅
     - ✅ Pure O(n lg n)
   * - 7
     - Partition (Hoare)
     - §7.1
     - elements partitioned ∧ perm
     - ✅
     - ✅ Linked O(n)
   * - 7
     - Lomuto Partition
     - §7.1
     - elements partitioned ∧ perm
     - ✅
     - —
   * - 7
     - Quicksort
     - §7.1
     - sorted ∧ permutation
     - ✅
     - ✅ Linked O(n²)
   * - 8
     - Counting Sort
     - §8.2
     - sorted ∧ permutation
     - ✅
     - ✅ Pure O(n+k)
   * - 8
     - Counting Sort (Stable)
     - §8.2
     - sorted ∧ stable ∧ perm
     - ✅
     - —
   * - 8
     - Radix Sort
     - §8.3
     - sorted ∧ permutation
     - ⚠️ 10: stability proofs
     - ✅ Pure Θ(d(n+k))
   * - 8
     - Bucket Sort
     - §8.4
     - sorted ∧ permutation
     - ⚠️ 1: concat sorted buckets
     - —
   * - 9
     - Min / Max
     - §9.1
     - result ∈ array ∧ is min/max
     - ✅
     - ✅ Linked O(n)
   * - 9
     - Simultaneous Min-Max
     - §9.1
     - min ∧ max of array
     - ✅
     - —
   * - 9
     - Quickselect
     - §9.2
     - k-th smallest at position k
     - ✅
     - ✅ Pure O(n²)
   * - 9
     - Partial Selection Sort
     - §9.2
     - first k sorted, k-th correct
     - ✅
     - ✅ Pure O(nk)
   * - 10
     - Stack / Queue
     - §10.1
     - ghost list matches contents
     - ✅
     - ✅ Pure O(1)
   * - 10
     - Linked List
     - §10.2
     - ghost list matches contents
     - ✅
     - —
   * - 10
     - Doubly-Linked List
     - §10.2
     - segment pred ∧ ghost list
     - ✅
     - ✅ Linked O(1)
   * - 11
     - Hash Table (Chaining)
     - §11.2
     - key ↦ value lookup
     - ✅
     - ✅ Linked O(n)
   * - 12
     - BST Search / Delete
     - §12.2–3
     - key set operations
     - ✅
     - ✅ Pure O(h)
   * - 12
     - BST Insert
     - §12.3
     - key set updated
     - ⚠️ 3: BST preservation
     - ✅ Pure O(h)
   * - 13
     - Red-Black Tree
     - §13.1–4
     - Okasaki balance ∧ BST
     - ✅
     - ✅ Pure O(lg n)
   * - 15
     - Rod Cutting
     - §15.1
     - optimal revenue
     - ✅
     - ✅ Linked O(n²)
   * - 15
     - Ext. Rod Cutting
     - §15.1
     - optimal revenue ∧ valid cuts
     - ✅
     - ✅ Linked O(n²)
   * - 15
     - LCS
     - §15.4
     - LCS length
     - ✅
     - ✅ Linked O(mn)
   * - 15
     - Matrix Chain
     - §15.2
     - optimal parenthesization cost
     - ✅
     - ✅ Pure O(n³)
   * - 16
     - Activity Selection
     - §16.1
     - greedy = optimal count
     - ✅
     - ✅ Linked O(n)
   * - 16
     - Huffman Coding
     - §16.3
     - prefix-free tree construction
     - ⚠️ 5: optimality proof
     - ✅ Pure O(n lg n)
   * - 21
     - Union-Find
     - §21.3
     - find/union maintain forest
     - ⚠️ 1: rank bound assume
     - ✅ Pure O(α(n))
   * - 22
     - BFS (Queue)
     - §22.2
     - distances ∧ parent tree
     - ⚠️ 2: shortest path
     - ✅ Linked O(V²)
   * - 22
     - DFS (Stack)
     - §22.3
     - timestamps ∧ classification
     - ⚠️ 10: DFS theorems
     - ✅ Linked O(V²)
   * - 22
     - Kahn Topological Sort
     - §22.4
     - valid topological order
     - ⚠️ 2: DAG correctness
     - ✅ Linked O(V+E)
   * - 23
     - Kruskal MST
     - §23.2
     - MST of graph
     - ⚠️ 15: forest/cut/sort
     - ⚠️ Linked (3 admits)
   * - 23
     - Prim MST
     - §23.2
     - MST of graph
     - ⚠️ 6: light edge
     - ✅ Linked O(V²)
   * - 23
     - MST Theory
     - §23.1
     - cut/cycle properties
     - ⚠️ 4: cut theorem
     - —
   * - 24
     - Bellman-Ford
     - §24.1
     - SSSP distances
     - ⚠️ 3: upper bound
     - ✅ Linked O(VE)
   * - 24
     - Dijkstra
     - §24.3
     - SSSP distances
     - ⚠️ 2: triangle ineq
     - ✅ Linked O(V²)
   * - 25
     - Floyd-Warshall
     - §25.2
     - APSP distances
     - ✅
     - ✅ Linked O(n³)
   * - 26
     - Ford-Fulkerson (Max Flow)
     - §26.2
     - max flow ∧ valid flow
     - ⚠️ 8: augmentation
     - ⚠️ Pure (2 admits)
   * - 28
     - Matrix Multiply
     - §28 (App)
     - C = A · B
     - ✅
     - ✅ Linked O(n³)
   * - 28
     - Strassen
     - §28 (App)
     - Strassen = standard mult
     - ⚠️ 1: quadrant props
     - —
   * - 31
     - GCD / Extended GCD
     - §31.2
     - gcd ∧ Bézout coefficients
     - ✅
     - ✅ Linked O(lg n)
   * - 31
     - Modular Exponentiation
     - §31.6
     - result = b^e mod m
     - ✅
     - ✅ Linked O(lg e)
   * - 32
     - Naive String Match
     - §32.1
     - all match positions
     - ✅
     - ✅ Linked O(nm)
   * - 32
     - KMP
     - §32.4
     - all match positions
     - ✅
     - ⚠️ Linked (7 admits)
   * - 32
     - Rabin-Karp
     - §32.2
     - all match positions
     - ✅
     - ✅ Pure O(nm)
   * - 33
     - Segment Intersection
     - §33.1
     - correct intersection test
     - ✅
     - ✅ Pure O(1)
   * - 35
     - Vertex Cover (2-approx)
     - §35.1
     - cover ≤ 2 · OPT
     - ⚠️ 1: execution trace
     - ✅ Pure O(V+E)

Proof Gaps
----------

As of this writing, the project has **82 unproven F\* obligations**
(``admit()``, ``assume()``, and ``assume val``) across **29 files**,
plus **38 Pulse** ``assume_`` **calls** in 6 implementation files.
Of the 50 algorithms in the table, **33 have fully proven correctness**
(zero admits) and **26 have fully proven complexity bounds**.

The remaining admits fall into a few categories:

1. **Graph theory** (Ch. 22–23, ~39 F\* admits): DFS parenthesis and
   white-path theorems (10), MST cut/cycle properties and Kruskal
   forest invariants (25), BFS shortest-path completeness (2),
   Kahn DAG correctness (2). Plus 34 Pulse ``assume_`` in
   StackDFS and QueueBFS loop invariants.

2. **Sorting stability** (Ch. 8, 11 admits): RadixSort stability
   proofs involve ∃∀ quantifier patterns that challenge the SMT
   solver (10).  BucketSort needs concat-of-sorted-buckets (1).

3. **Algorithmic correctness** (Ch. 16, 24, 26, ~18 admits): Huffman
   optimality: greedy-choice theorem, optimal-substructure, and
   dependent proofs in Complete (5); shortest-path upper-bound
   invariants for Bellman-Ford (3) and Dijkstra triangle
   inequality (2); max-flow augmentation (8).

4. **Complexity proofs** (Ch. 32, 7 admits): KMP
   amortized analysis (7).

5. **Miscellaneous** (7 admits):
   BST insert preservation (3), Union-Find rank bound (1),
   Strassen quadrant properties (1), Vertex Cover trace (1),
   Divide-and-Conquer max-subarray (1 assume val).

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
