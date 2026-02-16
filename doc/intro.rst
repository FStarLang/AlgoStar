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
implemented across 164 F* source files totaling approximately 50,000
lines. The table below summarizes the status of each algorithm.

**Legend:**

- ✅ = fully proven (0 unproven obligations)
- ⚠️ = partially proven (some admits/assumes remain)
- The "Admits" column counts ``admit()``, ``assume(...)``, and
  ``assume_`` calls outside of comments.

.. list-table:: Algorithm Status
   :header-rows: 1
   :widths: 5 20 10 15 15 8

   * - Ch
     - Algorithm
     - CLRS §
     - Correctness
     - Complexity
     - Status
   * - 2
     - Insertion Sort
     - §2.1
     - ✅ sorted ∧ perm
     - ✅ Linked O(n²)
     - ✅
   * - 2
     - Merge Sort
     - §2.3
     - ✅ sorted ∧ perm
     - ✅ O(n log n)
     - ✅
   * - 4
     - Binary Search
     - §2.3
     - ✅ found⟹match
     - ✅ Linked O(lg n)
     - ✅
   * - 6
     - Heapsort
     - §6.4
     - ✅ sorted ∧ perm
     - ✅ O(n lg n)
     - ✅
   * - 7
     - Quicksort
     - §7.1
     - ✅ sorted ∧ perm
     - ✅ O(n²) worst
     - ✅
   * - 8
     - Counting Sort
     - §8.2
     - ✅ sorted ∧ perm
     - ✅ O(n+k)
     - ✅
   * - 8
     - Radix Sort
     - §8.3
     - ⚠️ partial
     - ✅ Θ(d(n+k))
     - ⚠️
   * - 10
     - Stack / Queue / DLL
     - §10.1–2
     - ✅ ghost list
     - ✅ Linked O(1)
     - ✅
   * - 11
     - Hash Table
     - §11.4
     - ✅ key lookup
     - ✅ Linked O(n)
     - ✅
   * - 12
     - BST Search/Delete
     - §12.2–3
     - ✅ key set ops
     - ✅ Linked O(h)
     - ✅
   * - 13
     - Red-Black Tree
     - §13.1–4
     - ✅ Okasaki balance
     - ✅ Linked O(lg n)
     - ✅
   * - 15
     - Rod Cutting
     - §15.1
     - ✅ optimal revenue
     - ✅ Linked O(n²)
     - ✅
   * - 15
     - LCS
     - §15.4
     - ✅ lcs length
     - ✅ Linked O(mn)
     - ✅
   * - 15
     - Matrix Chain
     - §15.2
     - ✅ optimal cost
     - ✅ Linked O(n³)
     - ✅
   * - 22
     - BFS / DFS
     - §22.2–3
     - ⚠️ partial
     - ✅ Linked O(V²)
     - ⚠️
   * - 23
     - Kruskal / Prim
     - §23.2
     - ⚠️ partial
     - ✅ Linked
     - ⚠️
   * - 24
     - Dijkstra / Bellman-Ford
     - §24
     - ⚠️ partial
     - ✅ Linked O(V²)
     - ⚠️
   * - 25
     - Floyd-Warshall
     - §25.2
     - ✅ APSP
     - ✅ Linked O(n³)
     - ✅
   * - 28
     - Matrix Multiply
     - §28.1
     - ✅ C = A·B
     - ✅ Linked O(n³)
     - ✅
   * - 31
     - GCD / ModExp
     - §31.2,6
     - ✅ Bézout + modexp
     - ✅ Linked
     - ✅
   * - 32
     - String Matching
     - §32.1,4
     - ✅ all matches
     - ✅ Linked O(nm)
     - ✅

Proof Gaps
----------

As of this writing, the project has **128 unproven obligations** across
35 files:

- **75** ``admit()`` calls in pure F* lemma bodies
- **15** ``assume(...)`` calls (inline assumptions)
- **38** ``assume_`` calls (Pulse-specific unproven invariants)

The majority of remaining admits fall into a few categories:

1. **Graph theory** (Ch. 22–23): Deep structural theorems about DFS
   (parenthesis theorem, white-path theorem), BFS shortest paths, and
   MST cut/cycle properties. These require substantial graph theory
   infrastructure.

2. **Pulse loop invariants** (Ch. 22, 8): The imperative BFS, DFS,
   and stable counting sort implementations have ``assume_`` calls
   for bounds and framing properties that need careful invariant
   strengthening.

3. **Algorithmic correctness** (Ch. 16, 24): Greedy exchange arguments
   for activity selection and Huffman coding, and shortest-path
   invariants for Bellman-Ford and Dijkstra.

4. **Stability and quantifier reasoning** (Ch. 8): RadixSort stability
   proofs involve ∃∀ quantifier patterns that challenge the SMT solver.

Each chapter in this document notes any unproven obligations in its
scope. Fully verified chapters (marked ✅ above) have zero ``admit``,
``assume``, or ``assume_`` calls.

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
