# AutoCLRS Book — Documentation Plan

## Goal

Write a companion to the CLRS textbook with formalized proofs in F* and Pulse.
The document serves as:
1. A detailed record of what is proven (and what isn't) for each algorithm
2. A practical guide to proof techniques for algorithms in F*/Pulse
3. A companion to "Proof-oriented Programming in F*" (PoP-in-FStar)

## Format

- ReStructuredText (.rst), following PoP-in-FStar conventions
- Code listings pulled from actual F*/Pulse source via `//SNIPPET_START: name` /
  `//SNIPPET_END: name` tags in .fst files, referenced with `.. literalinclude::`
- Sphinx build system (conf.py, Makefile, fstar_pygments.py copied from PoP-in-FStar)
- **Never copy code into the document** — always use literalinclude

## Scope: Introduction + Two Selected Chapters

We start with the Introduction and two chapters that are fully verified
(0 admits/assumes/assume_). Later chapters will be added as proofs mature.

---

## Chapter Selection

### Criteria
- 0 unproven obligations (clean chapter)
- Has both Pure F* specs and Pulse implementations
- Has linked complexity proofs (not just separate)
- Pedagogically interesting (demonstrates key proof techniques)

### Selected

**Chapter A: Sorting I — Insertion Sort & Merge Sort (CLRS Ch. 2)**

Why: Foundational algorithms every reader knows. Demonstrates the basic
proof-oriented programming workflow: pure functional spec → Pulse implementation
→ correctness proof → complexity proof. Introduces the key concepts (loop
invariants in Pulse, ghost sequences, permutation reasoning, amortized-style
counting) in a simple setting before tackling harder algorithms.

Files:
- `ch02-getting-started/CLRS.Ch02.InsertionSort.fst` — Pulse impl + correctness
- `ch02-getting-started/CLRS.Ch02.InsertionSort.Complexity.fst` — linked O(n²)
- `ch02-getting-started/CLRS.Ch02.MergeSort.fst` — Pulse impl + correctness
- `ch02-getting-started/CLRS.Ch02.MergeSort.Complexity.fst` — linked O(n log n)

**Chapter B: Dynamic Programming — Rod Cutting, LCS, Matrix Chain (CLRS Ch. 15)**

Why: Shows a different proof paradigm — optimal substructure + memoization.
All three algorithms are fully proven with 0 admits. Rod Cutting has the most
complete proof (including a pure spec module proving optimality). Demonstrates
2D array reasoning in Pulse, sequence manipulation for functional specs, and how
to link imperative table-filling to recursive optimal-substructure definitions.

Files:
- `ch15-dynamic-programming/CLRS.Ch15.RodCutting.fst` — Pulse impl
- `ch15-dynamic-programming/CLRS.Ch15.RodCutting.Spec.fst` — optimality proof
- `ch15-dynamic-programming/CLRS.Ch15.RodCutting.Complexity.fst` — linked O(n²)
- `ch15-dynamic-programming/CLRS.Ch15.LCS.fst` — Pulse impl + correctness
- `ch15-dynamic-programming/CLRS.Ch15.LCS.Complexity.fst` — linked O(mn)
- `ch15-dynamic-programming/CLRS.Ch15.MatrixChain.fst` — Pulse impl + correctness
- `ch15-dynamic-programming/CLRS.Ch15.MatrixChain.Complexity.fst` — linked O(n³)

### Alternatives considered but deferred
- Ch07 (Quicksort): Rich but large (2081 lines, 6 files) — good for a later chapter
- Ch10 (Data Structures): Great for Pulse separation logic — but less algorithmically
  interesting for a first pass
- Ch06 (Heapsort): Would pair well with Ch07 but deferred for scope
- Ch31 (Number Theory): Interesting but niche audience

---

## Document Structure

```
doc/
├── PLAN.md                  ← this file
├── conf.py                  ← Sphinx config (from PoP-in-FStar)
├── Makefile                 ← Sphinx build (from PoP-in-FStar)
├── fstar_pygments.py        ← F* syntax highlighting
├── index.rst                ← Top-level table of contents
├── intro.rst                ← Introduction chapter
├── ch02_sorting.rst         ← Chapter A: Insertion Sort & Merge Sort
└── ch15_dynamic_prog.rst    ← Chapter B: Dynamic Programming
```

---

## Task Breakdown

### Task 1: Scaffold — Build infrastructure
- [ ] 1a. Copy conf.py, Makefile, fstar_pygments.py from PoP-in-FStar, adapt paths
- [ ] 1b. Create index.rst with toctree
- [ ] 1c. Test that `make html` works (even with placeholder content)

### Task 2: Introduction (intro.rst)
- [ ] 2a. Motivation section: why formalize CLRS algorithms?
- [ ] 2b. Process section: AI-human collaboration, tools used, mode of interaction
  - How the project was developed: iterative AI-human workflow
  - What the AI did well (boilerplate, first-pass proofs, infrastructure)
  - What required human guidance (proof strategy, spec bug detection, invariant design)
  - Tools: F*, Pulse, Z3, GitHub Copilot CLI
- [ ] 2c. Results overview: summary table of all chapters with status
  - For each algorithm: what is proven, what is admitted
  - Green/yellow/red status indicators
- [ ] 2d. Proof gaps audit section: honest accounting of what remains unproven
- [ ] 2e. Reading guide: how to use this document alongside CLRS and PoP-in-FStar

### Task 3: Chapter A — Sorting I (ch02_sorting.rst)

#### 3a. Insertion Sort
- [ ] 3a.1. Algorithm description (reference CLRS §2.1, do NOT reproduce)
- [ ] 3a.2. Add SNIPPET tags to InsertionSort.fst for key code fragments:
  - Pure functional spec (sorted, permutation)
  - Pulse implementation with loop invariant
  - Main correctness theorem signature
- [ ] 3a.3. Add SNIPPET tags to InsertionSort.Complexity.fst:
  - Cost model / counter threading
  - Main complexity theorem signature
- [ ] 3a.4. Write RST: code listings via literalinclude
- [ ] 3a.5. Write RST: proof walkthrough — how the loop invariant works,
  what SMT handles automatically, what needed manual lemmas
- [ ] 3a.6. Write RST: complexity proof walkthrough — how the counter is
  threaded through Pulse, how the O(n²) bound is established

#### 3b. Merge Sort
- [ ] 3b.1. Algorithm description (reference CLRS §2.3)
- [ ] 3b.2. Add SNIPPET tags to MergeSort.fst:
  - Merge function spec + implementation
  - Recursive sort with correctness
- [ ] 3b.3. Add SNIPPET tags to MergeSort.Complexity.fst:
  - Complexity theorem signature
- [ ] 3b.4. Write RST: code listings + proof walkthrough
- [ ] 3b.5. Write RST: merge correctness (sorted + permutation preservation)
- [ ] 3b.6. Write RST: complexity — recursive cost accounting

#### 3c. Chapter wrap-up
- [ ] 3c.1. Proof techniques summary for this chapter
- [ ] 3c.2. Common pitfalls encountered and workarounds
- [ ] 3c.3. References to PoP-in-FStar for deeper coverage of techniques used

### Task 4: Chapter B — Dynamic Programming (ch15_dynamic_prog.rst)

#### 4a. Rod Cutting
- [ ] 4a.1. Algorithm description (reference CLRS §15.1)
- [ ] 4a.2. Add SNIPPET tags to RodCutting.Spec.fst:
  - Optimal substructure definition
  - Optimality proof
- [ ] 4a.3. Add SNIPPET tags to RodCutting.fst + Complexity.fst:
  - Pulse bottom-up DP implementation
  - Correctness theorem
  - O(n²) complexity theorem
- [ ] 4a.4. Write RST: the key insight — proving optimal_revenue matches
  the recursive definition, then linking to the imperative table-fill
- [ ] 4a.5. Write RST: proof walkthrough

#### 4b. Longest Common Subsequence
- [ ] 4b.1. Algorithm description (reference CLRS §15.4)
- [ ] 4b.2. Add SNIPPET tags to LCS.fst + Complexity.fst
- [ ] 4b.3. Write RST: 2D table-filling in Pulse, proof structure

#### 4c. Matrix Chain Multiplication
- [ ] 4c.1. Algorithm description (reference CLRS §15.2)
- [ ] 4c.2. Add SNIPPET tags to MatrixChain.fst + Complexity.fst
- [ ] 4c.3. Write RST: O(n³) nested loops, optimal parenthesization proof

#### 4d. Chapter wrap-up
- [ ] 4d.1. DP proof pattern summary: optimal substructure → recurrence → table-fill
- [ ] 4d.2. Pulse patterns for 1D and 2D DP
- [ ] 4d.3. References to PoP-in-FStar

### Task 5: Review & Polish
- [ ] 5a. Verify all literalinclude references resolve correctly
- [ ] 5b. Build HTML and check rendering
- [ ] 5c. Review for CLRS plagiarism — ensure all algorithm descriptions
  are original and reference-only
- [ ] 5d. Proof-read for technical accuracy
- [ ] 5e. Verify snippet tags don't break F* verification

---

## Execution Order

1. **Task 1** (scaffold) — prerequisite for everything
2. **Task 2** (intro) — can be written in parallel with Task 3
3. **Task 3** (Ch02 sorting) — start here for first chapter content
4. **Task 4** (Ch15 DP) — after Ch02 is drafted
5. **Task 5** (review) — final pass

For Tasks 3 and 4, snippet tagging (3a.2, 3b.2, 4a.2, etc.) must happen
before the RST writing that references them.

---

## Key Principles

1. **No plagiarism**: Reference CLRS sections by number; describe algorithms
   in our own words; focus on the F*/Pulse formalization, not the algorithm itself

2. **Code as truth**: All code in the document comes from verified .fst files
   via literalinclude. If a snippet doesn't verify, fix the code, not the doc.

3. **Honest about gaps**: The introduction includes a clear audit of what is
   and isn't proven. Individual chapters note any `admit`/`assume` in their scope.

4. **Pedagogical**: Explain *why* proofs are structured the way they are,
   not just *what* the proofs say. Point out where SMT automation helps and
   where manual lemmas were needed.

5. **Cross-reference PoP-in-FStar**: Don't re-explain F* basics. Point readers
   to the appropriate PoP-in-FStar chapter for background on refinement types,
   Pulse, separation logic, etc.
