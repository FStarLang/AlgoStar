# AutoCLRS: Verified CLRS Algorithms in Pulse/F*

## Quick Reference

### Build & Verify

```bash
cd /home/nswamy/workspace/everest/AutoCLRS

# Full build (all chapters, parallel)
make -j128

# Verify a single file
fstar.exe --include $(realpath ../pulse)/out/lib/pulse --include common <file.fst>

# Files needing chapter-level includes:
#   --include ch08-linear-sorting    (RadixSort, CountingSort.Stable, BucketSort)
#   --include ch09-order-statistics  (Select.Correctness, etc.)
#   --include ch12-bst               (BST.Insert.Spec, BST.Delete.Spec)
#   --include ch16-greedy            (Huffman.Complete)
#   --include ch22-elementary-graph  (DFS.WhitePath, DFS.Spec, TopologicalSort)
#   --include ch23-mst               (Kruskal.Spec, Prim.Spec, etc.)
#   --include ch24-sssp              (Dijkstra.TriangleInequality, BellmanFord.Spec)
#   --include ch32-string-matching   (KMP.StrengthenedSpec, RabinKarp.Spec)

# Debugging verification failures
fstar.exe --query_stats --split_queries always --z3refresh <file.fst>
```

### Documentation

- **22 chapter .rst files** in `doc/`, all using `literalinclude` with SNIPPET markers (no inline `code-block`)
- Use `:language: fstar` for pure F* specs, `:language: pulse` for Pulse code
- SNIPPET markers are `//SNIPPET_START: name` / `//SNIPPET_END: name` comments in .fst files
- Build docs: `cd doc && make html`
- All admits/assumes documented honestly in each chapter
- Index: `doc/index.rst` includes all chapters in order
- **Missing**: ch26 (MaxFlow) has no .rst file

### Conventions

- **Functional correctness**: Imperative code proven equivalent to a pure, total, recursive spec.
  E.g., postcondition `result == sort_spec input` or `sorted s ∧ permutation s0 s`.
- **Complexity proofs**: Ghost tick counter `ctr: GR.ref nat` threaded through Pulse code.
  Postcondition asserts `GR.pts_to ctr (c0 + bound)` where `bound` is a formula on input size.
  "**Linked**" = ghost ticks in Pulse code. "**Separate**" = pure F* analysis only, not connected.
- **Graphs**: Adjacency matrix as flat `array int` of size `n*n`, `1000000` as infinity.
- **Trees**: Array-backed with `left[i]`, `right[i]`, `color[i]`, `key[i]` arrays; `-1` as null.
  RBTree: Pointer-based with `box rb_node` and recursive `is_rbtree` slprop.
- **DLL**: True doubly-linked via DLS segment predicate (separation logic, box-allocated nodes).

### Proof Techniques That Work

- **FiniteSet algebra** (BST): `FStar.FiniteSet.Base` with `FS.all_finite_set_facts_lemma()`.
  Discharges set equality for tree insert/delete key-set proofs.
- **Queue/stack validity invariants** (Graph algos): `forall i. i in range ==> element < n`.
- **strong_valid_state pattern** (DFS): Bidirectional color↔timestamp invariant.
- **Ghost tick via GhostReference**: `tick ctr` increments counter; postcondition bounds it.
- **`Classical.forall_intro` for Seq.upd reasoning** (Rod Cutting Extended): When the SMT
  can't prove a universal `forall k. P(Seq.index (Seq.upd s j v) k)` after an update, write
  an F* helper lemma that case-splits on `k = j` vs `k <> j`, calls `Seq.lemma_index_upd1`
  or `Seq.lemma_index_upd2` explicitly, and concludes via `Classical.forall_intro`.
- **`is_sorted` quantifier explosion with `count_occ`** (SortedPerm): Use `--split_queries always`
  with `--fuel 1`. Avoid asserting facts that create new `Seq.index` terms.
- **`calc (==) { ... }` blocks for modular arithmetic** (RabinKarp): Step-by-step equational
  reasoning using `FStar.Math.Lemmas.*`. Use `FStar.Pure.BreakVC.break_vc()` before nested
  calc blocks in recursive proofs to prevent VC explosion.
- **Sentinel bridge proofs** (MatrixChain): When `min_splits(start, acc1) <= acc2 <= acc1`,
  result is identical. Prove via 3-way case split.
- **Table-filling induction** (MatrixChain): Prove each DP table entry correct by induction on
  `(i0 - start_i)`. Requires `--split_queries always` for reliable verification.
- **F* nat subtraction saturates at 0**: `not (j0 - i0 < l - 1)` doesn't give SMT
  `j0 - i0 >= l - 1`. Fix: branch on `j0 - i0 + 1 = l` (addition, not subtraction).
- **Pulse option match rewrite pattern** (RBTree): After `match x { None -> }`, Pulse rewrites
  slprops from `is_rbtree x ft` to `is_rbtree None ft`.
- **Pure classifier for deep Pulse pattern matching** (RBTree balance): Define a pure `classify`
  function + `classify_lemma` in Spec, dispatch to per-case helper functions in Pulse.
- **Predicate-based Pulse proofs** (StackDFS/QueueBFS): Define named predicates with
  `{:pattern}` triggers. Prove isolated lemmas. Call lemmas inline in Pulse body.
  Assert postcondition quantifiers explicitly after lemma calls.
- **BoundedIntegers operator shadowing**: Spec modules shared with Pulse must also
  `open Pulse.Lib.BoundedIntegers`. Or define pure predicates BEFORE the open.
- **Z3 context pollution**: Mark quantifier-containing definitions `[@@"opaque_to_smt"]`.
- **CLRS §32.2 hash is big-endian**: Adapted from `FStar/examples/algorithms/StringMatching.fst`.
- **`hash_inversion` for rolling hash** (RabinKarp): The key lemma for polynomial rolling hash
  proofs extracts the most-significant digit: `hash(i,j) == (hash(i+1,j) + d^(j-i-1)·x[i]) % q`.
  Enables `remove_msd_lemma` → `rolling_hash` correctness → `rolling_hash_step_correct`.
- **`Classical.move_requires` with named helpers** (RabinKarp): Use a named local `let helper ()
  : Lemma (requires P) (ensures Q) = ...` and call `Classical.move_requires helper ()`.
  The lambda form `move_requires (fun () -> ...)` doesn't type-check because it can't carry
  the precondition annotation.
- **Empty pattern edge case** (RabinKarp): `matches_at text pattern pos` with empty pattern is
  vacuously true at every position. No-false-negatives theorem requires `m > 0` precondition.

### Anti-patterns

- Agents replacing `admit()` with `assume val` don't reduce the real admit count.
- z3rlimit > 100 causes timeouts. Keep ≤ 50.
- `--admit_smt_queries true` hides real failures — never use.
- Removing `rec` can break SMT encoding (3 known cases in Select.Spec).
- Strengthening preconditions cascades to all callers — requires full invariant propagation.
- **Pulse nested loops shadow outer invariant properties**: When a Pulse `while` loop
  existentially binds ghost sequences, properties from outer loops are lost even if the inner
  loop never modifies them. **Fix**: repeat outer properties verbatim in inner loop invariant.
  (Discovered in `CLRS.Ch15.RodCutting.Extended.fst`.)
- **`Pulse.Lib.BoundedIntegers` operator shadowing**: This module redefines `<=`, `<`, `>=`,
  `>`, `+`, `-`, etc. When a spec module defines predicates using Prims operators and a Pulse
  file opens BoundedIntegers, the SMT sees *different symbols*, causing spurious failures.
  **Fix**: Spec modules shared with Pulse code must also `open Pulse.Lib.BoundedIntegers`.
  Or define pure predicates BEFORE the open.
- **BoundedIntegers in pure definitions within Pulse files**: After `open Pulse.Lib.BoundedIntegers`,
  pure F* definitions using `-` or `+` on `nat`/`int` fail with Error 228 ("Could not solve
  typeclass constraint `bounded_int ...`"). **Fix**: Define pure spec predicates BEFORE
  `open Pulse.Lib.BoundedIntegers` so that standard operators are in scope.
- **Z3 context pollution from quantifier-containing definitions**: Adding definitions with
  universal quantifiers BEFORE a Pulse proof causes failures — F*'s SMT encoding adds axioms
  for ALL module-level definitions to each query; new quantifier axioms create matching loops.
  **Fix**: Mark such predicates `[@@"opaque_to_smt"]` and define before BoundedIntegers. Use
  plain `nat` parameters (no refinements). Call a bridge lemma with `reveal_opaque` inside
  the function body.

### Idiomatic F* Patterns

- **Inductive lemmas**: Define as a single `let rec` with the induction hypothesis built into
  the recursive structure. Don't separate the IH as a higher-order function argument.
- **`introduce forall ... with introduce _ ==> _ with _.`**: Use this pattern to prove
  universally quantified implications. Avoids the pitfall of `if ... then ... else ()` inside
  `with (...)` which can fail because the false branch returns `unit` not `squash`.

### Pulse `with_pure` Usage Rules

- **Use `with_pure (P)` in preconditions** when postcondition slprops reference erased params
  that need bounds for well-formedness. Pulse doesn't propagate `pure` facts to postcondition
  well-formedness checking; `with_pure` does.
- **Anti-pattern**: `with_pure (a /\ b) (fun _ -> pure (c /\ d))` — when the inner slprop is
  just `pure(...)`, all facts should be a single `pure (a /\ b /\ c /\ d)`.
- **Predicate opacity**: Facts inside opaque predicates are NOT available for postcondition
  well-formedness. Repeat critical bounds explicitly alongside predicate calls.
- **Postconditions**: Use flat `pure (P /\ Q /\ R)` — no need for `with_pure` in ensures.

### Predicate-Based Pulse Proofs (StackDFS/QueueBFS Pattern)

When a Pulse program has repeated invariant clusters across function pre/post/loop specs:
1. **Define named predicates** with explicit `{:pattern}` triggers on all quantifiers.
2. **Prove isolated lemmas** relating predicates across operations.
3. **Call lemmas inline** in the Pulse body (before/after state-changing operations).
4. **Assert postcondition quantifiers explicitly** after lemma calls — Z3 can prove each
   quantifier individually but may fail when asked to prove them all at once.
5. **Use `with_pure` in requires** to expose bounds for postcondition well-formedness.
6. **Keep predicates transparent** (`let`, not `val`) so Z3 can unfold them when needed.
7. **Add target predicates to inner function postconditions** instead of deriving them from
   abstract frame properties — Z3 sees `Seq.upd` axioms directly.

---

## Current Status (2025-02-23, updated)

**180 F* files, ~59,500 lines — 91 unproven obligations across 30 files**

| Type | Count | Description |
|------|-------|-------------|
| `admit()` | 65 | Unproven lemma/proof bodies (Pure F*) |
| `assume(...)` | 12 | Inline assumptions (MaxFlow: 8, Huffman.Spec: 4) |
| `assume val` | 2 | Axiomatized declarations (MaxSubarray.DC: 1, Kruskal: 1) |
| `assume_` | 12 | Pulse-specific unproven invariants (StackDFS.Cmplx: 6, QueueBFS.Cmplx: 6) |

### Key Progress Since AUDIT_0215 (Feb 15)

| Item | Old Status | New Status | Admits Δ |
|------|-----------|------------|----------|
| RBTree (Ch13) | ❌ Broken, no rotations | ✅ Pointer-based, full balance, zero admits | −0 (was 0 trivially) |
| ActivitySelection (Ch16) | 9 admits (exchange arg) | ✅ Zero admits, full optimality | −9 |
| RabinKarp.Spec (Ch32) | 3 admits | ✅ Zero admits, CLRS polynomial hash | −3 |
| MatrixChain.Spec (Ch15) | Unproven | ✅ Zero admits, sentinel bridge proven | 0 (new) |
| StackDFS main (Ch22) | 4 assume_ | ✅ Zero assumes, predicate-based | −4 |
| QueueBFS main (Ch22) | 4 assume_ | ✅ Zero assumes, predicate-based | −4 |
| UnionFind.RankBound (Ch21) | 1 admit | ✅ Zero admits | −1 |
| RodCutting.Spec (Ch15) | 1 assume val | ✅ Removed (dead code) | −1 |
| Dijkstra.Correctness (Ch24) | Did not exist | ✅ New file, proves d[v]=δ(s,v) | 0 (new) |
| RadixSort.FullSort (Ch08) | ~7 admits | 4 admits remaining | −3 |
| Prim.Complexity (Ch23) | 2 admits | ✅ Zero admits | −2 |
| **Net change** | ~155 total | ~97 total | **−58** |

### Per-Algorithm Status Table

| Ch | Algorithm | CLRS § | Func. Spec | Complexity | Admits | Notes |
|----|-----------|--------|------------|------------|--------|-------|
| 02 | Insertion Sort | §2.1 | ✅ sorted ∧ perm | ✅ Linked O(n²) | 0 | |
| 02 | Merge Sort | §2.3 | ✅ sorted ∧ perm | ⚠️ Separate O(n lg n) | 0 | |
| 04 | Binary Search | §2.3 | ✅ found⟹match, ¬found⟹∉ | ✅ Linked O(lg n) | 0 | |
| 04 | MaxSubarray.Kadane | — | ⚠️ self-referential spec | ✅ Linked O(n) | 0 | Not CLRS; spec IS algo |
| 04 | MaxSubarray D&C | §4.1 | ⚠️ 1 axiom | ⚠️ Separate O(n lg n) | 1 | Pure F* only |
| 06 | Heapsort | §6.4 | ✅ sorted ∧ perm | ⚠️ Separate O(n lg n) | 0 | |
| 07 | Partition (Lomuto) | §7.1 | ✅ partitioned ∧ perm | ✅ Linked O(n) | 0 | |
| 07 | Quicksort | §7.1 | ✅ sorted ∧ perm | ✅ Linked O(n²) | 0 | Enhanced file |
| 08 | CountingSort | §8.2 | ✅ sorted ∧ perm | ⚠️ Separate O(n+k) | 0 | 2-phase (not CLRS) |
| 08 | CountingSort.Stable | §8.2 | ❌ assumed postconds | ⚠️ Separate | 3 assume_ | CLRS 4-phase |
| 08 | RadixSort (d=1) | §8.3 | ✅ sorted ∧ perm | ⚠️ Separate Θ(d(n+k)) | 0 | d=1 only |
| 08 | RadixSort.MultiDigit | §8.3 | ⚠️ partial | — | 10 | Pure F*; stability admits |
| 08 | BucketSort | §8.4 | ⚠️ no perm proof | — | 1 | |
| 09 | MinMax | §9.1 | ✅ correct min/max | ✅ Linked O(n) | 0 | |
| 09 | SimultaneousMinMax | §9.1 | ✅ (min,max) | ✅ Linked 2(n-1) | 0 | |
| 09 | PartialSelectionSort | — | ✅ perm ∧ prefix sorted | ⚠️ Separate O(nk) | 0 | Not CLRS |
| 09 | Quickselect | §9.2 | ✅ perm ∧ result=s[k] | ⚠️ Separate O(n²) | 0 | |
| 10 | Stack | §10.1 | ✅ ghost list LIFO | ⚠️ Separate O(1) | 0 | |
| 10 | Queue | §10.1 | ✅ ghost list FIFO | ⚠️ Separate O(1) | 0 | |
| 10 | SinglyLinkedList | §10.2 | ✅ is_dlist | — | 0 | |
| 10 | DLL | §10.2 | ✅ DLS segment pred | ✅ Linked | 0 | |
| 11 | HashTable | §11.4 | ⚠️ key_in_table | ✅ Linked O(n) | 0 | No duplicate guard |
| 12 | BST Search/Min/Max | §12.2 | ✅ correct search | ✅ Linked O(h) | 0 | Array-based |
| 12 | BST Insert | §12.3 | ⚠️ membership only | ⚠️ Separate O(h) | 3 | Doesn't walk BST path |
| 12 | BST Delete | §12.3 | ✅ key_set \ {k} | ✅ Linked O(h) | 0 | FiniteSet algebra |
| 13 | RBTree (Pulse) | §13.1–4 | ✅ is_rbtree y (S.insert ft k) | ✅ Linked O(lg n) | 0 | ✅ Pointer-based, Okasaki balance |
| 13 | RBTree.Spec (pure) | §13.1–4 | ✅ Okasaki + Thm 13.1 | ✅ Linked O(lg n) | 0 | |
| 15 | LCS | §15.4 | ✅ result=spec | ✅ Linked O(mn) | 0 | |
| 15 | MatrixChain | §15.2 | ✅ mc_cost proven | ⚠️ Separate O(n³) | 0 | ✅ Sentinel bridge |
| 15 | RodCutting | §15.1 | ✅ optimal_revenue | ✅ Linked O(n²) | 0 | |
| 15 | RodCutting.Extended | §15.1 | ✅ cuts_are_optimal | — | 0 | |
| 16 | ActivitySelection | §16.1 | ✅ exchange argument | ✅ Linked O(n) | 0 | ✅ Full optimality |
| 16 | Huffman | §16.3 | ⚠️ cost only | ✅ Linked (cost) | 6 | Spec: greedy+substructure assumed |
| 21 | Union-Find | §21.3 | ✅ find=root, union | ⚠️ Separate O(mn) | 1 assume | FullCompress available |
| 22 | IterativeBFS | — | ⚠️ reachability | — | 0 | Not CLRS |
| 22 | QueueBFS | §22.2 | ⚠️ no shortest path | ✅ Linked O(n²) | 0+6 | Main: 0; Cmplx: 6 assume_ |
| 22 | IterativeDFS | — | ⚠️ reachability | — | 0 | Not CLRS |
| 22 | StackDFS | §22.3 | ⚠️ d<f, no full nesting | ✅ Linked O(n²) | 0+6 | Main: 0; Cmplx: 6 assume_ |
| 22 | KahnTopologicalSort | — | ✅ topo order ∧ distinct | ✅ Linked O(n²) | 0 | ✅ Fully verified (was 2 admits) |
| 22 | BFS/DFS specs | §22 | ⚠️ partial | — | 8 | Distance, parenthesis, white-path |
| 23 | Kruskal | §23.2 | ⚠️ forest, not MST | ✅ Linked O(n³) | 16 | Across Spec/EdgeSort/Cmplx |
| 23 | Prim | §23.2 | ⚠️ key bounds only | ✅ Linked O(n²) | 6 | |
| 23 | MST.Spec | §23.1 | ⚠️ admitted | — | 4 | Exchange lemma proven |
| 24 | Dijkstra | §24.3 | ⚠️ upper bound (Pulse) | ✅ Linked O(n²) | 1 | Correctness.fst: d=δ proven |
| 24 | Bellman-Ford | §24.1 | ⚠️ upper bound only | ⚠️ Separate O(V³) | 3 | |
| 25 | Floyd-Warshall | §25.2 | ✅ result=spec | ✅ Linked O(n³) | 0 | |
| 26 | MaxFlow | §26.2 | ❌ STUB | — | 8 assume | Stretch goal |
| 28 | MatrixMultiply | §28.1 | ✅ C=A·B | ✅ Linked O(n³) | 0 | |
| 28 | Strassen | §28.2 | ⚠️ 1 structural admit | ⚠️ Separate | 1 | |
| 31 | GCD | §31.2 | ✅ result=gcd(a,b) | ✅ Linked O(lg b) | 0 | |
| 31 | ExtendedGCD | §31.2 | ✅ Bézout identity | — | 0 | Pure F* |
| 31 | ModExp | §31.6 | ✅ (b^e)%m | ✅ Linked O(lg e) | 0 | |
| 32 | NaiveStringMatch | §32.1 | ✅ all matches | ✅ Linked O(nm) | 0 | |
| 32 | KMP | §32.4 | ⚠️ prefix correct; matcher weak | ✅ Linked O(n+m)* | 7 | *Amortized admits |
| 32 | RabinKarp | §32.2 | ✅ CLRS polynomial hash | ⚠️ Separate O(nm) | 0 | ✅ hash_inversion proven |
| 33 | Segments | §33.1 | ✅ intersection | ⚠️ Separate O(1) | 0 | |
| 35 | VertexCover | §35.1 | ✅ valid cover + 2-approx | ⚠️ Separate O(V²) | 1 | |

### Unproven Obligation Distribution (67 admit + 16 assume + 2 assume_val + 12 assume_ = 97 total)

| Chapter | admit | assume | assume_val | assume_ | Total | Top files |
|---------|-------|--------|------------|---------|-------|-----------|
| ch23 (MST) | 23 | 1 | 1 | 1 | 26 | Kruskal.Spec(9), Prim.Spec(6), MST.Spec(4), Kruskal.Cmplx(2+1), EdgeSort(2), SortedEdges(0+1), Kruskal(0+0+1) |
| ch22 (graphs) | 8 | 0 | 0 | 12 | 20 | StackDFS.Cmplx(0+0+6), QueueBFS.Cmplx(0+0+6), DFS.Spec(5), DFS.WhitePath(3), BFS.DistSpec(2) |
| ch08 (sorting) | 11 | 0 | 0 | 3 | 14 | RadixSort.FullSort(4), RS.MultiDigit(2), RS.Spec(2), RS.Stability(2), CountingSort.Stable(0+3), BucketSort(1) |
| ch26 (MaxFlow) | 0 | 8 | 0 | 0 | 8 | MaxFlow.Proofs(4), MaxFlow.Spec(2), MaxFlow.Cmplx(2) — **stretch goal** |
| ch32 (strings) | 7 | 0 | 0 | 0 | 7 | KMP.Complexity(7) |
| ch16 (greedy) | 2 | 4 | 0 | 0 | 6 | Huffman.Complete(2), Huffman.Spec(0+4) |
| ch24 (SSSP) | 4 | 0 | 0 | 0 | 4 | BellmanFord.Spec(3), Dijkstra.TriIneq(1) |
| ch12 (BST) | 3 | 0 | 0 | 0 | 3 | BST.Insert.Spec(3) |
| Other | 2 | 1 | 1 | 0 | 4 | MaxSubarray.DC(0+0+1), VertexCover.Spec(1), Strassen(1), UF.Spec(0+1) |
| **Total** | **66** | **14** | **2** | **12** | **94** | |

---

## Key Learnings

### What Worked Well

1. **Predicate-based refactoring for Pulse proofs**: Named predicates with `{:pattern}` triggers
   + isolated lemmas proved in isolation + inline calls in Pulse bodies. This pattern eliminated
   all assume_ in StackDFS.fst and QueueBFS.fst (8 assume_ → 0). Should be applied to the
   remaining Complexity files.

2. **Okasaki-style balance for RBTree**: Instead of CLRS's imperative case-analysis approach,
   the pure classifier + per-case handler pattern made the Pulse RBTree tractable.
   Key insight: define `classify_runtime` as read-only traversal, then dispatch to handlers.

3. **Ghost execution traces for exchange arguments**: ActivitySelection succeeded by maintaining
   a ghost sequence `sel` tracking selected indices, with `earliest_compatible` predicate
   carried through the loop invariant. This pattern may transfer to VertexCover.

4. **Sentinel bridge proofs for DP**: MatrixChain.Spec proved correctness by showing that
   for any two accumulators satisfying `min_splits(start, acc1) <= acc2 <= acc1`, the result
   is the same. Induction on `(i0 - start_i)` with `--split_queries always`.

5. **CLRS-faithful hash**: RabinKarp was fixed to use CLRS big-endian polynomial hash
   (adapted from FStar/examples/algorithms/StringMatching.fst). Key lemma: `hash_inversion`.

### What's Hard

1. **Graph theory proofs**: MST cut property, DFS parenthesis theorem, BFS shortest-path —
   these require deep structural induction over graph topology. 32 of 97 admits are in ch22+ch23.
   No clear path to automation; may require fundamentally new ghost state.

2. **Stability proofs for RadixSort**: The cascade CountingSort.Stable → RadixSort.Stability →
   MultiDigit → FullSort has 14 admits. The root cause is that CountingSort.Stable's key
   postconditions (sorted, permutation) are assumed. Proving those requires tracking position
   assignments through the backwards pass.

3. **Amortized complexity (KMP)**: The 7 admits in KMP.Complexity need a formal potential
   function argument. This is intrinsically difficult in F* because the potential changes
   non-monotonically across iterations.

4. **Self-referential specs**: MaxSubarray.Kadane proves `result == kadane_spec(input)` where
   the spec IS the algorithm. LCS and Floyd-Warshall prove equivalence to their recurrences
   but do not independently prove the recurrences solve the stated problems. This is a pattern
   across the codebase that should be acknowledged.

### Spec Strength Hierarchy

From strongest to weakest:
1. **Full independent optimality**: RodCutting, MatrixChain, ActivitySelection — spec independently
   proves the recurrence/greedy choice is optimal
2. **Recurrence equivalence**: LCS, FloydWarshall — proves Pulse equals pure recurrence,
   which CLRS proves is correct (but we don't re-prove that)
3. **Property-based**: Sorting (sorted ∧ perm), BST (key membership), GCD — proves desired
   mathematical property directly
4. **Self-referential**: Kadane — proves Pulse equals spec that IS the algorithm
5. **Partial**: Kruskal (forest only), Dijkstra-main (upper bound only)
6. **Trivial**: MaxFlow (zero flow), CountingSort.Stable (assumed)

---

## Action Plan

### Phase 1: Documentation & Code Comments Update

Update all docs and code comments to accurately reflect current state, including
the Kahn topological sort work (most recent), and fix known doc/code discrepancies.
Good for human review in parallel with later phases.

#### 1a: Code comment headers — update stale admit/assume claims
- [ ] **ch22 KahnTopologicalSort.Complexity.fst**: Header says "Uses admit() where needed" but
  file now has **0 admits**. Update header to reflect fully verified status.
- [ ] **ch22 KahnTopologicalSort.fst**: Ensure header comments reflect 0 admits (split into Defs+Pulse).
- [ ] Sweep all .fst headers: any file whose comment says "N admits" but actual count differs
  should be updated. Key files to check: all recently-fixed files (StackDFS, QueueBFS,
  ActivitySelection, RabinKarp, MatrixChain, RodCutting.Spec, UnionFind.RankBound).

#### 1b: ch22_graphs.rst — update Kahn topological sort section
- [ ] **KahnTopologicalSort**: Doc says "2 admit() calls" (line 247) — now **0 admits**.
  Rewrite to reflect the fully verified status, including the Defs module split and
  the proof techniques used (pn_completeness, indeg_correct, pigeonhole via count_occurrences).
- [ ] **Verification Status Summary table** (line 300–302): Change KahnTopologicalSort from
  "2 admit()" to "**0** ✅". Add KahnTopologicalSort.Defs and .Defs.fsti as 0-admit entries.
- [ ] Add brief description of the proof architecture: the split into Defs (pure predicates +
  lemmas) and KahnTopologicalSort (Pulse), and the key invariants (indeg_correct, strong_order_inv,
  partial_distinct, pn_completeness).

#### 1c: ch26_max_flow.rst — create missing doc
- [ ] Create `doc/ch26_max_flow.rst` documenting the MaxFlow stub honestly. Include what
  Spec defines (valid_flow, augment_preserves_valid) and the 8 assume()s. Add to index.rst.

#### 1d: README.md — fix overstatement
- [ ] The "Zero admits across ~18,000 lines" is misleading. Replace with accurate statement:
  "148 files fully verified with zero admits (~42,600 lines). 32 files have 93 remaining
  admits (~16,900 lines)." (93 = 97 minus the 4 Kahn admits now resolved.)

#### 1e: intro.rst — update admit counts and summary table
- [ ] Line 432: "82 unproven F* obligations" → update to current count (~93).
- [ ] Line 436: "26 have fully proven complexity bounds" → recount.
- [ ] Category breakdown (lines 440–463): update counts per category.
- [ ] Summary table: update KahnTopologicalSort, ActivitySelection, RabinKarp, MatrixChain
  entries to reflect ✅ status.

#### 1f: Other chapter .rst files — accuracy sweep
- [ ] **ch24_sssp.rst**: Clarify that Dijkstra.Correctness.fst proves d[v]=δ(s,v) with zero
  admits, but the chain to the Pulse implementation passes through 2 admits in TriangleInequality.
- [ ] **ch15_dynamic_prog.rst / ch25_apsp.rst**: Add note that LCS and Floyd-Warshall prove
  equivalence to their recurrences, not that the recurrences independently solve the stated
  problems (this is a standard approach but should be documented).
- [ ] **ch16_greedy.rst**: Clarify Huffman admit breakdown: 2 admit() in Complete + 4 assume()
  in Spec = 6 total.

### Phase 2: Critical Proof Gaps

#### 2a: DFS.Spec Termination Assumes (2 assume in visit_neighbors + dfs_visit) — ✅ DONE
**Goal**: Eliminate the 2 `assume` calls that bypass the termination proof for the mutually
recursive `visit_neighbors`/`dfs_visit` functions in DFS.Spec.fst (lines 214 and 231).

Both assumes assert `count_white_vertices st1 < count_white_vertices st` — i.e., the white
vertex count strictly decreases. These are the termination measures for the lexicographic
`decreases %[count_white_vertices st; ...]` annotation.

**Step 1: Fix dfs_visit (line 231).** The assume after `discover_vertex u st` is:
```
assume (count_white_vertices st1 < count_white_vertices st);
```
The existing lemma `discover_decreases_white_count` (line 181) already proves exactly this,
given: `u < st.n`, `u < Seq.length st.color`, `Seq.index st.color u = White`,
`Seq.length st.d = st.n`. These preconditions all hold in the calling context (guarded by
the `if` chain at lines 224–226 + length invariants from `discover_preserves_lengths`).
**Fix**: Replace the `assume` with a call to `discover_decreases_white_count u st`.
May need to propagate length invariants (color/d/f arrays all have length n) as a
precondition or prove them inline.

**Step 2: Fix visit_neighbors (line 214).** The assume after `dfs_visit adj n v st` is:
```
assume (count_white_vertices st1 < count_white_vertices st);
```
This requires `dfs_visit` to *return* a state with strictly fewer white vertices
(when the input vertex is white). **Fix**: Enrich the return type of `dfs_visit` to:
```fstar
and dfs_visit (adj: ...) (n: nat) (u: nat) (st: dfs_state)
  : Tot (st':dfs_state{
      u < Seq.length st.color /\ Seq.index st.color u = White ==>
      count_white_vertices st' < count_white_vertices st})
    (decreases %[count_white_vertices st; 0])
```
This requires proving that the composition `discover_vertex` → `visit_neighbors` →
`finish_vertex` never *increases* white count (discover decreases by 1, visit_neighbors
is monotonically non-increasing, finish_vertex only changes Gray→Black which doesn't
affect white count). The key property is that `visit_neighbors` preserves `count_white_vertices st' <= count_white_vertices st_input` — which follows from the
fact that it only calls `dfs_visit` on white vertices (which decreases white count)
or skips already-visited ones.

**Dependencies**: Step 2 depends on Step 1. Once `dfs_visit` has the enriched return
type, the `assume` in `visit_neighbors` can be replaced by the refinement from the
return type of the recursive `dfs_visit` call.

#### 2b: Close Dijkstra End-to-End (2 admits in TriangleInequality) — ⚠️ PARTIAL (2→1)
**Goal**: Make Dijkstra the first SSSP algorithm with fully proven exact shortest paths.
- Dijkstra.Correctness (zero admits) already proves d[v]=δ(s,v) given triangle inequality + upper bound.
- TriangleInequality.fst ~~2~~ **1** admit remaining: stability maintenance across processing steps.
- **Done**: Added `relaxation_stable_for_processed` predicate, proved preservation under stability.
- **Remaining**: Proving stability is maintained when processing order follows Dijkstra's greedy extraction.

#### 2c: Close Bellman-Ford Spec (3 admits)
- Line 235: relaxation preserves upper bound — should be provable with path weight algebra
- Line 405: inductive correctness after k rounds — needs induction on path length
- Line 454: negative cycle detection — needs path with n+ edges implies cycle

#### 2d: CountingSort.Stable Postconditions (3 assume_)
**Impact**: Unblocks the entire RadixSort stability cascade (14 admits depend on this).
- Position bounds (line 260): prove cumulative sum stays in [1, n]
- Sorted output (line 284): prove backward placement + cumulative counts → sorted
- Permutation (line 285): prove each element placed exactly once

#### 2e: BST Insert Path (3 admits in Insert.Spec)
- Need to walk the BST comparison path instead of appending at next free slot
- Or: prove current array-based insert preserves BST property with current approach
  (subtree range preservation, disjoint subtree invariance, key set membership)

### Phase 3: Link Separate Complexity Proofs to Pulse

17 algorithms have pure F* complexity proofs not connected via ghost ticks.
**Do NOT duplicate the code** — add ghost tick counters directly to the existing
verified Pulse implementations (alongside the existing correctness postconditions).

**Easy (simple loop structure, add tick + postcondition):**
- [ ] 3a: CountingSort O(n+k) — 2-phase, straightforward loop
- [ ] 3b: MatrixChain O(n³) — triple loop, similar to FloydWarshall
- [ ] 3c: BellmanFord O(V³) — triple loop (depends on 2b or can be done independently)

**Medium (recursive or multi-loop):**
- [ ] 3d: MergeSort O(n lg n) — recursive with merge subroutine; tick through recursion
- [ ] 3e: Heapsort O(n lg n) — build-heap + extract-max + sift-down loops
- [ ] 3f: Quickselect O(n²) — partition-based tail recursion

**Low priority:**
- [ ] 3g: Stack/Queue O(1), Segments O(1), VertexCover O(V²), RabinKarp O(nm)

### Phase 4: Complexity File Cleanup (Apply Known Patterns)

These use the predicate-based pattern that worked for StackDFS/QueueBFS main files.

- [ ] 4a: **QueueBFS.Complexity** (6 assume_): Apply same predicates from QueueBFS.fst + tick arithmetic.
  Expected: all 6 assume_ can be eliminated.
- [ ] 4b: **StackDFS.Complexity** (6 assume_): Apply same predicates from StackDFS.fst + tick arithmetic.
  Expected: all 6 assume_ can be eliminated.
- [ ] 4c: **Kruskal.Complexity** (2 admit + 1 assume_): Minor tick arithmetic. The assume_ at line 333
  may need inner loop invariant + tick bound for n<3 edge case.

### Phase 5: Missing CLRS Theorems (Hard)

| Item | CLRS Ref | Admits | Difficulty | Approach |
|------|----------|--------|------------|----------|
| 5a: BFS shortest paths | Thm 22.5 | 2 | Hard | BFS.DistanceSpec: prove no shorter path via induction on BFS levels |
| 5b: DFS parenthesis | Thm 22.7 | 7+3 | Very Hard | DFS.Spec + WhitePath: induction over entire DFS execution |
| 5c: MST cut property | Thm 23.1 | 4+9+6 | Very Hard | MST.Spec + Kruskal.Spec + Prim.Spec: exchange argument for minimum weight |
| 5d: Huffman optimality | Thm 16.3 | 6 | Hard | Huffman.Spec: greedy choice + optimal substructure |
| 5e: VertexCover 2-approx | Thm 35.1 | 1 | Medium | VertexCover.Spec: ghost matching extraction |
| 5f: KMP amortized O(n+m) | §32.4 | 7 | Hard | KMP.Complexity: formal potential function |

### Phase 6: Missing CLRS Algorithms

- [ ] 6a: **DFS-based TopologicalSort** (ch22) — Sort by StackDFS finish times
- [ ] 6b: **D&C MaxSubarray in Pulse** (ch04) — From DivideConquer.fst pure spec
- [ ] 6c: **Multi-digit RadixSort in Pulse** (ch08) — Stable CountingSort d times (depends on 2c)
- [ ] 6d: **Huffman tree construction** (ch16) — Priority queue + merge loop
- [ ] 6e: **RBTree DELETE** (ch13) — 8 fixup cases, currently missing

### Phase 7: Stretch Goals

- [ ] 7a: MaxFlow Ford-Fulkerson (ch26) — full Edmonds-Karp
- [ ] 7b: Union-Find O(m·α(n)) amortized (ch21) — inverse Ackermann
- [ ] 7c: Max-flow min-cut theorem (ch26)
- [ ] 7d: KMP matcher strengthened spec (count == count_matches_spec)

---

## Session Log (2025-02-23)

### Completed
- **AUDIT_0223.md**: Full audit of all 180 files, 22 chapters, 24 doc files
- **PROGRESS_PLAN.md**: Consolidated from PROGRESS_PLAN_0223.md + old PROGRESS_PLAN.md.
  Updated with current counts, key learnings, prioritized action plan.
- **KahnTopologicalSort**: Confirmed fully verified (0 admits across all files including Complexity)
  after the commit series 49f47b1..51374a7. The AUDIT_0215 said "2 admit()" — now resolved.
- **Key findings**:
  - 155 → ~93 admits since AUDIT_0215 (40% reduction)
  - RBTree, ActivitySelection, RabinKarp, MatrixChain.Spec, Kahn all fully proven
  - StackDFS/QueueBFS main fully proven (complexity files remain)
  - Dijkstra.Correctness.fst new — proves d[v]=δ(s,v) (chain incomplete: 2 admits in TriIneq)
  - Documentation mostly accurate; main gaps: ch26 .rst missing, README overstatement,
    ch22 Kahn section stale

## Session Log (2025-02-21)

### Completed
- **QueueBFS.fst**: Fully verified, 0 assume_ (was 4). Commit `fb5bafe`.
  - Predicates: `queue_ok`, `dist_ok`, `source_ok`, `count_nonwhite` with `{:pattern}` triggers
  - Lemmas: `queue_ok_after_discover`, `blacken_preserves_queue_ok`, `blacken_preserves_source_ok`,
    `blacken_preserves_dist_ok`, `discover_preserves_dist_ok`, 6 `count_nonwhite_*` lemmas
  - Key insight: add `queue_ok` directly to `maybe_discover` postcondition so Z3 reasons about
    exact `Seq.upd` terms (avoids chained quantifier trigger failures through abstract frame props)
  - Bug fix: `count_nonwhite_upd_single` was called with post-assignment state; fixed to use
    pre-assignment state via `with scolor_zeros`
- **ActivitySelection.fst**: Fixed flaky SMT with `--z3rlimit 20`. Commit `f65573b`.

---

## Appendix: Detailed Per-File Admit Tracking

### Tier 1: Automatable (Z3 with hints / simple lemma calls) — ~15 admits remaining

After systematic attempts, most initially-classified "automatable" admits turned out to be blocked
by deeper issues. Status tracking from prior sessions:

| File | Line(s) | Admits | Status |
|------|---------|--------|--------|
| Prim.Complexity | 130 | 0 | ✅ Fixed: loop invariant v_iter < n in inner loops |
| Kruskal.Complexity | 371, 390 | 2 | ❌ Blocked: Pulse admits + bound fails for n<3 + upstream assume_ at 333 |
| Kruskal.Spec | 452, 378 | 2 | ❌ Blocked: needs build_components induction + cut property |
| RadixSort.Stability | 150, 208 | 2 | ❌ Blocked: Z3 incomplete quantifiers on nested ∃/∀ in sorted_up_to_digit |
| RadixSort.FullSort | 269 | 0 | ✅ Proved with SeqP.index_tail + explicit quantifier trigger |
| RadixSort.FullSort (digit_decomposition) | | 0 | ✅ Proved with pow_split + modular arithmetic |
| RadixSort.FullSort (digits_lex_order) | | 0 | ✅ Proved with lemma_digit_sum_msd_le_3 + StrongExcludedMiddle |
| RadixSort.FullSort (sorted_up_to_all_digits) | | 0 | ✅ Proved via pairwise ordering + digits_lex_order_implies_numeric_order |
| PartialSelect | 117 | 1 | ❌ Blocked: Z3 can't bridge count_occ/tail/sorted quantifiers |
| UnionFind.RankBound | — | 0 | ✅ All invariants fully proven (size_correctness_invariant added) |
| UnionFind.Spec | 92 | 1 | ❌ Blocked: Z3 can't instantiate refined quantifier from rank_invariant |
| Prim.Spec | 209, 270 | 2 | ❌ Blocked: Needs find_min_edge_aux trace |
| RabinKarp.Spec | — | 0 | ✅ CLRS-faithful big-endian hash, hash_inversion + rolling_hash proven |
| ActivitySelection.Spec | 305 | 1 | ❌ Blocked: max_compatible_count is itself admitted |

### Tier 2: Helper lemmas (provable separately, then plugged in) — ~40 admits

Each needs a standalone lemma proved first, then called at the admit site.

| File | Admits | Helper lemma needed |
|------|--------|---------------------|
| **StackDFS.fst** | 0 | ✅ All 4 assume_ eliminated via predicate-based refactoring |
| **StackDFS.Complexity** | 6 | vtop < n (2), found ==> top < n (1), vc bound (2), final postcondition (1) |
| **QueueBFS.fst** | 0 | ✅ Fully verified via predicate-based proof |
| **QueueBFS.Complexity** | 6 | Mirror of QueueBFS.fst: same invariants + tick arithmetic |
| **RadixSort.Stability** | 2 | Stable-sort preservation: equal-key elements maintain relative order |
| **RadixSort.Spec** | 1 | Same as Stability but at spec level |
| **RadixSort.FullSort** | 4 | Bridge admits: reference results from RadixSort.Stability module |
| **Kruskal.Spec** | 13 | ✅ same_component_symmetric + transitive PROVEN. Remaining: decidability, forest preservation, MST optimality |
| **Prim.Spec** | 3 | Prim step verification: trace find_min_edge_aux |
| **BFS.DistanceSpec** | 1 | ✅ reachable_trans PROVEN. L219: visited ⟹ path exists (parent-pointer reconstruction) |
| **BellmanFord.Spec** | 1 | Negative cycle detection: post-(n-1)-round distance change ⟹ cycle |
| **Dijkstra.TriIneq** | 1 | Triangle preservation for processed vertices |
| **PartialSelect.Correctness** | 2 | Count-based uniqueness: count_lt + count_le determine k-th element |
| **UnionFind.Spec** | 2 | Path tracing after parent update / union |
| **MaxSubarray.DC** | 1 | D&C and Kadane equivalence |
| **BucketSort** | 1 | Sorted bucket concatenation |
| **CountingSort.Stable** | 1 | Cumulative count bounds |

### Tier 3: Expert guidance required (deep structural / new invariants) — ~40 admits

These require fundamental proof architecture changes: new ghost state, new invariants
threaded through entire algorithms, or deep mathematical theorems.

| File | Admits | Why expert guidance is needed |
|------|--------|------------------------------|
| **StackDFS.fst** | 0 | ✅ Full DFS correctness proven via final_postcondition_lemma |
| **CountingSort.Stable** | 2 | Stability: backward traversal preserves relative order. Permutation: each element placed once. |
| **RadixSort.Spec** | 1 | Permutation composition across d stable sorts |
| **RadixSort.MultiDigit** | 2 | Stability reasoning: stable_sort_preserves_order + stable_sort_preserves_sorted |
| **PartialSelect.Correctness** | 2 | Partition/quickselect specs admitted as axioms |
| **BST.Insert.Spec** | 3 | Mutually-recursive structural induction on array-based tree |
| **DFS.Spec** | 5 | CLRS Thms 22.7-22.8: parenthesis, reachability, white-path, cycle, topological sort |
| **DFS.WhitePath** | 3 | White path transitivity + DFS ancestor equivalence |
| **BFS.DistanceSpec** | 3 | L67: axiomatic. L236: hard direction (no shorter path). L251: combines both |
| **Kruskal.Spec** | 3 | Acyclicity preservation, spanning tree, MST optimality |
| **Kruskal.EdgeSorting** | 2 | Insertion sort stability: position tracking through swaps |
| **Kruskal.fst** | 1 | Union-find cycle detection ⟹ forest acyclicity |
| **Kruskal.Complexity** | 1 | Inner loop invariant restoration with complexity tracking |
| **MST.Spec** | 4 | Core MST theory: cycle characterization, cut-crossing, generic MST correctness |
| **Prim.Spec** | 1 | Spanning tree characterization |
| **BellmanFord.Spec** | 2 | L235: relaxation upper bound. L405: CLRS Lemma 24.2 (path relaxation) |
| **Dijkstra.TriIneq** | 1 | Triangle preservation needs Dijkstra invariant (processed=optimal) |
| **KMP.Complexity** | 7 | Amortized complexity: formal potential function |
| **ActivitySelection.Spec** | 2 | L176: ghost supremum. L420: full greedy optimality induction |
| **Huffman.Complete** | 2 | Multiset/permutation + CLRS Theorem 16.3 (Huffman optimality) |
| **VertexCover.Spec** | 1 | 2-approximation: ghost matching extraction |
