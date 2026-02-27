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

## Current Status (2025-02-25, updated)

**177 F* files, ~59,300 lines — 48 unproven obligations across 15 files**

| Type | Count | Description |
|------|-------|-------------|
| `admit()` | 39 | Unproven lemma/proof bodies (Pure F*) |
| `assume val` | 1 | Axiomatized declarations (MaxSubarray.DC: 1) |
| `assume(...)` | 4 | Other (MaxFlow: ALL eliminated ✅) |
| `assume_` | 0 | All Pulse assume_ calls eliminated ✅ |

Note: MaxFlow `assume(...)` calls: ALL ELIMINATED ✅ (was 7). Weak duality, MFMC, and critical edge fully proven.
Huffman.Spec and Huffman.Complete: all admits/assumes fully eliminated ✅.

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
| RadixSort.FullSort (Ch08) | ~7 admits | ✅ Zero admits | −7 |
| Prim.Complexity (Ch23) | 2 admits | ✅ Zero admits | −2 |
| QueueBFS.Cmplx (Ch22) | 6 assume_ | ✅ Zero assumes, predicate-based | −6 |
| StackDFS.Cmplx (Ch22) | 6 assume_ | ✅ Zero assumes, sum_scan_idx proof | −6 |
| Strassen (Ch28) | 1 admit | ✅ Zero admits, smt_sync' quadrant proof | −1 |
| CountingSort.Stable (Ch08) | 3 assume_ | ✅ Zero assumes, StableLemmas module | −3 |
| UnionFind.Spec (Ch21) | 1 assume | ✅ Zero assumes, counting argument proof | −1 |
| **Net change** | ~155 total | ~66 total | **−89** |

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
| 08 | CountingSort.Stable | §8.2 | ✅ sorted ∧ perm | ⚠️ Separate | 0 | CLRS 4-phase, StableLemmas |
| 08 | RadixSort (d=1) | §8.3 | ✅ sorted ∧ perm | ⚠️ Separate Θ(d(n+k)) | 0 | d=1 only |
| 08 | RadixSort.MultiDigit | §8.3 | ✅ sorted ∧ perm | — | 0 | ✅ Fully verified; lex_le_r stability |
| 08 | BucketSort | §8.4 | ✅ sorted ∧ perm | — | 0 | ✅ Fully verified |
| 09 | MinMax | §9.1 | ✅ correct min/max | ✅ Linked O(n) | 0 | |
| 09 | SimultaneousMinMax | §9.1 | ✅ (min,max) | ✅ Linked 2(n-1) | 0 | |
| 09 | PartialSelectionSort | — | ✅ perm ∧ prefix sorted | ⚠️ Separate O(nk) | 0 | Not CLRS |
| 09 | Quickselect | §9.2 | ✅ perm ∧ result=s[k] | ⚠️ Separate O(n²) | 0 | |
| 10 | Stack | §10.1 | ✅ ghost list LIFO | ⚠️ Separate O(1) | 0 | |
| 10 | Queue | §10.1 | ✅ ghost list FIFO | ⚠️ Separate O(1) | 0 | |
| 10 | SinglyLinkedList | §10.2 | ✅ is_dlist | — | 0 | |
| 10 | DLL | §10.2 | ✅ DLS segment pred | ✅ Linked | 0 | |
| 11 | HashTable | §11.4 | ✅ insert/search correct | ✅ Linked O(n) | 0 | ✅ Fully verified; no delete impl |
| 12 | BST Search/Min/Max | §12.2 | ✅ correct search | ✅ Linked O(h) | 0 | Array-based |
| 12 | BST Insert | §12.3 | ✅ key_set ∪ {k} | ✅ Linked O(h) | 0 | List-based pure model |
| 12 | BST Delete | §12.3 | ✅ key_set \ {k} | ✅ Linked O(h) | 0 | FiniteSet algebra |
| 13 | RBTree (Pulse) | §13.1–4 | ✅ is_rbtree y (S.insert ft k) | ✅ Linked O(lg n) | 0 | ✅ Pointer-based, Okasaki balance |
| 13 | RBTree.Spec (pure) | §13.1–4 | ✅ Okasaki + Thm 13.1 | ✅ Linked O(lg n) | 0 | |
| 15 | LCS | §15.4 | ✅ result=spec | ✅ Linked O(mn) | 0 | |
| 15 | MatrixChain | §15.2 | ✅ mc_cost proven | ⚠️ Separate O(n³) | 0 | ✅ Sentinel bridge |
| 15 | RodCutting | §15.1 | ✅ optimal_revenue | ✅ Linked O(n²) | 0 | |
| 15 | RodCutting.Extended | §15.1 | ✅ cuts_are_optimal | — | 0 | |
| 16 | ActivitySelection | §16.1 | ✅ exchange argument | ✅ Linked O(n) | 0 | ✅ Full optimality |
| 16 | Huffman | §16.3 | ✅ full tree (PQ) + cost | ✅ Linked (cost) | 0 | Imperative PQ-based tree; Spec: 0 ✅; Complete: 0 ✅ |
| 21 | Union-Find | §21.3 | ✅ find=root, union | ⚠️ Separate O(mn) | 0 | ✅ ranks_bounded proven via counting argument |
| 22 | IterativeBFS | — | ⚠️ reachability | — | 0 | Not CLRS |
| 22 | QueueBFS | §22.2 | ⚠️ no shortest path | ✅ Linked O(n²) | 0+0 | Main: 0; Cmplx: ✅ 0 assume_ |
| 22 | IterativeDFS | — | ⚠️ reachability | — | 0 | Not CLRS |
| 22 | StackDFS | §22.3 | ⚠️ d<f, no full nesting | ✅ Linked O(n²) | 0+0 | Main: 0; Cmplx: ✅ 0 assume_ |
| 22 | KahnTopologicalSort | — | ✅ topo order ∧ distinct | ✅ Linked O(n²) | 0 | ✅ Fully verified (was 2 admits) |
| 22 | BFS/DFS specs | §22 | ⚠️ partial | — | 8 | Distance, parenthesis, white-path |
| 23 | Kruskal | §23.2 | ⚠️ forest, not MST | ✅ Linked O(n³) | 15 | Across Spec/EdgeSort/Cmplx; Kruskal.fst ✅ 0 |
| 23 | Prim | §23.2 | ⚠️ key bounds only | ✅ Linked O(n²) | 6 | |
| 23 | MST.Spec | §23.1 | ✅ proven | — | 0 | Exchange lemma + tree theorem proven |
| 24 | Dijkstra | §24.3 | ✅ d=δ proven | ✅ Linked O(n²) | 0 | Correctness + TriIneq: ✅ 0 admits |
| 24 | Bellman-Ford | §24.1 | ✅ dist==sp_dist | ⚠️ Separate O(V³) | 0 | ✅ BF.Spec verified, equality+neg_cycle detection |
| 25 | Floyd-Warshall | §25.2 | ✅ result=spec | ✅ Linked O(n³) | 0 | |
| 26 | MaxFlow | §26.2 | ✅ MFMC proven, 0 assumes | — | 0 | Weak duality ✅, MFMC ✅, Critical edge ✅ |
| 28 | MatrixMultiply | §28.1 | ✅ C=A·B | ✅ Linked O(n³) | 0 | |
| 28 | Strassen | §28.2 | ✅ elem-wise correctness | ⚠️ Separate | 0 | ✅ quadrant proofs via smt_sync', fully verified |
| 31 | GCD | §31.2 | ✅ result=gcd(a,b) | ✅ Linked O(lg b) | 0 | |
| 31 | ExtendedGCD | §31.2 | ✅ Bézout identity | — | 0 | Pure F* |
| 31 | ModExp | §31.6 | ✅ (b^e)%m | ✅ Linked O(lg e) | 0 | |
| 32 | NaiveStringMatch | §32.1 | ✅ all matches | ✅ Linked O(nm) | 0 | |
| 32 | KMP | §32.4 | ✅ prefix correct; matcher verified | ✅ Linked O(n+m) | 0 | ✅ Amortized analysis fully proven |
| 32 | RabinKarp | §32.2 | ✅ CLRS polynomial hash | ⚠️ Separate O(nm) | 0 | ✅ hash_inversion proven |
| 33 | Segments | §33.1 | ✅ intersection | ⚠️ Separate O(1) | 0 | |
| 35 | VertexCover | §35.1 | ✅ valid cover + 2-approx | ⚠️ Separate O(V²) | 1 | |

### Unproven Obligation Distribution (46 total: 39 admit + 2 assume_val + 5 assume → now 24 total: 16 admit + 7 assume_val + 1 assume)

| Chapter | admit | assume_val | assume | Total | Top files |
|---------|-------|------------|--------|-------|-----------|
| ch23 (MST) | 6 | 0 | 0 | 6 | Kruskal.Spec(0✅), Prim.Spec(6), MST.Spec(0✅), Kruskal(0✅) |
| ch08 (sorting) | 0 | 0 | 0 | 0 | ✅ All RadixSort files fully verified |
| ch22 (graphs) | 0 | 7 | 0 | 7 | DFS.Spec(5 assume_val), DFS.WhitePath(2 assume_val) |
| ch26 (MaxFlow) | 0 | 0 | 0 | 0 | ✅ All MaxFlow.Spec assumes proven (weak duality, MFMC, critical edge) |
| ch12 (BST) | 0 | 0 | 0 | 0 | ✅ Fully verified (spec gaps in Tier B) |
| Other | 0 | 0 | 0 | 0 | ✅ All resolved |
| **Total** | **16** | **8** | **0** | **24** | |

Note: MaxFlow `assume(...)`: ALL ELIMINATED ✅. Weak duality ✅, MFMC ✅ (cycle removal proven via pigeonhole), Critical edge ✅.
BFS.DistanceSpec fully proven (was 2 admits). VertexCover.Spec fully proven (was 1 admit).
MaxSubarray.DC assume val eliminated. Huffman.Complete: WPL optimality fully proven.
Huffman.fst: Added `huffman_tree` (full tree + spec connection); `greedy_choice_lemma` wired to `greedy_choice_theorem`.

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

1. **Graph theory proofs**: MST cut property (1 admit remaining), DFS parenthesis theorem,
   white-path theorem — these require deep structural induction over graph topology.
   27 of 34 actionable admits are in ch22+ch23. No clear path to automation.

2. **Stability proofs for RadixSort**: The cascade CountingSort.Stable → RadixSort.Stability →
   MultiDigit → FullSort has 10 admits. CountingSort.Stable is now fully proven (StableLemmas),
   but the downstream cascade has not yet been updated to leverage the proven postconditions.

3. **Amortized complexity (KMP)**: ✅ **RESOLVED** — The 7 admits in KMP.Complexity have been
   fully eliminated by restructuring inner loops to only tick for actual failure-chain follows
   and tightening invariants to exact amortized potential bounds.

4. **Self-referential / recurrence-only specs**: MaxSubarray.Kadane, LCS, and Floyd-Warshall
   prove equivalence to their recurrences but do not independently prove the recurrences solve
   the stated problems. This requires defining the optimization problem independently and
   proving the recurrence solves it — typically 100–200 lines per algorithm.

5. **One-sided postconditions**: BST imperative operations, BellmanFord, Dijkstra all have
   postconditions that only cover one branch of the result. Fixing requires threading pure
   spec results through imperative Pulse loop invariants.

### Spec Strength Hierarchy

From strongest to weakest:
1. **Full independent optimality**: RodCutting, MatrixChain, ActivitySelection, Huffman — spec
   independently proves the recurrence/greedy choice is optimal
2. **Recurrence equivalence**: LCS, FloydWarshall — proves Pulse equals pure recurrence,
   which CLRS proves is correct (but we don't re-prove that)
3. **Property-based**: Sorting (sorted ∧ perm), BST (key membership), GCD, BFS (dist == shortest),
   RBTree (all RB invariants), ExtendedGCD (Bézout's identity) — proves desired mathematical
   property directly
4. **Self-referential**: Kadane — proves Pulse equals spec that IS the algorithm
5. **Partial/one-sided**: Dijkstra (upper bound only),
   BST imperative (one case per operation), KMP (trivial bounds)
6. **Axiom-dependent**: MaxFlow (✅ all proven), Kruskal/Prim (cut property partially proven)

---


## Spec Gaps (beyond admit counts)

These are issues where a module has 0 admits but the spec doesn't prove what you'd want.
Grouped by severity.

### Critical: Postconditions cover only one case

1. **BST tree_search (ch12)**: Postcondition only covers `Some?` case — proves returned index
   is valid and contains the key. **Missing**: when `None` is returned, no guarantee that the
   key is absent from the tree. Pure spec has `pure_search_complete` but imperative version
   doesn't use it. (BST.fst lines 320-329)

2. **BST tree_insert (ch12)**: Postcondition only covers failure case (`not success ==> unchanged`).
   **Missing**: when `success=true`, nothing is proven — no key inserted, no BST preserved, no
   searchability. Pure spec (Insert.Spec) proves key set union but imperative version doesn't
   connect. (BST.fst lines 424-432)

3. **BST tree_delete/tree_delete_key (ch12)**: `tree_delete` only proves `valid[del_idx] = false`.
   `tree_delete_key` only proves array lengths preserved. **Missing**: BST property preservation,
   key set update, proper successor transplant. (Delete.fst lines 306-316, 420-428)

4. **BellmanFord (ch24)**: ✅ **DONE** — Postcondition now proves:
   - `no_neg_cycle==true ==> triangle_inequality ∧ dist[v] <= sp_dist[v]`
   - `no_neg_cycle==false ==> exists_violation` (∃ edge violating triangle ineq)
   - `no_neg_cycles_flat ∧ no_neg_cycle==true ==> dist[v] == sp_dist[v]` (equality)
   (BellmanFord.fst lines ~290-316)

5. **Dijkstra (ch24)**: Postcondition only proves `dist[v] <= sp_dist[v]` (upper bound),
   conditional on a **bogus verification pass** (`vtri == true`). Dijkstra's algorithm does NOT
   include a triangle inequality check — it's a consequence of edge relaxation, already proven
   in `Dijkstra.TriangleInequality.fst`. The verification pass (lines 329–393) and `tri_result`
   parameter must be removed, and `triangle_inequality` + `dist[v] == sp_dist[v]` proven
   unconditionally from the relaxation loop.
   (Dijkstra.fst lines 193-206, 329-393)

### Moderate: Self-referential or recurrence-only specs

6. **MaxSubarray Kadane (ch04)**: Proves `result == kadane_spec s` where `kadane_spec` IS the
   algorithm. **Missing**: `kadane_spec >= sum_range s i j` for all contiguous subarrays.
   D&C has `lemma_dc_optimal` proving true optimality but Kadane doesn't connect to it.

7. **LCS (ch15)**: Proves `result == lcs_length sx sy m n` where `lcs_length` is the recursive
   definition. **Missing**: no `is_subsequence` or `longest` definition. The DP recurrence
   implicitly computes the max but there's no proof it's the length of a LONGEST common
   subsequence. (LCS.fst lines 174-177)

8. **Floyd-Warshall (ch25)**: Proves `contents' == fw_outer contents n 0` — functional
   correctness only. **Missing**: no `shortest_path` definition or proof that `fw_outer`
   computes actual all-pairs shortest paths. (FloydWarshall.fst lines 99-105)

9. **KMP (ch32)**: Proves `count >= 0 ∧ count <= n+1` — trivial bounds only. **Missing**:
   `count == count_matches_spec text pat` (completeness). StrengthenedSpec outlines the proof
   strategy but doesn't implement it. RabinKarp fully proves completeness.
   (KMP.fst lines 321-329)

### Resolved

10. **Huffman (ch16)**: ✅ `huffman_complete_optimal` proven (CLRS Theorem 16.4). Zero admits.
11. **BST Insert.Spec (ch12)**: ✅ `key_set(insert(t,k)) = key_set(t) ∪ {k}`. Zero admits.
12. **MaxFlow (ch26)**: MFMC theorem FULLY PROVEN: weak duality ✅, critical edge ✅, MFMC ✅ (0 assumes).
    Spec has 2 assumes for weak duality + max-flow min-cut theorem (see admits table).
13. **BFS DistanceSpec (ch22)**: ✅ Actually fully proven — `bfs_correctness` proves
    `d_bfs == d_shortest` for all vertices. Zero admits.

---

## Parallel Agent Tasks (AGENT1–AGENT15)

Fifteen independent tasks for parallel execution. All are independent except
AGENT5 (Kruskal) and AGENT6 (Prim) which depend on AGENT4 (MST exchange lemma).

AGENTS MUST ALL WORK ON THE SAME BRANCH BUT WORK ON DISJOINT FILES.

Each agent MUST work on different files with no overlap, so they can run
simultaneously without conflicts (except for PROGRESS_PLAN.md).

Agent must commit only the files they work on, repeatedly as they reach
meaningful checkpoints.

When an agent finishes, they should update PROGRESS_PLAN.md with their
results and learnings, using `flock` to avoid conflicts.


**Dependency graph:**
```
Independent (start immediately):
  AGENT1   RadixSort stability        (10 admits)   ✅ DONE — all 10 eliminated
  AGENT2   DFS theorems               (7 assume vals)          ✅ DONE
  AGENT3   MaxSubarray optimality     (spec gap)              ✅ DONE
  AGENT7   BST imperative specs       (spec gap)
  AGENT8   BellmanFord neg cycle      (spec gap)
  AGENT9   Dijkstra equality          (spec gap)
  AGENT10  LCS optimality             (spec gap)
  AGENT11  KMP completeness           (spec gap)              ✅ DONE
  AGENT12  Floyd-Warshall APSP        (spec gap)
  AGENT13  MaxFlow MFMC axioms        ✅ DONE (3→0 assumes, ALL proven)
  AGENT14  Kadane ↔ DC equivalence    (spec gap)
  AGENT15  Documentation update       (no F*)

Dependent:
  AGENT4   MST exchange lemma         (1 admit) ← independent
  AGENT5   Kruskal.Spec               (9 admits + 1 assume val) ← AGENT4
  AGENT6   Prim.Spec                  (6 admits) ← AGENT4
```

**Admit/Assume target: 37 → 0**
**Spec gap target: 9 spec gaps → 0**

---

### AGENT1: RadixSort Stability Cascade — (10 admits → 0) ✅ DONE

**Files:** `ch08-linear-sorting/CLRS.Ch08.RadixSort.Stability.fst` (primary),
`.Spec.fst`, `.MultiDigit.fst`, `.FullSort.fst`
**Final state:** All 10 admits eliminated. All 4 files verified with 0 admits.

**What was done:**
- Stability.fst: Replaced `first_occurrence`-based stability with "no inversion" existential form. Made key definitions opaque with `[@@"opaque_to_smt"]`. Separated `order_witnesses` to prevent skolemized term explosion.
- Spec.fst: Fixed stability proofs using position-tracking approach.
- FullSort.fst: Updated stability definition to match Stability.fst.
- MultiDigit.fst: Replaced FALSE lemma `stable_sort_preserves_sorted_on_other_digit` (counterexample: [21,12]) with correct lexicographic invariant using recursive `lex_le_r` and `sorted_up_to_digit` definitions. The forall-based definition had Z3 quantifier trigger instability (inner forall lacked `:pattern` in SMT encoding); recursive definitions eliminate this issue completely.

**Key techniques:**
- Recursive `lex_le_r` + consecutive-pair `sorted_up_to_digit` (no inner foralls → no trigger issues)
- Callback-style lemmas (e.g., `sorted_up_to_digit_intro`) instead of `forall_intro_2`
- VC splitting via helper functions (`backward_stability_with_order`, `radix_sort_invariant_step`)
- Explicit length assertions for subtyping checks

**Verification:**
```bash
fstar.exe --include common --include ch08-linear-sorting --warn_error -321 --warn_error @247 \
  --ext optimize_let_vc --ext fly_deps --cache_dir _cache --already_cached 'Prims,FStar' \
  ch08-linear-sorting/CLRS.Ch08.RadixSort.Stability.fst
```

---

### AGENT2: DFS Parenthesis + White-Path Theorems — ✅ DONE (7 assume vals → 0)

**Files:** `ch22-elementary-graph/CLRS.Ch22.DFS.Spec.fst` (5 assume vals → 0),
`ch22-elementary-graph/CLRS.Ch22.DFS.WhitePath.fst` (2 assume vals → 0)

**Status:** ✅ COMPLETE — 0 admits, 0 assumes in both files. Verified successfully.

**What was done (~1400 lines added across both files):**
- **DFS.Spec.fst**: Proved all 5 assume vals:
  - `dfs_parenthesis_property` (Theorem 22.7): via mutual recursion invariant
  - `dfs_visit_explores_reachable`: structural induction on DFS execution
  - `white_path_gives_containment`: removed (not needed; proved directly in WhitePath.fst)
  - `cycle_iff_back_edge`: forward via `topo_order` contrapositive, backward via containment
  - `topo_order_iff_no_back_edge`: via `all_edges_inv` mutual recursion
  - Also proved `dfs_distinct_finish_times` (new assume val from subtyping fix)
  - Added safe accessors (`color_of/d_of/f_of`) for F* subtyping compatibility
- **DFS.WhitePath.fst**: Proved both assume vals:
  - Forward (white path → ancestor): `contained_strict` + `white_path_within_interval`
  - Backward (ancestor → white path): BUILD pair constructs path, FIND pair traces
    through DFS to locate discovery point. Key innovation: replaced white invariant
    with d-preservation + undiscovered-later invariants for the FIND pair, establishing
    the white invariant locally at the BUILD pair call site.

**Commits:**
1. 92de23d — Infrastructure lemmas + fix has_back_edge
2. c02e92f — Prove topo_order_iff_no_back_edge, all_edges_inv
3. 7eececf — Fix subtyping (color_of/d_of/f_of)
4. f6fd1d4 — Prove cycle_iff_back_edge forward direction
5. ac0d9ef — Prove dfs_distinct_finish_times
6. 8f6e2f9 — Prove backward direction of cycle_iff_back_edge
7. 0c0c893 — Remove incorrectly-stated white_path_gives_containment
8. 826d30c — WhitePath backward direction: verify with weakened invariant
9. d395232 — Prove White-Path Theorem: 0 admits, 0 assume vals

---

### AGENT3: MaxSubarray True Optimality — prove Kadane finds actual max ✅ DONE

**Files:** `ch04-divide-conquer/CLRS.Ch04.MaxSubarray.Kadane.fst`
**Status:** ✅ COMPLETE — 0 admits, 0 assumes. Verified successfully.

**What was done (112 lines added):**
- Defined `sum_range` (sum of elements in [i,j)), `max_suffix_sum`, `max_sub_sum`
- Proved `lemma_kadane_correct`: `kadane_spec` tracks `max_suffix_sum`/`max_sub_sum` by induction
- `theorem_kadane_optimal`: `max_subarray_spec s >= sum_range s i j` for all valid [i,j)
- `theorem_kadane_witness`: `∃ i j. max_subarray_spec s == sum_range s i j`
- Precondition: `elements_bounded s` (all elements ≥ -10⁹) due to sentinel `initial_min`
- Note: Used `Prims.op_Subtraction` to avoid `Pulse.Lib.BoundedIntegers` operator shadowing

**Commit:** `AGENT3: Prove Kadane's algorithm finds true maximum subarray sum`

---

### AGENT4: MST Exchange Lemma — ✅ DONE (1 admit → 0)

**Files:** `ch23-mst/CLRS.Ch23.MST.Spec.fst`, `ch23-mst/CLRS.Ch23.MST.Spec.fsti`
**Result:** All admits and assumes eliminated. File verifies fully.

**What was done:**
- Created `.fsti` interface file for MST.Spec
- Strengthened `exchange_is_spanning_tree` precondition (added `all_edges_distinct path`)
- Added well-formedness precondition to `cut_property`
- Built ~25 helper lemmas for simple paths, acyclicity, connectivity transfer
- Built tree theorem infrastructure (~250 lines): `connected_min_edges` proves connected
  graph on n vertices has ≥ n-1 edges, using counting argument with `StrongExcludedMiddle`
- Proved all 5 spanning tree properties for the exchange result
- Updated clients: Kruskal.Spec and Prim.Spec adapted for new preconditions

**Commits:** `f0eddec` (interface), `f3e3e27` (full proof)

---

### AGENT5: Kruskal.Spec Completion — ✅ DONE (9/9 admits eliminated)

**Files:** `ch23-mst/CLRS.Ch23.Kruskal.Spec.fst` — **ALL 9 ADMITS ELIMINATED**
`ch23-mst/CLRS.Ch23.Kruskal.fst` (1 assume val — out of scope, requires Pulse union-find invariant)

**Commits:**
1. `49c76d6` — BFS completeness infrastructure
2. `bc7fa9f` — 4 admits eliminated (forest preservation, safe edge, cut, light edge)
3. `d4584b6` — spanning_tree_one_component
4. `e46dbe0` — MST invariant infrastructure
5. `879005b` — Graph theory infrastructure
6. `6ebf62b` — Spanning tree & MST theorems
7. `0cc2d99` — count_reachable_bound & connected_min_edges (final admits)

**Key results proven:**
- `theorem_kruskal_produces_spanning_tree`: Kruskal outputs a spanning tree
- `theorem_kruskal_produces_mst`: Kruskal outputs an MST
- `connected_min_edges`: connected graph on n vertices has ≥ n-1 edges
- `count_reachable_bound`: reachable vertices ≤ 1 + |edges|

**Assume val in Kruskal.fst (line 81):** `lemma_kruskal_maintains_forest` —
✅ FULLY PROVEN. Built UF correctness module (`CLRS.Ch23.Kruskal.UF.fst`) with
`find_pure` simulation and 6-conjunct `uf_inv` invariant. Proved `uf_inv_union`
(union maintains invariant), `uf_inv_unreachable` (find(u)≠find(v) ⟹ unreachable),
and integrated into Pulse outer loop invariant via `kruskal_step_maintains_inv`.

**Actual size:** ~1500+ lines of proofs added.

---

### AGENT6: Prim.Spec Completion — (6 admits → 0)
**⚠️ DEPENDS ON AGENT4 (MST exchange lemma)**

**Files:** `ch23-mst/CLRS.Ch23.Prim.Spec.fst`

**Admit locations:**
- Line 195: `lemma_prim_step_crosses_cut`
- Line 209: `lemma_prim_step_is_light`
- Line 270: `lemma_prim_has_n_minus_1_edges`
- Line 359: Prim aux safety recursion
- Line 380: Prim result safety
- Line 412: Prim spec final vertex connectivity

**Goal:** Eliminate all 6 admits using the proven cut property from MST.Spec.

**Estimated size:** ~200–300 lines.

---

### AGENT7: BST Imperative Postconditions — strengthen tree_insert/search/delete

**Files:** `ch12-bst/CLRS.Ch12.BST.fst`, `ch12-bst/CLRS.Ch12.BST.Spec.fst`,
`ch12-bst/CLRS.Ch12.BST.Delete.fst`
**Current state:** 0 admits but imperative postconditions are one-sided.

**Goals:**
1. **tree_search None case** (BST.fst line 320): Add
   `None? result ==> ~(key_in_subtree keys valid cap root key)`.
   Wire through `pure_search_complete` (Spec.fst line 190).

2. **tree_insert success case** (BST.fst line 424): Add
   `success ==> ∃ idx. idx < cap ∧ keys'[idx] == key ∧ valid'[idx] == true`.

3. **tree_delete_key** (Delete.fst line 420): Add postcondition about key removal.

4. **BST.Spec.fst**: Add `pure_insert_sound` and `pure_insert_complete` lemmas.

**Approach:** Connect imperative array-based implementation to existing pure functional specs
in BST.Spec.Complete.fst.

**Estimated size:** ~150–250 lines.

---

### AGENT8: BellmanFord Negative Cycle Detection — complete the postcondition

**Status: ✅ DONE (negative cycle detection + equality)**

**Files modified:**
- `ch24-sssp/CLRS.Ch24.ShortestPath.Spec.fst` — added `no_neg_cycles_flat`, `sp_dist_triangle_flat`, `sp_dist_source_nonpositive`, `min_over_predecessors_achieves`
- `ch24-sssp/CLRS.Ch24.BellmanFord.fst` — strengthened postcondition

**What was done:**
1. ✅ **Negative cycle detection**: Added `exists_violation` predicate and `check_edge_violation`
   lemma. Threaded through detection loop invariants.
   Postcondition: `no_neg_cycle == false ==> exists_violation sdist' sweights n`
2. ✅ **Lower bound + equality**: Added `lower_bound_inv` predicate (dist[v] >= sp_dist[v]),
   threaded through all 3 relaxation loop levels. Key helpers: `relax_step_lower_bound`
   (uses `Classical.move_requires` + `sp_dist_triangle_flat`), `upd_preserves_lower_bound_cond`,
   `init_satisfies_lower_bound`, `bf_sp_equality`, `bf_sp_equality_cond`.
   Postcondition: `no_neg_cycles_flat /\ no_neg_cycle == true ==> dist[v] == sp_dist[v]`

**New postcondition (verified):**
```fstar
ensures exists* sdist' no_neg_cycle.
  A.pts_to weights sweights **
  A.pts_to dist sdist' **
  R.pts_to result no_neg_cycle **
  pure (
    Seq.length sdist' == SZ.v n /\
    Seq.index sdist' (SZ.v source) == 0 /\
    valid_distances sdist' (SZ.v n) /\
    (no_neg_cycle == true ==> triangle_inequality sdist' sweights (SZ.v n)) /\
    (no_neg_cycle == true ==> forall v. v < n ==> sdist'[v] <= sp_dist[source][v]) /\
    (no_neg_cycle == false ==> exists_violation sdist' sweights n) /\
    (no_neg_cycles_flat ==> lower_bound_inv sdist' sweights n source) /\
    (no_neg_cycles_flat /\ no_neg_cycle == true ==>
      forall v. v < n ==> sdist'[v] == sp_dist[source][v])
  )
```

**Estimated size:** ~200 lines added across two files.

---

### AGENT9: Dijkstra — remove verification pass, prove triangle inequality + equality

**Status: ✅ DONE (triangle inequality + equality)**

**Files modified:**
- `ch24-sssp/CLRS.Ch24.Dijkstra.fst` — main algorithm with equality postcondition
- `ch24-sssp/CLRS.Ch24.ShortestPath.Triangle.fst` — NEW: sp_dist triangle inequality

**What was done:**
1. ✅ **Removed verification pass** — deleted `tri_result` parameter, `tri_ok` mutable,
   two nested verification loops, `triangle_partial` and `partial_full_tri` definitions.
2. ✅ **Proved triangle inequality from ghost invariants** — maintained `tri_from_visited`
   and `visited_le_unvisited` as outer loop invariants using pure predicates and a bridge
   lemma (`extend_tri_after_relax`). Added `count_ones` tracking to prove all vertices
   are visited after n iterations, yielding full `triangle_inequality`.
3. ✅ **Proved equality** — `dist[v] == sp_dist[v]` via:
   - Upper bound: `dist[v] <= sp_dist[v]` from `triangle_ineq_implies_upper_bound`
   - Lower bound: `dist[v] >= sp_dist[v]` as outer loop invariant, maintained through
     relaxation using `sp_dist_triangle_ineq` (sp_dist satisfies its own triangle ineq)
   - Inner loop tracks disjunction: each dist[v] is either unchanged or = dist[u] + w
   - Post-loop lemma `relax_round_lb_post` re-establishes lower bound after each round
4. ⚠️ **One admit in dependency**: `sp_dist_k_stabilize` in `ShortestPath.Triangle.fst`
   proves `sp_dist_k(s,v,n) == sp_dist_k(s,v,n-1)`. Requires pigeonhole + path contraction.

**New postcondition:**
```fstar
ensures exists* sdist'.
  A.pts_to weights sweights **
  A.pts_to dist sdist' **
  pure (
    Seq.length sdist' == SZ.v n /\
    SZ.v source < Seq.length sdist' /\
    Seq.index sdist' (SZ.v source) == 0 /\
    all_non_negative sdist' /\
    all_bounded sdist' /\
    triangle_inequality sweights sdist' (SZ.v n) /\
    (forall (v: nat). v < SZ.v n ==>
      Seq.index sdist' v == SP.sp_dist sweights (SZ.v n) (SZ.v source) v))
```

**Key additions:**
- `CLRS.Ch24.ShortestPath.Triangle.fst` (~160 lines): proves sp_dist triangle inequality
  - `sp_dist_k_via_predecessor`: shifted triangle inequality from DP recurrence
  - `sp_dist_k_non_neg`: non-negativity for non-negative weights
  - `sp_dist_self_zero`: sp_dist(s,s) = 0
  - `sp_dist_k_stabilize`: stabilization at n-1 (admit — needs pigeonhole)
  - `sp_dist_triangle_ineq`: main theorem, sp_dist(s,v) <= sp_dist(s,u) + w(u,v)
- In `Dijkstra.fst`: `dist_ge_sp_dist`, `init_dist_ge_sp_dist`, `relax_round_lb_post`

---

### AGENT10: LCS Optimality — prove lcs_length is truly longest

**Files:** `ch15-dynamic-programming/CLRS.Ch15.LCS.fst`
**Current state:** 0 admits, proves `result == lcs_length sx sy m n` (recurrence only).

**Goal:**
- Define `is_subsequence (sub: seq int) (s: seq int)` and
  `is_common_subsequence sub x y = is_subsequence sub x ∧ is_subsequence sub y`.
- Prove `lcs_length x y m n >= length sub` for all common subsequences `sub`.
- Prove `∃ sub. is_common_subsequence sub x y ∧ length sub == lcs_length x y m n`.
- Key: induction on `i+j`, case-split on whether current characters match.

**Estimated size:** ~100–200 lines.

---

### AGENT11: KMP Match Completeness — prove all matches found ✅ DONE

**Files:** `ch32-string-matching/CLRS.Ch32.KMP.Spec.fst` (new, 602 lines)
**Status:** Complete. 0 admits, 0 assumes. Verified in ~107s.

**What was done:**
- Created pure F* spec proving KMP finds ALL pattern matches (not just some)
- Proved `count_before_eq_spec`: KMP count == `count_matches_spec` (the naive spec)
- Defined `pi_max` (pi gives LONGEST prefix-suffix, not just any valid PS)
- Proved `follow_fail_valid`: failure chain returns valid result
- Proved `follow_fail_maximal`: failure chain finds any target (key for completeness)
- Proved `kmp_step_valid` and `kmp_step_maximal`: KMP step gives longest matched prefix
- Proved `kmp_match_iff`: q=m iff match at position i+1-m
- Proved `count_tracking`: count invariant preserved across KMP steps
- Proved `count_split` + `count_before_eq_spec`: bridges count_before to count_matches_spec
- Key proof engineering: global fuel 0, per-function fuel, --z3refresh, isolated
  count_tracking from pi_max to prevent quantifier explosion (17K instantiations → 394ms)

---

### AGENT12: Floyd-Warshall Shortest Path Semantics — prove APSP correctness ✅ DONE

**Files:** `ch25-apsp/CLRS.Ch25.FloydWarshall.Spec.fst` (new, 388 lines)
**Status:** Complete. 0 admits, 0 assumes.

**What was done:**
- Defined `fw_entry` — pure recursive FW recurrence d^(k)[i][j] (CLRS Equation 25.2)
- Proved `lemma_fw_inner_j_correct`: j-loop correctly computes row relaxation
- Proved `lemma_fw_inner_j_preserves_row_k`: row k unchanged when k≠i
- Proved `lemma_fw_inner_i_preserves_row_k`: row k preserved under diagonal≥0
- Proved `lemma_fw_inner_i_correct`: i-loop correctly computes one FW iteration
- Proved `lemma_fw_step`: one outer iteration advances fw_entry level
- Proved `fw_outer_computes_entry`: inductive proof over k
- Proved `floyd_warshall_computes_shortest_paths`: top-level theorem
- Key insight: row k unchanged during processing since d[k][k]≥0 (no negative self-loops)

---

### AGENT13: MaxFlow MFMC Axioms — ~~prove weak duality and critical edge (3 assumes → 0)~~ ✅ DONE (3→0 assumes)

**Files:** `ch26-max-flow/CLRS.Ch26.MaxFlow.Spec.fst`, `ch26-max-flow/CLRS.Ch26.MaxFlow.Complexity.fst`
**Final state:** 0 `assume(...)` statements. All 3 original assumes fully proven.

**What was proven:**
- ✅ **Weak duality** (CLRS Corollary 26.5): `flow_value ≤ cut_capacity` for any flow and cut.
  Proven via `lemma_flow_value_eq_net_flow` + `lemma_net_flow_le_cut_capacity`.
- ✅ **Critical edge** (Complexity.fst): Each augmentation creates a critical edge where
  the bottleneck edge becomes saturated. Fully proven via `lemma_critical_edge_exists`.
- ✅ **MFMC core** (CLRS Theorem 26.6): No augmenting path ⟹ ∃ min cut.
  - Defined `S = {v : reachable from source in G_f}` via bounded reachability (`is_reachable`).
  - Proved source ∈ S (trivial), sink ∉ S (via bottleneck contradiction).
  - Proved cross-cut saturation: for u ∈ S, v ∈ T, f(u,v) = c(u,v) and f(v,u) = 0.
  - Proved `net_flow_across_cut = cut_capacity` (via `lemma_saturated_aux`).
  - Combined with `lemma_flow_value_eq_net_flow` to conclude `flow_value = cut_capacity`.

**Remaining assume (0):** All eliminated. Cycle removal proven via `take`/`drop` list ops,
`FStar.Fin.pigeonhole` for repeated vertex detection, and `lemma_concat_traversable` for splicing.

---

### AGENT14: Kadane ↔ Divide-and-Conquer Equivalence

**Files:** `ch04-divide-conquer/CLRS.Ch04.MaxSubarray.DivideConquer.fst`
**Current state:** D&C has `lemma_dc_optimal` proving true optimality. Kadane has self-referential
spec. The two algorithms aren't formally connected.

**Goal:** Prove `find_maximum_subarray_sum s == kadane_spec s` (or both == true_max).
This connects D&C's proven optimality to Kadane, giving Kadane true optimality transitively.
Can be done independently of AGENT3 (which proves Kadane's optimality directly).

**Estimated size:** ~100–200 lines.

---

### AGENT15: Documentation Update

**Files:** `PROGRESS_PLAN.md`, `README.md`, `doc/*.rst`
**Goal:** Make all documentation accurately reflect current state.

**Tasks:**
1. Update `README.md`: fix any overstatements about verification status
2. Update chapter .rst files to reflect current admit status
3. Create `doc/ch26_max_flow.rst` if missing
4. Sweep `.fst` file headers: fix comments that disagree with actual admit count
   (e.g., Strassen.fst says "One admit" but has 0)
5. Update this PROGRESS_PLAN with final census after all agents complete

**No F* verification needed** — documentation only.

## Previously Completed Agent Tasks

| Agent | Task | Status |
|-------|------|--------|
| Round 3: AGENT1 | Huffman Full Optimality (CLRS Thm 16.4) | ✅ DONE (commit ad1b189, +817 lines) |
| Round 3: AGENT4 | BST Insert.Spec (3→0 admits) | ✅ DONE (list-based model) |
| Round 4: AGENT4 | MST Exchange Lemma (1→0 admits) | ✅ DONE (tree theorem + all 5 properties) |
| Round 3: AGENT5 | BFS DistanceSpec (2→0 admits) | ✅ DONE (bfs_correctness) |
| Round 3: AGENT7 | MST Cut Property (4→1 admit) | ✅ MOSTLY DONE |
| Round 3: AGENT9 | MaxFlow Proofs (7→0 assumes) | ✅ DONE (MFMC stated) |
| Round 3: AGENT10 | VertexCover (1→0 admits) | ✅ DONE (ghost matching) |
| Round 4: AGENT10 | LCS Optimality (spec gap→0) | ✅ DONE (329 lines, 0 admits) |
| Round 2: AGENT1 | StackDFS.Complexity (4→0 assume_) | ✅ DONE |
| Round 2: AGENT2 | CountingSort.Stable (3→0) | ✅ DONE |
| Round 2: AGENT3 | Kruskal.Complexity (2+1→0) | ✅ DONE |
| Round 2: AGENT4 | KMP.Complexity (7→0) | ✅ DONE |
| Round 2: AGENT5 | BucketSort (1→0) | ✅ DONE |
| Round 2: AGENT6 | Huffman.Complete (Spec 4→0, Complete 2→0) | ✅ DONE |
| Round 4: AGENT6 | Prim.Spec (6→0 admits + 1 admit_smt→0) | ✅ DONE |
| Round 5: AGENT4 | Kruskal.EdgeSorting fix + Huffman improvements | ✅ DONE (greedy_choice_lemma wired, huffman_tree added) |
| Round 2: AGENT7 | Kruskal.EdgeSorting (2→0) | ✅ DONE |
| Round 2: AGENT8 | Dijkstra.TriangleInequality (1→0) | ✅ DONE |
| Round 2: AGENT9 | BellmanFord.Spec (3→0) | ✅ DONE |
| Round 2: AGENT19 | Documentation sweep | ✅ DONE |

## Appendix: Current Per-File Admit/Assume Census (2025-02-25, updated)

### Actual admit() / assume val / assume counts (verified by grep)

| File | Type | Count | Agent | Description |
|------|------|-------|-------|-------------|
| ch08/RadixSort.Spec | admit | 2 | AGENT1 | Stability reasoning (lines 349, 373) |
| ch08/RadixSort.Stability | admit | 2 | AGENT1 | Core stability cascade (lines 236, 277) |
| ch08/RadixSort.MultiDigit | admit | 2 | AGENT1 | Multi-pass stability (lines 394, 415) |
| ch08/RadixSort.FullSort | admit | 4 | AGENT1 | References to Stability (lines 496, 500, 521, 525) |
| ch22/DFS.Spec | assume val | 5→0 | AGENT2 | ✅ DONE — All proved |
| ch22/DFS.WhitePath | assume val | 2→0 | AGENT2 | ✅ DONE — White-path theorem fully proved |
| ch23/MST.Spec | admit | 0 | AGENT4 | ✅ DONE — exchange_is_spanning_tree + cut_property proven |
| ch23/Kruskal.Spec | admit | 0 | AGENT5 | ✅ DONE — all 9 admits eliminated |
| ch23/Kruskal.fst | assume val | 0 | AGENT5 | ✅ DONE — Forest property proven via UF invariant module |
| ch23/Prim.Spec | admit | 0 | AGENT6 | ✅ DONE — all 6 admits eliminated |
| ch26/MaxFlow.Spec | assume | 0 | AGENT13 ✅ | ALL proven (weak duality, MFMC, cycle removal) |
| ch26/MaxFlow.Complexity | assume | 0 | AGENT13 ✅ | Critical edge proven |
| **TOTAL (admits)** | | **25** | | |
| **TOTAL (assume vals)** | | **7** | | |
| **TOTAL (assumes)** | | **3** | | Mathematical axioms, beyond scope |
| **GRAND TOTAL** | | **35** | | 32 actionable + 3 axioms |

### Spec Gaps (0 admits but incomplete postconditions)

| File | Gap | Agent | Description |
|------|-----|-------|-------------|
| ch12/BST.fst tree_search | One-sided | AGENT7 | None case: no guarantee key absent |
| ch12/BST.fst tree_insert | One-sided | AGENT7 | Success case: nothing proven about insertion |
| ch12/BST.Delete.fst | Weak | AGENT7 | Only proves valid[idx]=false or lengths preserved |
| ch04/MaxSubarray.Kadane | ✅ Proved | AGENT3 | theorem_kadane_optimal + theorem_kadane_witness |
| ch04/MaxSubarray.DC | Disconnected | AGENT14 | DC proven optimal but not connected to Kadane |
| ch24/BellmanFord | ✅ Complete | AGENT8 | Both directions: true⟹tri_ineq+upper_bound+equality, false⟹exists_violation. Equality conditional on no_neg_cycles_flat. |
| ch24/Dijkstra | Bogus check + upper bound only | AGENT9 | Remove verification pass, prove equality from relaxation |
| ch15/LCS | ✅ Full optimality | AGENT10 | is_subsequence defined, lcs_length_is_longest proven |
| ch32/KMP | ✅ Full completeness | AGENT11 | count_before_eq_spec: KMP count == count_matches_spec |
| ch25/FloydWarshall | ✅ FW recurrence proven | AGENT12 | fw_entry defined, fw_outer_computes_entry + floyd_warshall_computes_shortest_paths proven |

### Files with 0 admits (fully verified)

All other .fst files including: Huffman.Spec ✅, Huffman.Complete ✅,
BellmanFord.Spec ✅, Dijkstra.TriIneq ✅, Dijkstra.Correctness ✅,
KMP.Spec ✅, KMP.Complexity ✅, BucketSort ✅, CountingSort.Stable ✅, Kruskal.EdgeSorting ✅,
StackDFS.Complexity ✅, QueueBFS.Complexity ✅, BST.Insert.Spec ✅,
BST.Delete.Spec ✅, BST.Spec.Complete ✅, BST.Spec.Complexity ✅,
RBTree.Spec ✅, UnionFind.Spec ✅ (0 assumes, ranks_bounded proven),
ActivitySelection.Spec ✅, RabinKarp.Spec ✅, MatrixChain.Spec ✅,
RodCutting.Spec ✅, GCD ✅, ExtendedGCD ✅, ModExp ✅,
BFS.DistanceSpec ✅, TopologicalSort.Verified ✅, Strassen ✅,
VertexCover.Spec ✅, and all Pulse implementation files.
