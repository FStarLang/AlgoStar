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
| `assume val` | 2 | Axiomatized declarations (MaxSubarray.DC: 1, Kruskal: 1) |
| `assume(...)` | 7 | MaxFlow Spec/Proofs/Complexity |
| `assume_` | 0 | All Pulse assume_ calls eliminated ✅ |

Note: MaxFlow `assume(...)` calls (7) are in stub/axiom files, now counted above for completeness.
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
| RadixSort.FullSort (Ch08) | ~7 admits | 4 admits remaining | −3 |
| Prim.Complexity (Ch23) | 2 admits | ✅ Zero admits | −2 |
| QueueBFS.Cmplx (Ch22) | 6 assume_ | ✅ Zero assumes, predicate-based | −6 |
| StackDFS.Cmplx (Ch22) | 6 assume_ | ✅ Zero assumes, sum_scan_idx proof | −6 |
| Strassen (Ch28) | 1 admit | ✅ Zero admits, smt_sync' quadrant proof | −1 |
| CountingSort.Stable (Ch08) | 3 assume_ | ✅ Zero assumes, StableLemmas module | −3 |
| **Net change** | ~155 total | ~67 total | **−88** |

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
| 08 | RadixSort.MultiDigit | §8.3 | ⚠️ partial | — | 10 | Pure F*; stability admits |
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
| 16 | Huffman | §16.3 | ⚠️ cost only | ✅ Linked (cost) | 0 | Spec: 0 ✅; Complete: 0 ✅ |
| 21 | Union-Find | §21.3 | ✅ find=root, union | ⚠️ Separate O(mn) | 1 assume | FullCompress available |
| 22 | IterativeBFS | — | ⚠️ reachability | — | 0 | Not CLRS |
| 22 | QueueBFS | §22.2 | ⚠️ no shortest path | ✅ Linked O(n²) | 0+0 | Main: 0; Cmplx: ✅ 0 assume_ |
| 22 | IterativeDFS | — | ⚠️ reachability | — | 0 | Not CLRS |
| 22 | StackDFS | §22.3 | ⚠️ d<f, no full nesting | ✅ Linked O(n²) | 0+0 | Main: 0; Cmplx: ✅ 0 assume_ |
| 22 | KahnTopologicalSort | — | ✅ topo order ∧ distinct | ✅ Linked O(n²) | 0 | ✅ Fully verified (was 2 admits) |
| 22 | BFS/DFS specs | §22 | ⚠️ partial | — | 8 | Distance, parenthesis, white-path |
| 23 | Kruskal | §23.2 | ⚠️ forest, not MST | ✅ Linked O(n³) | 16 | Across Spec/EdgeSort/Cmplx |
| 23 | Prim | §23.2 | ⚠️ key bounds only | ✅ Linked O(n²) | 6 | |
| 23 | MST.Spec | §23.1 | ⚠️ admitted | — | 4 | Exchange lemma proven |
| 24 | Dijkstra | §24.3 | ✅ d=δ proven | ✅ Linked O(n²) | 0 | Correctness + TriIneq: ✅ 0 admits |
| 24 | Bellman-Ford | §24.1 | ✅ dist=sp_dist | ⚠️ Separate O(V³) | 0 | ✅ BF.Spec fully verified |
| 25 | Floyd-Warshall | §25.2 | ✅ result=spec | ✅ Linked O(n³) | 0 | |
| 26 | MaxFlow | §26.2 | ❌ STUB | — | 8 assume | Stretch goal |
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

### Unproven Obligation Distribution (48 total: 39 admit + 2 assume_val + 7 assume)

| Chapter | admit | assume_val | assume | Total | Top files |
|---------|-------|------------|--------|-------|-----------|
| ch23 (MST) | 16 | 1 | 0 | 17 | Kruskal.Spec(9), Prim.Spec(6), MST.Spec(1), Kruskal(0+1 assume_val) |
| ch08 (sorting) | 10 | 0 | 0 | 10 | RadixSort.FullSort(4), RS.MultiDigit(2), RS.Spec(2), RS.Stability(2) |
| ch22 (graphs) | 0 | 7 | 0 | 7 | DFS.Spec(5 assume_val), DFS.WhitePath(2 assume_val) |
| ch26 (MaxFlow) | 0 | 0 | 3 | 3 | MaxFlow.Spec(2 assume), Complexity(1 assume) — axioms |
| ch12 (BST) | 0 | 0 | 0 | 0 | ✅ Fully verified (spec gaps in Tier B) |
| Other | 0 | 0 | 0 | 0 | ✅ All resolved |
| **Total** | **26** | **8** | **3** | **37** | |

Note: MaxFlow `assume(...)` are mathematical axioms (weak duality, MFMC), beyond scope.
BFS.DistanceSpec fully proven (was 2 admits). VertexCover.Spec fully proven (was 1 admit).
MaxSubarray.DC assume val eliminated. Huffman.Complete: WPL optimality fully proven.

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
5. **Partial/one-sided**: Dijkstra (upper bound only), BellmanFord (positive case only),
   BST imperative (one case per operation), KMP (trivial bounds)
6. **Axiom-dependent**: MaxFlow (MFMC assumed), Kruskal/Prim (cut property partially proven)

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

4. **BellmanFord (ch24)**: Postcondition proves `no_neg_cycle==true ==> triangle_inequality ∧
   dist[v] <= sp_dist`. **Missing**: `no_neg_cycle==false ==> negative cycle exists`. The Spec
   module has `bf_negative_cycle_detection` (Corollary 24.5) connecting `exists_relaxable_edge`
   to the extra round, but this is not wired into the imperative postcondition.
   (BellmanFord.fst lines 134-149)

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
12. **MaxFlow (ch26)**: Implementation proves capacity+conservation but not max value.
    Spec has 2 assumes for weak duality + max-flow min-cut theorem (see admits table).
13. **BFS DistanceSpec (ch22)**: ✅ Actually fully proven — `bfs_correctness` proves
    `d_bfs == d_shortest` for all vertices. Zero admits.

---

## Parallel Agent Tasks (AGENT1–AGENT15)

Fifteen independent tasks for parallel execution. All are independent except
AGENT5 (Kruskal) and AGENT6 (Prim) which depend on AGENT4 (MST exchange lemma).

Each agent MUST work on different files with no overlap, so they can run
simultaneously without conflicts (except for PROGRESS_PLAN.md).

Agent must commit only the files they work on, repeatedly as they reach
meaningful checkpoints.

When an agent finishes, they should update PROGRESS_PLAN.md with their
results and learnings, using `flock` to avoid conflicts.

**Dependency graph:**
```
Independent (start immediately):
  AGENT1   RadixSort stability        (10 admits)
  AGENT2   DFS theorems               (7 assume vals)
  AGENT3   MaxSubarray optimality     (spec gap)
  AGENT7   BST imperative specs       (spec gap)
  AGENT8   BellmanFord neg cycle      (spec gap)
  AGENT9   Dijkstra equality          (spec gap)
  AGENT10  LCS optimality             (spec gap)
  AGENT11  KMP completeness           (spec gap)
  AGENT12  Floyd-Warshall APSP        (spec gap)
  AGENT13  MaxFlow MFMC axioms        (3 assumes)
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

### AGENT1: RadixSort Stability Cascade — (10 admits → 0)

**Files:** `ch08-linear-sorting/CLRS.Ch08.RadixSort.Stability.fst` (primary),
`.Spec.fst`, `.MultiDigit.fst`, `.FullSort.fst`
**Current state:** 10 admits total: Stability(2), Spec(2), MultiDigit(2), FullSort(4).
FullSort's 4 are references to Stability.

**Goal:** Eliminate all 10 admits.

**Admit locations:**
- Stability.fst line 236: `lemma_stable_sort_preserves_lower_order`
- Stability.fst line 277: `lemma_stable_pass_preserves_ordering` (final step)
- Spec.fst line 349: `lemma_stable_sort_preserves_order`
- Spec.fst line 373: `radix_sort_correctness`
- MultiDigit.fst line 394: `stable_sort_preserves_order`
- MultiDigit.fst line 415: `stable_sort_preserves_sorted_on_other_digit`
- FullSort.fst lines 496, 500, 521, 525: references to Stability results

**Approach:** The core blocker is `lemma_stable_sort_preserves_lower_order` in Stability.fst:
stable sort on digit d preserves MSD-lex order on digits 0..d-1 for elements with equal digit d.
Once Stability.fst is proven, the other 8 admits dissolve.

**Estimated size:** ~100–150 lines (concentrated in Stability.fst).

**Verification:**
```bash
fstar.exe --include common --include ch08-linear-sorting --warn_error -321 --warn_error @247 \
  --ext optimize_let_vc --ext fly_deps --cache_dir _cache --already_cached 'Prims,FStar' \
  ch08-linear-sorting/CLRS.Ch08.RadixSort.Stability.fst
```

---

### AGENT2: DFS Parenthesis + White-Path Theorems — (7 assume vals → 0)

**Files:** `ch22-elementary-graph/CLRS.Ch22.DFS.Spec.fst` (5 assume vals),
`ch22-elementary-graph/CLRS.Ch22.DFS.WhitePath.fst` (2 assume vals)

**Assume vals in DFS.Spec.fst:**
1. `dfs_parenthesis_property` (line 965) — CLRS Theorem 22.7
2. `dfs_visit_explores_reachable` (line 1034)
3. `white_path_gives_containment` (line 1082)
4. `cycle_iff_back_edge` (line 1136)
5. `topo_order_iff_no_back_edge` (line 1176)

**Assume vals in DFS.WhitePath.fst:**
1. `white_path_implies_descendant_aux` (line 289)
2. `descendant_implies_white_path_aux` (line 342)

**Approach:** Structural induction on DFS execution. The parenthesis theorem is the foundation;
edge classification and white-path theorem follow from it.

**Estimated size:** ~200–350 lines.

---

### AGENT3: MaxSubarray True Optimality — prove Kadane finds actual max

**Files:** `ch04-divide-conquer/CLRS.Ch04.MaxSubarray.Kadane.fst`
**Current state:** 0 admits but spec is self-referential (`result == kadane_spec s`).

**Goal:** Prove `kadane_spec s >= sum_range s i j` for all contiguous subarrays `[i,j)`,
AND `∃ i j. kadane_spec s == sum_range s i j`.

**Approach:**
- Prove `kadane_spec` at position i tracks max suffix sum ending at i. Induction on i.
- Prove `best_sum = max over all positions of current_sum = true_max_subarray s`.

**Estimated size:** ~200–300 lines.

---

### AGENT4: MST Exchange Lemma — (1 admit → 0)

**Files:** `ch23-mst/CLRS.Ch23.MST.Spec.fst`
**Current state:** 1 admit at line 799: `exchange_is_spanning_tree`.

**Goal:** Prove that swapping an edge on the path between two vertices in a spanning tree
with a new edge preserves the spanning tree property.

**Approach:** When edge (u,v) is removed from a spanning tree T, T splits into two components.
Adding edge e that crosses this partition reconnects the tree. Prove:
1. Removing an edge from a spanning tree creates exactly 2 components
2. Adding an edge crossing the partition produces a spanning tree
3. The new tree has n-1 edges and connects all vertices

**Estimated size:** ~150–200 lines.

**Verification:**
```bash
fstar.exe --include common --include ch23-mst --warn_error -321 --warn_error @247 \
  --ext optimize_let_vc --ext fly_deps --cache_dir _cache --already_cached 'Prims,FStar' \
  ch23-mst/CLRS.Ch23.MST.Spec.fst
```

---

### AGENT5: Kruskal.Spec Completion — (9 admits + 1 assume val → 0)
**⚠️ DEPENDS ON AGENT4 (MST exchange lemma)**

**Files:** `ch23-mst/CLRS.Ch23.Kruskal.Spec.fst` (9 admits),
`ch23-mst/CLRS.Ch23.Kruskal.fst` (1 assume val)

**Admit locations:**
- Line 615: `lemma_kruskal_step_preserves_forest`
- Line 681: `lemma_kruskal_step_safe_edge`
- Line 688: `lemma_forest_respects_own_cut`
- Line 710: `lemma_edge_is_light`
- Line 742: `theorem_kruskal_produces_spanning_tree`
- Line 769: `theorem_kruskal_produces_mst`
- Line 780: `lemma_edge_addition_reduces_components`
- Lines 893, 901: Additional helpers

**Assume val in Kruskal.fst:**
- Line 81: `lemma_kruskal_maintains_forest`

**Goal:** Eliminate all 10 obligations using the proven cut property from MST.Spec.

**Estimated size:** ~250–350 lines.

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

**Files:** `ch24-sssp/CLRS.Ch24.BellmanFord.fst`
**Current state:** 0 admits, but postcondition only covers `no_neg_cycle == true`.

**Goal:** Add postcondition:
`no_neg_cycle == false ==> ∃ u v. edge(u,v) violates triangle inequality`.

The spec module already has `bf_negative_cycle_detection` (Spec.fst line 921-969) proving
`exists_relaxable_edge ⟺ extra round changes distances`. The verification loop already
detects the violating edge. Wire the detection into the postcondition using
`no_violations_partial` from the loop invariant.

**Estimated size:** ~50–100 lines.

---

### AGENT9: Dijkstra — remove verification pass, clean up infinity, prove equality

**Files:** `ch24-sssp/CLRS.Ch24.Dijkstra.fst`, using theory from
`ch24-sssp/CLRS.Ch24.Dijkstra.TriangleInequality.fst` and
`ch24-sssp/CLRS.Ch24.Dijkstra.Correctness.fst`
**Current state:** 0 admits, but:
1. The implementation has a **bogus triangle inequality verification pass** (lines 329–393)
   that reads all edges after the main loop and checks `dist[v] <= dist[u] + w`. This is NOT
   part of Dijkstra's algorithm — the triangle inequality is a *consequence* of edge relaxation.
2. The postcondition is conditional on `vtri == true` (the check passing) and only proves
   `dist[v] <= sp_dist[v]` (upper bound), not equality.
3. There is a `tri_result` parameter that makes no algorithmic sense.
4. The code uses `1000000` as a magic constant for infinity throughout. Since Dijkstra only
   works with non-negative edge weights, `-1` is a cleaner sentinel for "unreachable/no edge"
   in the distance array (any negative value is impossible as a real distance).

**What's already proven (in TriangleInequality.fst):**
- `relax_edge_establishes_triangle`: relaxing edge (u,v) ⟹ triangle inequality for that edge
- `process_vertex_extends_triangle`: relaxing all edges from u extends triangle inequality
- `dijkstra_algorithm_establishes_triangle`: after processing all vertices, triangle inequality
  holds for ALL edges — **no verification pass needed**
- `dijkstra_init_satisfies_triangle`, `dijkstra_init_ordering`: initial conditions hold
- The file explicitly states (line 877): "The verification pass is REDUNDANT"

**What's already proven (in Correctness.fst):**
- `greedy_choice_invariant`: when u is extracted as min unvisited, `dist[u] == sp_dist[u]`
  (requires `SP.has_triangle_inequality` + `all_settled_optimal` + `all_distances_upper_bounds`)
- `relax_establishes_triangle_inequality`: relaxing all edges from settled x establishes
  triangle inequality for edges from x

**Goal (4 sub-tasks):**

1. **Remove the verification pass** (lines 329–393 in Dijkstra.fst). Delete the `tri_result`
   parameter, the `tri_ok` mutable, and the two nested verification loops. The postcondition
   should unconditionally assert `triangle_inequality` (not conditional on `vtri == true`).

2. **Clean up infinity convention.** Replace `1000000` with `-1` as the sentinel for infinity
   in the distance array. Since all edge weights are non-negative (precondition), any real
   shortest-path distance is ≥ 0, so `-1` is unambiguous.
   - In Dijkstra.fst: change initialization `1000000` → `-1`, relax condition
     `w < 1000000 && dist_u < 1000000` → `w >= 0 && dist_u >= 0` (i.e., both are real/finite),
     remove `all_bounded`, simplify `all_non_negative` to mean "dist[v] >= 0 or dist[v] == -1".
   - In ShortestPath.Spec.fst: change `let inf = 1000000` → `let inf = -1`. This affects
     `sp_dist_k`, `path_weight`, etc. The spec's inf sentinel is only used for "no path" and
     comparisons — changing it to -1 requires updating comparisons like `via_u < inf` to
     `via_u >= 0` (i.e., finite check). **This is the main ripple.** The TriangleInequality and
     BellmanFord spec files also define `let inf = 1000000` and must be updated in sync.
   - **Scope warning:** This touches ShortestPath.Spec, BellmanFord.Spec, BellmanFord.fst,
     Dijkstra.TriangleInequality, BellmanFord.TriangleInequality. Coordinate with AGENT8
     (BellmanFord) if both agents are running. Alternative: do this cleanup AFTER AGENT8
     finishes, or let AGENT9 handle all SSSP files.

3. **Connect the pure model to the Pulse loop.** The main loop (lines 246–322) must maintain
   a ghost invariant linking its state to `process_vertices` from TriangleInequality.fst:
   - Ghost `processed_set` tracking which vertices have been settled
   - Invariant: `triangle_inequality_from_processed dist weights processed`
   - Invariant: `processed_le_unprocessed dist processed`
   - After n iterations, all vertices processed ⟹ full `triangle_inequality`
   - Call `dijkstra_algorithm_establishes_triangle` or reproduce its argument in the loop

4. **Prove shortest-path equality** (`dist[v] == sp_dist[v]` for all v). The chain:
   - Triangle inequality (from step 3) ⟹ `dist[v] <= sp_dist[v]` via `triangle_ineq_implies_upper_bound`
   - `greedy_choice_invariant` gives `dist[u] == sp_dist[u]` at each extraction step
   - Accumulate `all_settled_optimal` across the loop
   - After all vertices settled: `dist[v] == sp_dist[v]` for all v

**New postcondition should be (after cleanup):**
```fstar
ensures exists* sdist'.
  A.pts_to weights sweights **
  A.pts_to dist sdist' **
  pure (
    Seq.length sdist' == SZ.v n /\
    Seq.index sdist' (SZ.v source) == 0 /\
    (forall (v: nat). v < SZ.v n ==>
      Seq.index sdist' v == SP.sp_dist sweights (SZ.v n) (SZ.v source) v)
  )
```

**Approach:** The hard part is step 3 — connecting the Pulse loop to the pure model. Two options:
- (A) Add ghost state (`processed: GR.ref processed_set`) to the Pulse loop, maintain
  the pure invariants alongside the imperative code. Call the TriangleInequality lemmas
  at each iteration.
- (B) Prove a simulation lemma: the sequence of `dist` values produced by the Pulse loop
  equals `process_vertices dist_init weights initial_processed n`. Then apply
  `dijkstra_algorithm_establishes_triangle` once at the end.

Option (A) is more direct. The loop invariant grows but each step is already proven.

**Estimated size:** ~300–500 lines (verification pass removal + infinity cleanup + ghost state + equality proof).

**Recommended ordering:** Do sub-tasks 1, 3, 4 first (remove pass, prove equality). Then do
sub-task 2 (infinity cleanup) as a separate commit since it touches shared spec files.

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

### AGENT11: KMP Match Completeness — prove all matches found

**Files:** `ch32-string-matching/CLRS.Ch32.KMP.fst` or `KMP.StrengthenedSpec.fst`
**Current state:** 0 admits, proves trivial bounds `0 <= count <= n+1`.

**Goal:** Strengthen postcondition to `count == count_matches_spec text pat n m`.
The StrengthenedSpec module already outlines this. Need:
(a) KMP maintains count invariant (each match incremented)
(b) Failure links cover all necessary positions (no matches missed)
RabinKarp already has this proof as a template.

**Estimated size:** ~100–200 lines.

---

### AGENT12: Floyd-Warshall Shortest Path Semantics — prove APSP correctness

**Files:** `ch25-apsp/CLRS.Ch25.FloydWarshall.fst`
**Current state:** 0 admits, proves `contents' == fw_outer contents n 0` (recurrence only).

**Goal:** Prove `fw_outer` computes actual shortest paths.
- Define `shortest_path_dist n adj i j` (can reuse ShortestPath.Spec.fst's `sp_dist` pattern).
- Prove by induction on k that `fw_outer[k][i][j] = min over paths using vertices {0,...,k-1}`.
- CLRS Theorem 25.2.

**Estimated size:** ~150–250 lines.

---

### AGENT13: MaxFlow MFMC Axioms — prove weak duality and critical edge (3 assumes → 0)

**Files:** `ch26-max-flow/CLRS.Ch26.MaxFlow.Spec.fst`, `ch26-max-flow/CLRS.Ch26.MaxFlow.Complexity.fst`
**Current state:** 3 `assume(...)` statements (mathematical axioms).

**Assume locations:**
- Spec.fst line 354: Weak duality `flow_value ≤ cut_capacity`
- Spec.fst line 382: MFMC — no augmenting path ⟹ ∃ min cut
- Complexity.fst line 102: Each augmentation creates a critical edge

**Goal:** Replace assumes with proofs.

**Approach:**
- Weak duality: decompose flow value as net flow across the cut, show each edge contributes
  ≤ its capacity. Induction on edges crossing the cut.
- MFMC: define the residual graph's source-reachable set as the cut S. Show flow on S→T edges
  equals capacity (no augmenting path ⟹ residual capacity = 0). Combine with weak duality.
- Critical edge: follows from bottleneck definition — the bottleneck edge becomes saturated.

**Estimated size:** ~200–300 lines.

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
| Round 3: AGENT5 | BFS DistanceSpec (2→0 admits) | ✅ DONE (bfs_correctness) |
| Round 3: AGENT7 | MST Cut Property (4→1 admit) | ✅ MOSTLY DONE |
| Round 3: AGENT9 | MaxFlow Proofs (7→0 assumes) | ✅ DONE (MFMC stated) |
| Round 3: AGENT10 | VertexCover (1→0 admits) | ✅ DONE (ghost matching) |
| Round 2: AGENT1 | StackDFS.Complexity (4→0 assume_) | ✅ DONE |
| Round 2: AGENT2 | CountingSort.Stable (3→0) | ✅ DONE |
| Round 2: AGENT3 | Kruskal.Complexity (2+1→0) | ✅ DONE |
| Round 2: AGENT4 | KMP.Complexity (7→0) | ✅ DONE |
| Round 2: AGENT5 | BucketSort (1→0) | ✅ DONE |
| Round 2: AGENT6 | Huffman.Complete (Spec 4→0, Complete 2→0) | ✅ DONE |
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
| ch22/DFS.Spec | assume val | 5 | AGENT2 | Parenthesis theorem, edge classification (lines 965, 1034, 1082, 1136, 1176) |
| ch22/DFS.WhitePath | assume val | 2 | AGENT2 | White-path theorem fwd/bwd (lines 289, 342) |
| ch23/MST.Spec | admit | 1 | AGENT4 | Exchange in spanning tree (line 799) |
| ch23/Kruskal.Spec | admit | 9 | AGENT5 | Forest, MST invariant (lines 615, 681, 688, 710, 742, 769, 780, 893, 901) |
| ch23/Kruskal.fst | assume val | 1 | AGENT5 | Maintains forest (line 81) |
| ch23/Prim.Spec | admit | 6 | AGENT6 | Light edge, edge count (lines 195, 209, 270, 359, 380, 412) |
| ch26/MaxFlow.Spec | assume | 2 | AGENT13 | Weak duality + MFMC axioms (lines 354, 382) |
| ch26/MaxFlow.Complexity | assume | 1 | AGENT13 | Critical edge existence (line 102) |
| **TOTAL (admits)** | | **26** | | |
| **TOTAL (assume vals)** | | **8** | | |
| **TOTAL (assumes)** | | **3** | | Mathematical axioms, beyond scope |
| **GRAND TOTAL** | | **37** | | 34 actionable + 3 axioms |

### Spec Gaps (0 admits but incomplete postconditions)

| File | Gap | Agent | Description |
|------|-----|-------|-------------|
| ch12/BST.fst tree_search | One-sided | AGENT7 | None case: no guarantee key absent |
| ch12/BST.fst tree_insert | One-sided | AGENT7 | Success case: nothing proven about insertion |
| ch12/BST.Delete.fst | Weak | AGENT7 | Only proves valid[idx]=false or lengths preserved |
| ch04/MaxSubarray.Kadane | Self-referential | AGENT3 | result==kadane_spec, not >= all subarrays |
| ch04/MaxSubarray.DC | Disconnected | AGENT14 | DC proven optimal but not connected to Kadane |
| ch24/BellmanFord | One-sided | AGENT8 | no_neg_cycle=false: no negative cycle proof |
| ch24/Dijkstra | Bogus check + upper bound only | AGENT9 | Remove verification pass, prove equality from relaxation |
| ch15/LCS | Recurrence only | AGENT10 | result==lcs_length, no is_subsequence definition |
| ch32/KMP | Trivial bounds | AGENT11 | count bounds only, not == count_matches_spec |
| ch25/FloydWarshall | Recurrence only | AGENT12 | result==fw_outer, no shortest-path proof |

### Files with 0 admits (fully verified)

All other .fst files including: Huffman.Spec ✅, Huffman.Complete ✅,
BellmanFord.Spec ✅, Dijkstra.TriIneq ✅, Dijkstra.Correctness ✅,
KMP.Complexity ✅, BucketSort ✅, CountingSort.Stable ✅, Kruskal.EdgeSorting ✅,
StackDFS.Complexity ✅, QueueBFS.Complexity ✅, BST.Insert.Spec ✅,
BST.Delete.Spec ✅, BST.Spec.Complete ✅, BST.Spec.Complexity ✅,
RBTree.Spec ✅, UnionFind.Spec ✅ (1 assume for rank bound),
ActivitySelection.Spec ✅, RabinKarp.Spec ✅, MatrixChain.Spec ✅,
RodCutting.Spec ✅, GCD ✅, ExtendedGCD ✅, ModExp ✅,
BFS.DistanceSpec ✅, TopologicalSort.Verified ✅, Strassen ✅,
VertexCover.Spec ✅, and all Pulse implementation files.
