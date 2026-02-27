# Audit Report: Chapter 04 — Divide and Conquer

**Scope**: Binary Search, Maximum Subarray (Kadane & Divide-and-Conquer)  
**Directory**: `ch04-divide-conquer/`  
**Date**: 2025-07-18  
**Auditor**: Automated (Copilot CLI)

---

## File Inventory

| File | Lines | Language | Role |
|------|-------|---------|------|
| `CLRS.Ch04.BinarySearch.fst` | 184 | Pulse | Verified imperative binary search |
| `CLRS.Ch04.MaxSubarray.Spec.fst` | 155 | F* (pure) | Shared spec: `kadane_spec`, `sum_range`, optimality theorems |
| `CLRS.Ch04.MaxSubarray.DivideConquer.fst` | 383 | F* (pure) | D&C algorithm + correctness + complexity + equivalence |
| `CLRS.Ch04.MaxSubarray.Kadane.fst` | 115 | Pulse | Verified imperative Kadane |
| `Test.BinarySearch.fst` | 76 | Pulse | Two smoke tests (found / not-found) |
| `Test.MaxSubarray.fst` | 24 | F* (ML) | Print-only example; no executable test |

**Supporting**: `common/CLRS.Common.Complexity.fst` (81 lines) — ghost tick framework (not used by ch04; ch04 inlines its own).

---

## 1. CLRS Fidelity

### 1.1 Binary Search (`CLRS.Ch04.BinarySearch.fst`)

CLRS presents binary search as Exercise 2.3-5 ("Write pseudocode, either iterative or recursive, for binary search"). There is no canonical pseudocode in the textbook; the exercise leaves the form to the reader. The implementation follows the standard iterative binary search pattern:

| Aspect | CLRS Exercise 2.3-5 | Implementation | Match? |
|--------|---------------------|----------------|--------|
| Structure | Iterative or recursive | Iterative while loop | ✅ Standard |
| Range convention | 1-indexed | 0-indexed half-open `[lo, hi)` | ✅ Adapted |
| Midpoint calc | `mid = (lo + hi) / 2` | `mid = lo + (hi - lo) / 2` | ✅ Overflow-safe |
| Not-found sentinel | Unspecified | Returns `len` (= n) | ✅ Clean |
| Three-way compare | Check `=`, `<`, `>` | `mid_val = key`, `mid_val < key`, else | ✅ |
| Termination | `lo > hi` | `lo >= hi || found` | ✅ |

**Edge cases**: Empty arrays are excluded by precondition `SZ.v len > 0`. This is reasonable but deviates from a fully general implementation (an empty-array guard would be trivial to add).

**Verdict**: ✅ Faithful to standard binary search. Correctly adapted for 0-indexed half-open intervals.

### 1.2 Maximum Subarray — Divide & Conquer (`CLRS.Ch04.MaxSubarray.DivideConquer.fst`)

Compared against CLRS Section 4.1 pseudocode:

| CLRS Pseudocode | Implementation | Match? |
|-----------------|----------------|--------|
| `FIND-MAX-CROSSING-SUBARRAY(A, low, mid, high)` | `find_max_crossing_subarray` (line 64) via `find_max_crossing_left`/`find_max_crossing_right` | ✅ |
| Left scan: `for i = mid downto low` | `find_max_crossing_left`: recursive, starts at `mid-1` down to `low` | ✅ Equivalent |
| Right scan: `for j = mid+1 to high` | `find_max_crossing_right`: recursive, starts at `mid` up to `high-1` | ⚠️ See note |
| `FIND-MAXIMUM-SUBARRAY(A, low, high)` | `find_maximum_subarray_dc` (line 81) | ✅ |
| Base: `high == low` → return `(low, high, A[low])` | `low + 1 = high` → return `(A[low], low, high)` | ✅ Half-open adaptation |
| `mid = floor((low+high)/2)` | `mid = low + (high - low) / 2` | ✅ |
| Recursive left: `(low, mid)` | ✅ | |
| Recursive right: `(mid+1, high)` → `(mid, high)` in half-open | ✅ | |
| 3-way max comparison | Lines 96–101: `if left_sum >= right_sum && left_sum >= cross_sum` etc. | ✅ |

**Note on right scan**: CLRS initializes `right-sum = -∞` and scans from `mid+1`. The implementation initializes `best_sum = A[mid]` and `best_idx = mid+1`, scanning from `mid`. This is functionally equivalent — the first element (`A[mid]`) is accumulated into `current_sum` and compared against `best_sum` in the first iteration, producing the same result as starting with `-∞` and scanning from `mid+1`. The half-open `[low, high)` convention means `mid` in the implementation plays the role of `mid+1` in CLRS's 1-indexed closed `[low..high]`.

**Empty range handling**: The implementation adds a `low >= high` → `(0, low, low)` case that CLRS doesn't have (CLRS requires `high >= low` with at least one element). This is a safe extension.

**Verdict**: ✅ Structurally faithful. The half-open interval adaptation is correct and consistently applied.

### 1.3 Maximum Subarray — Kadane (`CLRS.Ch04.MaxSubarray.Kadane.fst`)

CLRS Exercise 4.1-5 describes the algorithm informally: "Start at the left end, progress toward the right, keeping track of the maximum subarray seen so far. A maximum subarray of A[1..j+1] is either a maximum subarray of A[1..j] or a subarray A[i..j+1]." No explicit pseudocode is given.

The implementation follows the standard Kadane's algorithm:
- `current_sum` tracks the maximum subarray ending at the current position
- `best_sum` tracks the global maximum
- `new_current = max(elem, current_sum + elem)` — standard Kadane recurrence
- `new_best = max(best_sum, new_current)` — global update

The initial values are `current_sum = 0` and `best_sum = initial_min = -10^9`. The loop invariant ties to `kadane_spec` from the Spec module.

**Verdict**: ✅ Faithful to Kadane's algorithm as described in CLRS Exercise 4.1-5.

---

## 2. Specification Strength

### 2.1 Binary Search

**Postcondition** (lines 96–107):
```
result <= len ∧
(result < len ⟹ s0[result] == key) ∧
(result == len ⟹ ∀i. i < |s0| ⟹ s0[i] ≠ key) ∧
complexity_bounded_log cf c0 len
```

| Property | Proved? | Rating |
|----------|---------|--------|
| Found → correct index | ✅ | **Strong** |
| Not-found → key absent from entire array | ✅ | **Strong** |
| Complexity: ≤ log₂(n) + 1 comparisons | ✅ | **Strong** |
| Uniqueness (returns *first* / *any* occurrence) | Not specified | — |

**Rating**: **Strong**. The postcondition fully specifies correctness (both found and not-found) and complexity. The only missing nuance is which index is returned when duplicates exist (but CLRS doesn't require this either).

### 2.2 Kadane's Algorithm (Spec + Kadane)

**Postcondition** (Kadane.fst lines 62–65):
```
result == max_subarray_spec s0 ∧
complexity_bounded_linear cf c0 len
```

**Theorems in Spec module**:

| Property | Proved? | Rating |
|----------|---------|--------|
| Kadane tracks `max_suffix_sum` / `max_sub_sum` (`lemma_kadane_correct`) | ✅ | **Strong** |
| Optimal: result ≥ every `sum_range s i j` (`theorem_kadane_optimal`) | ✅ | **Strong** |
| Achievable: ∃ i j. result == `sum_range s i j` (`theorem_kadane_witness`) | ✅ | **Strong** |
| Complexity: exactly n operations | ✅ | **Strong** |

**Precondition caveat**: `elements_bounded s` requires all elements ≥ `initial_min` (-10⁹). This is documented and necessary because the sentinel value `initial_min` is used as the initial `best_sum`. Without this, if all elements are < -10⁹, the result could be wrong.

**Rating**: **Strong**. Full optimality proof with both upper-bound and witness directions.

### 2.3 Divide & Conquer

| Property | Proved? | Rating |
|----------|---------|--------|
| Returned sum = `sum_range s left right` (`lemma_dc_sum_correct`) | ✅ | **Strong** |
| D&C result ≥ every subarray sum (`lemma_dc_optimal`) | ✅ | **Strong** |
| Non-empty input → non-empty result (`lemma_dc_nonempty`) | ✅ | **Strong** |
| Complexity: `dc_ops_count n ≤ 4n(log₂_ceil(n)+1)` | ✅ | **Strong** |
| D&C ≡ Kadane (`dc_kadane_equivalence`) | ✅ | **Strong** |

**Rating**: **Strong**. Complete correctness, optimality, and equivalence proofs.

### 2.4 Kadane ↔ D&C Equivalence

**Proved** in `CLRS.Ch04.MaxSubarray.DivideConquer.fst` lines 360–374:

```fstar
let dc_kadane_equivalence (s: Seq.seq int)
  : Lemma (requires Seq.length s > 0 /\ elements_bounded s)
          (ensures find_maximum_subarray_sum s == max_subarray_spec s)
```

The proof goes through `max_sub_sum` as an intermediary:
1. Kadane = `max_sub_sum` (from Spec module's `lemma_kadane_correct`)
2. D&C ≤ `max_sub_sum` (D&C returns some `sum_range`; `max_sub_sum` ≥ all `sum_range`)
3. D&C ≥ `max_sub_sum` (`max_sub_sum` = some `sum_range`; D&C ≥ all `sum_range`)

There is also a trivial wrapper `lemma_dc_equals_kadane` (line 377) that just calls `dc_kadane_equivalence`.

**Rating**: **Strong**. Fully machine-checked equivalence.

---

## 3. Complexity Results

### 3.1 Binary Search — O(log n)

| Aspect | Detail |
|--------|--------|
| Counter | Ghost `GR.ref nat`, erased at runtime |
| Bound | `complexity_bounded_log cf c0 n` ≡ `cf - c0 ≤ log2f(n) + 1` |
| Helper lemmas | `log2f` (floor), `lemma_log2f_mono` (monotonicity), `lemma_log2f_step` (halving step) |
| Proof technique | Loop invariant tracks remaining "budget": `(vc - c0) + log2f(hi - lo) ≤ log2f(n)` |

**Verdict**: ✅ **O(log n) proven**. The bound `≤ ⌊log₂(n)⌋ + 1` is tight.

### 3.2 Kadane — O(n)

| Aspect | Detail |
|--------|--------|
| Counter | Ghost `GR.ref nat`, erased at runtime |
| Bound | `complexity_bounded_linear cf c0 n` ≡ `cf - c0 == n` (exact, not just ≤) |
| Proof | Loop invariant: `vc == c0 + i` (one tick per iteration) |

**Verdict**: ✅ **O(n) proven** — actually Θ(n), exactly n operations.

### 3.3 D&C — O(n log n)

| Aspect | Detail |
|--------|--------|
| Recurrence model | `dc_ops_count n = 2 * dc_ops_count(n/2) + n` for n > 1, `dc_ops_count 1 = 1` |
| Bound | `dc_ops_count n ≤ 4n(log₂_ceil(n) + 1)` |
| Helper | `log2_ceil` (ceiling), `log2_ceil_monotone`, `log2_ceil_halving` |
| Proof | Induction on n; uses `8h ≤ 4n` and halving lemma |

**Note**: The complexity is proved on the *recurrence model* `dc_ops_count`, not on actual tick counts in the pure implementation. This is the standard approach for pure (non-Pulse) code, since there's no mutable state to thread a counter through. The constant factor 4 is conservative but correct.

**Verdict**: ✅ **O(n log n) proven** via Master Theorem case 2.

---

## 4. Code Quality

### 4.1 Code Duplication

| Duplicated Code | Location 1 | Location 2 | Severity |
|----------------|-----------|-----------|----------|
| `incr_nat` definition | BinarySearch.fst:30 | Kadane.fst:31 | **Medium** |
| `tick` ghost function | BinarySearch.fst:32–38 | Kadane.fst:33–39 | **Medium** |
| `complexity_bounded_*` predicates | BinarySearch.fst:72–73 | Kadane.fst:43 | **Low** |

The `common/CLRS.Common.Complexity.fst` module provides `tick` and complexity helpers, but ch04 modules define their own private versions using `GhostReference` instead of `Reference`. The Common module uses `Pulse.Lib.Reference` (observable state), while ch04 uses `Pulse.Lib.GhostReference` (erased state). This is the correct design choice for ch04 (ghost ticks are erased at runtime), but the duplication could be eliminated by parameterizing or adding a ghost-tick variant to Common.

### 4.2 Dead Code

- `lemma_dc_equals_kadane` (DivideConquer.fst:377–382) is a trivial wrapper around `dc_kadane_equivalence` with identical spec. One of them is redundant.
- `min_int` (DivideConquer.fst:26) is defined but never used anywhere.

### 4.3 Naming

Generally excellent. Module names follow `CLRS.ChNN.AlgorithmName` convention consistently. Function names are descriptive (`find_max_crossing_left`, `lemma_crossing_left_sum`). Lemma naming convention: `lemma_*` for internal lemmas, `theorem_*` for exported results.

### 4.4 Organization

Good separation of concerns:
- **Spec.fst**: Pure specifications and optimality proofs (reusable)
- **DivideConquer.fst**: Algorithm + correctness + complexity + equivalence
- **Kadane.fst**: Pulse implementation referencing Spec
- **BinarySearch.fst**: Self-contained (does not depend on common)

The Spec module is well-designed as a shared foundation.

---

## 5. Proof Quality

### 5.1 Admits / Assumes / Axioms

| Pattern | Count | Locations |
|---------|-------|-----------|
| `admit()` | **0** | — |
| `admit_` | **0** | — |
| `assume` (term-level) | **0** | — |
| `assume val` | **0** | — |
| `sorry` | **0** | — |
| `Tactics.Admit` | **0** | — |

**All six files are admit-free.** ✅

### 5.2 Solver Hints

| File | Hint | Location |
|------|------|----------|
| `CLRS.Ch04.BinarySearch.fst` | `--z3rlimit 20` | Line 77 |

Only a single `z3rlimit 20` directive in the entire chapter. This is very conservative (default is 5). No `--retry`, `--z3seed`, `--quake`, or `--z3cliopt` directives anywhere.

**Verdict**: ✅ Excellent proof stability. The low rlimit suggests proofs are robust.

### 5.3 Proof Architecture

| Technique | Used? | Notes |
|-----------|-------|-------|
| SMT-based | ✅ | Primary approach |
| Ghost state (GhostRef) | ✅ | For complexity counting in Pulse |
| Structural recursion | ✅ | All recursive lemmas have explicit `decreases` |
| Intermediate spec (`max_suffix_sum`, `max_sub_sum`) | ✅ | Clean layered proof |
| Witness functions | ✅ | `max_suffix_witness`, `max_sub_witness` for existential proofs |

The proof structure in Spec.fst is particularly clean: two orthogonal optimality theorems (upper bound + witness) compose to prove Kadane optimal, and the same `max_sub_sum` serves as the bridge for the D&C equivalence proof.

---

## 6. Documentation & Comments

### 6.1 Module Headers

All four implementation files have module-level doc comments listing what is proved and any relevant constraints. All correctly claim "NO admits. NO assumes." — verified by audit.

### 6.2 Inline Comments

- BinarySearch.fst: Well-commented sections (`Ghost tick`, `Pure helper`, `Definitions`, `Complexity bound predicate`)
- Spec.fst: Clear section headers and per-theorem documentation
- DivideConquer.fst: Good section organization; the equivalence proof has a nice inline explanation
- Kadane.fst: Adequate; the loop body has a complexity comment

### 6.3 SNIPPET markers

Both `BinarySearch.fst` and `DivideConquer.fst` use `//SNIPPET_START` / `//SNIPPET_END` markers for key signatures and theorems — good for documentation extraction.

### 6.4 Issues

- **DivideConquer.fst header** (line 10): Claims "Complexity: O(n lg n) via T(n) = 2T(n/2) + Theta(n) recurrence" — ✅ accurate.
- **DivideConquer.fst header** (line 12): Claims "Equivalence with Kadane's algorithm (proved)" — ✅ accurate.
- **Spec.fst**: `initial_min` is documented as "A very small integer" (line 19). It would be clearer to document the `elements_bounded` constraint more prominently, since it is a precondition on all optimality theorems.

---

## 7. Test Coverage

### 7.1 Binary Search Tests (`Test.BinarySearch.fst`)

| Test | Description | Verified? |
|------|-------------|-----------|
| `test_binary_search_found` | Search for 3 in [1,2,3,4,5] | ✅ Pulse-verified |
| `test_binary_search_not_found` | Search for 25 in [10,20,30,40,50] | ✅ Pulse-verified |

Tests allocate arrays, run binary search, and clean up. They verify type-level properties (via Pulse postconditions) but do **not** assert specific index values at runtime. The sorted-array precondition is proved by the specific constants used.

**Missing tests**: Empty array (precluded by spec), single element, duplicate keys, boundary elements (first/last).

### 7.2 MaxSubarray Tests (`Test.MaxSubarray.fst`)

This file only prints a description string. It does **not** call `max_subarray` or `find_maximum_subarray_dc` at runtime. It references the classic example `[-2, 1, -3, 4, -1, 2, 1, -5, 4]` with expected sum 6, but never verifies it.

**Missing**: Any actual executable test of either Kadane or D&C.

---

## 8. Summary Scorecard

| Dimension | Binary Search | MaxSubarray D&C | MaxSubarray Kadane | MaxSubarray Spec |
|-----------|:---:|:---:|:---:|:---:|
| CLRS Fidelity | ✅ | ✅ | ✅ | N/A |
| Spec Strength | Strong | Strong | Strong | Strong |
| Complexity Proof | O(log n) ✅ | O(n log n) ✅ | O(n) ✅ | N/A |
| Admits/Assumes | 0 | 0 | 0 | 0 |
| Proof Stability | Excellent | Excellent | Excellent | Excellent |
| Documentation | Good | Good | Good | Good |
| Test Coverage | Basic | **None** | **None** | N/A |
| Code Duplication | Minor | None | Minor | None |

---

## 9. Task List

### Priority 1 — High (Correctness / Completeness)

- [ ] **T1: Add executable test for Kadane.** `Test.MaxSubarray.fst` currently only prints strings. Add a Pulse test that allocates an array (e.g., `[-2, 1, -3, 4, -1, 2, 1, -5, 4]`), calls `max_subarray`, and asserts the result equals 6.
- [ ] **T2: Add executable test for D&C.** Either in `Test.MaxSubarray.fst` or a new file, call `find_maximum_subarray_sum` on the same example and check the result.
- [ ] **T3: Document `elements_bounded` constraint.** The `-10^9` sentinel is an implicit precondition on all optimality theorems. Add a prominent note in `Spec.fst` header explaining the valid input range and when this could bite users.

### Priority 2 — Medium (Code Quality)

- [ ] **T4: Eliminate `incr_nat`/`tick` duplication.** Extract a `CLRS.Common.GhostComplexity` module with ghost-tick versions of `incr_nat`, `tick`, and the complexity-bound predicates. Update `BinarySearch.fst` and `Kadane.fst` to import it.
- [ ] **T5: Remove dead code.** Delete `min_int` (DivideConquer.fst:26) and either `dc_kadane_equivalence` or `lemma_dc_equals_kadane` (keep one, remove the duplicate wrapper).
- [ ] **T6: Support empty arrays in Binary Search.** Add an `if len = 0 then return 0sz` guard (or document why it is intentionally excluded).

### Priority 3 — Low (Polish)

- [ ] **T7: Add more Binary Search test cases.** Test: single element found, single element not-found, duplicate keys, key at boundaries (first/last element).
- [ ] **T8: Add negative-test for MaxSubarray.** Test all-negative array (e.g., `[-3, -5, -1]`) — expected result should be `-1`.
- [ ] **T9: Consider generalizing `initial_min`.** The hard-coded `-10^9` sentinel limits the algorithm to inputs ≥ -10⁹. An alternative design could use `Option int` or parameterize the sentinel, making the spec unconditional.
- [ ] **T10: Align D&C complexity proof with implementation.** Currently the complexity bound is on the recurrence model `dc_ops_count`, not on actual operations in `find_maximum_subarray_dc`. Consider adding a ghost parameter or operational cost annotation for tighter integration.

---

## Appendix: Cross-Reference to CLRS

| CLRS Reference | Implementation |
|---------------|----------------|
| Exercise 2.3-5 (Binary Search) | `CLRS.Ch04.BinarySearch.binary_search` |
| Section 4.1 `FIND-MAX-CROSSING-SUBARRAY` | `CLRS.Ch04.MaxSubarray.DivideConquer.find_max_crossing_subarray` |
| Section 4.1 `FIND-MAXIMUM-SUBARRAY` | `CLRS.Ch04.MaxSubarray.DivideConquer.find_maximum_subarray_dc` |
| Exercise 4.1-5 (Kadane / linear-time) | `CLRS.Ch04.MaxSubarray.Kadane.max_subarray` |
| Section 4.1 Complexity: T(n) = 2T(n/2) + Θ(n) | `CLRS.Ch04.MaxSubarray.DivideConquer.lemma_dc_complexity_bound` |

---

*End of audit.*
