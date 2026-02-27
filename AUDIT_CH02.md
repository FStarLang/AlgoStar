# Audit Report: Chapter 02 — Getting Started (Insertion Sort, Merge Sort)

**Date:** 2025-07-17  
**Scope:** `ch02-getting-started/`, `common/CLRS.Common.SortSpec.fst`, `common/CLRS.Common.Complexity.fst`, `common/Predicates.fst`  
**Auditor:** Copilot  

## Files Audited

| File | Lines | Purpose |
|------|-------|---------|
| `CLRS.Ch02.InsertionSort.fst` | 222 | Insertion sort with complexity proof |
| `CLRS.Ch02.MergeSort.fst` | 583 | Merge sort (merge + recursive sort) |
| `CLRS.Ch02.MergeSort.Complexity.fst` | 246 | O(n log n) bound for merge sort (pure) |
| `CLRS.Common.SortSpec.fst` | 106 | Shared definitions: sorted, permutation, lemmas |
| `CLRS.Common.Complexity.fst` | 81 | Ghost tick counter, triangle/log helpers |
| `Predicates.fst` / `.fsti` | 45 / 45 | Generic predicates (sorted, heap, bounds) |
| `ch02-getting-started/README.md` | 79 | Chapter documentation |

---

## 1. CLRS Fidelity

### 1.1 Insertion Sort (`CLRS.Ch02.InsertionSort.fst`)

**CLRS pseudocode (Section 2.1, p. 18):**
```
INSERTION-SORT(A)
1  for j = 2 to A.length
2    key = A[j]
3    i = j - 1
4    while i > 0 and A[i] > key
5      A[i+1] = A[i]        // shift right
6      i = i - 1
7    A[i+1] = key            // insert key
```

**Implementation structure:**
- Outer loop: `j = 1 to len-1` (0-indexed) — **matches** CLRS after index adjustment.
- Key extraction: `key = a.(vj)` at line 133 — **matches**.
- Inner loop guard: `continue` flag set by explicit comparison — **deviation** from CLRS's `while i > 0 and A[i] > key`. The implementation uses a boolean mutable `continue` to track the loop condition, which is an idiomatic Pulse pattern (no compound `while` guards).

**Significant Deviation — Swap vs. Shift:**
CLRS shifts elements right (`A[i+1] = A[i]`) and inserts the key at the end (`A[i+1] = key`). The implementation instead **swaps adjacent elements** (lines 180-184):
```pulse
a.(vi - 1sz) <- val_curr;   // key moves left
a.(vi) <- val_prev;          // displaced element moves right
```
This is functionally equivalent (the key "bubbles" left through swaps) but differs from CLRS's shift-then-insert strategy. The key is always at position `i` rather than held in a register. This is a well-known variant, sometimes called "swap-based insertion sort."

**Impact:** The swap variant performs 2× the writes of CLRS's shift variant (two writes per inner iteration vs. one shift + one insert). The number of **comparisons** is identical, so the complexity proof counting comparisons is unaffected.

**Edge Case — `len > 0` Precondition:**
The implementation requires `SZ.v len > 0` (line 102). CLRS handles empty arrays implicitly (the `for j = 2 to 0` loop body never executes). This is a minor restriction; callers must ensure the array is non-empty.

**Naming:** `insertion_sort` — consistent with CLRS `INSERTION-SORT` (snake_case adaptation).

### 1.2 Merge (`CLRS.Ch02.MergeSort.fst`, `merge_impl`)

**CLRS pseudocode (Section 2.3.1, p. 31):**
```
MERGE(A, p, q, r)
1  n1 = q - p + 1
2  n2 = r - q
3  let L[1..n1+1] and R[1..n2+1] be new arrays
4  for i = 1 to n1: L[i] = A[p+i-1]
5  for j = 1 to n2: R[j] = A[q+j]
6  L[n1+1] = ∞
7  R[n2+1] = ∞
8  i = 1; j = 1
9  for k = p to r
10   if L[i] <= R[j]: A[k] = L[i]; i++
11   else: A[k] = R[j]; j++
```

**Implementation deviations:**
1. **No sentinel values.** CLRS uses `∞` sentinels; the implementation uses explicit index-bounds checking (`vi = l1`, `vj = l2`) at lines 440, 448. This avoids needing a sentinel representation for `int`.
2. **Half-open intervals.** CLRS uses inclusive `[p, q]` and `[q+1, r]`. Implementation uses `[lo, mid)` and `[mid, hi)` (standard for PL implementations).
3. **CLRS uses a single for loop** `for k = p to r`. The implementation uses a **while loop** with manual k-increment since Pulse lacks range-based for loops.
4. **Ghost-level merge function.** A pure `seq_merge` function (line 39) defines the expected result, and the loop invariant proves the imperative output matches it element-by-element. This is a stronger verification strategy than CLRS's loop invariant.

**Naming:** `merge_impl` — deviates from CLRS `MERGE`. Consider renaming to `merge` for clarity.

### 1.3 Merge Sort (`CLRS.Ch02.MergeSort.fst`, `merge_sort` / `merge_sort_aux`)

**CLRS pseudocode (Section 2.3.1, p. 34):**
```
MERGE-SORT(A, p, r)
1  if p < r
2    q = ⌊(p+r)/2⌋
3    MERGE-SORT(A, p, q)
4    MERGE-SORT(A, q+1, r)
5    MERGE(A, p, q, r)
```

**Implementation:**
```pulse
fn rec merge_sort_aux (a: array int) (lo hi: SZ.t)
  ...
  let mid = lo +^ (len /^ 2sz);   // mid = lo + ⌊len/2⌋
  merge_sort_aux a lo mid;          // left  = [lo, mid)
  merge_sort_aux a mid hi;          // right = [mid, hi)
  merge_impl a lo mid hi;
```

**Deviations:**
1. **Half-open intervals** (same as merge). CLRS recursive calls are `(A, p, q)` and `(A, q+1, r)` with inclusive bounds. The implementation uses `[lo, mid)` and `[mid, hi)`. Functionally equivalent.
2. **Base case:** CLRS uses `if p < r`; implementation uses `len < 2` (handles len=0 and len=1). This correctly handles the empty subarray case that CLRS handles implicitly.
3. **Two entry points:** `merge_sort` (top-level, takes `A.pts_to`) wraps `merge_sort_aux` (recursive, uses `pts_to_range`). This is a clean design necessitated by Pulse's ownership model.

**Naming:** `merge_sort` / `merge_sort_aux` — consistent with CLRS `MERGE-SORT`.

### 1.4 Fidelity Summary

| Algorithm | CLRS Section | Naming | Structure Match | Deviations |
|-----------|-------------|--------|-----------------|------------|
| Insertion Sort | 2.1 | ✅ | Partial | Swap vs. shift; `len > 0` required |
| Merge | 2.3.1 | ⚠️ `merge_impl` | Close | No sentinels; half-open intervals |
| Merge Sort | 2.3.1 | ✅ | Close | Half-open intervals; two entry points |

---

## 2. Specification Strength

### 2.1 Insertion Sort

**Postcondition (lines 104-109):**
```fstar
sorted s /\
permutation s0 s /\
complexity_bounded cf (reveal c0) (SZ.v len)
```

- **Sorted:** ✅ Full `sorted` (all pairs ordered).
- **Permutation:** ✅ Uses count-based `permutation` from `CLRS.Common.SortSpec`.
- **Complexity:** ✅ Proves `cf - c0 <= n*(n-1)/2` (comparison count).
- **Length preservation:** ✅ `Seq.length s == Seq.length s0`.

**Rating: Strong.** Proves sortedness, permutation, and O(n²) complexity bound — all three key properties.

### 2.2 Merge Sort

**Postcondition (lines 559-565):**
```fstar
Seq.length s == Seq.length s0 /\
sorted s /\
permutation s0 s
```

- **Sorted:** ✅ Full `sorted`.
- **Permutation:** ✅ Count-based `permutation`.
- **Length preservation:** ✅
- **Complexity:** ❌ Not proved in the imperative code. No ghost tick counter.

**Rating: Medium-Strong.** Proves functional correctness (sorted + permutation) but lacks complexity instrumentation in the imperative code.

### 2.3 Merge Sort Complexity (`CLRS.Ch02.MergeSort.Complexity.fst`)

**What is proved (lines 169-231):**
```fstar
merge_sort_ops n <= 4 * n * log2_ceil n + 4 * n
```

This is a **pure F* proof** about a mathematical recurrence `T(n) = 2·T(⌈n/2⌉) + n`. It proves:
- The recurrence's closed-form upper bound is `4n⌈log₂ n⌉ + 4n`, i.e., O(n log n).

**Spec gap:** The complexity module defines its own recurrence (`merge_sort_ops`) but this is **not linked** to the actual imperative `merge_sort` or `merge_impl` code via ghost tick counting. There is no proof that the imperative merge sort's actual comparison count equals `merge_sort_ops(n)`.

**Rating: Medium.** The math is correct and non-trivial, but the gap between the pure recurrence and the imperative code is unbridged.

### 2.4 Common SortSpec

**Definitions (lines 23-31):**
- `sorted`: ∀ i ≤ j < len. s[i] ≤ s[j] — standard, correct.
- `prefix_sorted`: sorted on prefix [0, k) — useful for loop invariants.
- `permutation`: wraps `FStar.Seq.Properties.permutation`, marked `opaque_to_smt` — good practice.

**Lemmas provided:**
- `permutation_refl`, `compose_permutations`, `permutation_same_length` — with SMTPats ✅
- `swap_is_permutation`, `append_permutations` — key building blocks ✅
- `singl_sorted` — base case ✅

**Rating: Strong.** Clean, well-structured specification module.

### 2.5 Specification Summary

| Function | Sorted | Permutation | Complexity | Overall |
|----------|--------|-------------|------------|---------|
| `insertion_sort` | ✅ | ✅ | ✅ O(n²) | **Strong** |
| `merge_sort` | ✅ | ✅ | ❌ | **Medium-Strong** |
| `merge_sort_ops` (pure) | — | — | ✅ O(n log n) | **Medium** (not linked) |
| `merge_impl` | ✅ | ✅ | ❌ | **Medium-Strong** |

---

## 3. Complexity Results

### 3.1 Insertion Sort — O(n²) Comparisons

**Bound proved:** `cf - c0 <= n*(n-1)/2` (line 88-89).

This is the **worst-case** number of comparisons (triangular number), matching CLRS's analysis: Θ(n²) worst-case, with the exact count being `n(n-1)/2` when the array is reverse-sorted.

**Ghost instrumentation:** The `tick` function (lines 34-40) uses `GR.ref nat` (ghost reference, erased at runtime). Each comparison in the inner loop increments the counter (lines 142, 196). The first comparison before the inner loop is also ticked (line 142).

**Bound tightness:** The bound `n(n-1)/2` is **tight** — it equals the exact worst-case count. ✅

**Linkage to imperative code:** The tick counter is threaded through `insertion_sort`'s signature. The postcondition directly bounds the counter. **Fully linked.** ✅

### 3.2 Merge Sort — O(n log n)

**Bound proved:** `merge_sort_ops(n) <= 4n⌈log₂ n⌉ + 4n` (line 170).

**Recurrence:**
```fstar
merge_sort_ops(n) = if n = 1 then 0 else 2 * merge_sort_ops(ceil(n/2)) + n
```

**CLRS comparison:**
- CLRS states Θ(n lg n) (Theorem 2.3, recurrence `T(n) = 2T(n/2) + Θ(n)`).
- The implementation uses `2T(⌈n/2⌉) + n` which slightly over-counts (uses ceiling for both halves, whereas CLRS splits into ⌈n/2⌉ and ⌊n/2⌋).
- The constant factor 4 is deliberately loose (noted at line 17).
- The bound is **valid but not tight**. CLRS's Θ(n lg n) is tighter.

**Linkage to imperative code:** ❌ **Not linked.** The complexity module is a standalone pure proof about a mathematical function. The imperative `merge_sort` / `merge_impl` have no ghost tick counter. There is no formal proof that the imperative code performs exactly `merge_sort_ops(n)` comparisons.

### 3.3 Complexity Summary

| Algorithm | Bound | Tight? | Matches CLRS? | Linked to Code? |
|-----------|-------|--------|---------------|-----------------|
| Insertion Sort | n(n-1)/2 | Yes | Yes (Θ(n²)) | ✅ Yes |
| Merge Sort | 4n⌈log₂ n⌉ + 4n | No (loose ×4) | Yes (O(n log n)) | ❌ No |

---

## 4. Code Quality

### 4.1 Code Duplication

1. **`tick` function duplication.** `CLRS.Ch02.InsertionSort.fst` defines its own `tick` (lines 34-40) using `GR.ref nat` (ghost reference), while `CLRS.Common.Complexity.fst` defines a different `tick` (lines 31-37) using `R.ref nat` (concrete reference). These serve the same purpose but use different reference types and are not shared.
   - InsertionSort's `tick`: `GR.ref nat` → fully erased at runtime ✅
   - Common Complexity `tick`: `R.ref nat` → not erased, has runtime cost ❌
   - **Issue:** The common module's tick is inferior (not ghost-erased). InsertionSort correctly uses the ghost variant but doesn't import from Common.

2. **`sorted` definition duplication.** Both `CLRS.Common.SortSpec.fst` (line 23) and `Predicates.fst` (line 18) define `sorted`. The SortSpec version is specialized to `int`; the Predicates version is generic over a comparator function. The two modules are not used together in ch02, but the duplication is a project-wide concern.

3. **`permutation` / `is_permutation` naming.** `SortSpec.fst` calls it `permutation`; `Predicates.fst` calls it `is_permutation`. Both wrap `FStar.Seq.Properties.permutation`.

### 4.2 Dead Code

1. **`module Classical = FStar.Classical`** in `CLRS.Ch02.InsertionSort.fst` (line 28): The `Classical` module alias is never used in InsertionSort. It is used in MergeSort (line 105).

2. **`Predicates.fst` / `Predicates.fsti`:** Not imported by any chapter 2 file. Not imported by any file in the project (based on grep). Appears to be dead code project-wide, superseded by `CLRS.Common.SortSpec.fst`.

3. **`CLRS.Common.Complexity.fst`:** Not imported by any chapter 2 file. InsertionSort re-implements its own ghost tick counter.

### 4.3 Code Organization

**Strengths:**
- Clean separation: one file per algorithm, shared specs in `common/`.
- `MergeSort.Complexity.fst` is properly separated from the imperative code.
- Pure `seq_merge` function serves as a specification for the imperative merge — good refinement pattern.

**Weaknesses:**
- The `common/` directory has two overlapping specification modules (`SortSpec` and `Predicates`).
- InsertionSort's complexity machinery is inline rather than shared.

### 4.4 Naming Conventions

| Convention | Status |
|-----------|--------|
| Module names: `CLRS.Ch02.<Algorithm>` | ✅ Consistent |
| Function names: snake_case | ✅ Consistent |
| Lemma names: descriptive snake_case | ✅ Good (`lemma_prefix_le_key`, `seq_merge_sorted`) |
| Module aliases: short uppercase | ✅ Consistent (`A`, `R`, `SZ`, `Seq`) |

---

## 5. Proof Quality

### 5.1 Admits, Assumes, Assume Vals

**`ch02-getting-started/CLRS.Ch02.InsertionSort.fst`:** ✅ **Zero** admits/assumes.  
**`ch02-getting-started/CLRS.Ch02.MergeSort.fst`:** ✅ **Zero** admits/assumes.  
**`ch02-getting-started/CLRS.Ch02.MergeSort.Complexity.fst`:** ✅ **Zero** admits/assumes.  
**`common/CLRS.Common.SortSpec.fst`:** ✅ **Zero** admits/assumes.  
**`common/CLRS.Common.Complexity.fst`:** ✅ **Zero** admits/assumes.  
**`common/Predicates.fst`:** ✅ **Zero** admits/assumes.

**Total: 0 admits, 0 assumes, 0 assume vals, 0 sorry.** All proofs are complete.

### 5.2 Z3 Resource Limits

| File | Line | Setting | Concern Level |
|------|------|---------|---------------|
| `MergeSort.fst` | 67 | `--z3rlimit 50 --fuel 3 --ifuel 2` | ⚠️ Moderate (fuel 3 could be costly) |
| `MergeSort.fst` | 113 | `--z3rlimit 40 --fuel 2 --ifuel 1` | ✅ Reasonable |
| `MergeSort.fst` | 172 | `--z3rlimit 50 --fuel 2 --ifuel 1` | ✅ Reasonable |
| `MergeSort.fst` | 293 | `--z3rlimit 40 --fuel 0 --ifuel 0` | ✅ Conservative |
| `MergeSort.fst` | 340 | `--z3rlimit 80 --fuel 2 --ifuel 1` | ⚠️ Elevated (highest in ch02) |
| `MergeSort.fst` | 496 | `--z3rlimit 40 --fuel 1 --ifuel 1` | ✅ Reasonable |
| `MergeSort.Complexity.fst` | 167 | `--z3rlimit 10 --fuel 1 --ifuel 0` | ✅ Low |
| `InsertionSort.fst` | — | No `#push-options` | ✅ Defaults only |

**No `--retry` flags found.** No `z3seed` overrides.

The highest rlimit is 80 (MergeSort merge loop, line 340). This is moderately high but acceptable for an imperative loop with a non-trivial invariant involving `seq_merge` and `pts_to_range`. The `fuel 3` at line 67 for the `seq_merge_count` proof could be reduced with more explicit lemma applications.

**Stability assessment:** Proofs appear stable — no retry flags, no extremely high rlimits (nothing above 100). InsertionSort is particularly clean with no custom options at all.

### 5.3 Proof Architecture

**InsertionSort:** The proof is structured around two nested loop invariants:
- Outer loop (lines 115-129): tracks `prefix_sorted`, permutation of `s0`, and comparison count.
- Inner loop (lines 149-175): tracks key position, comparison with neighbors, element preservation, and comparison count.
- Post-loop lemmas (`lemma_prefix_le_key`, `lemma_combine_sorted_regions`, `lemma_triangle_step`) are cleanly separated.

**MergeSort:** The proof is structured in layers:
1. Pure `seq_merge` + properties (length, count, sortedness).
2. Suffix lemmas relating imperative loop state to `seq_merge` output.
3. Imperative `merge_impl` loop invariant matching `ghost_merged`.
4. Recursive `merge_sort_aux` composing permutations.

**MergeSort.Complexity:** Clean inductive proof with explicit arithmetic lemmas (`log_linear_bound`, `arithmetic_step`).

---

## 6. Documentation & Comments

### 6.1 Module-Level Comments

| File | Comment Accurate? | Notes |
|------|-------------------|-------|
| `InsertionSort.fst` (lines 1-12) | ✅ Accurate | Claims "NO admits. NO assumes." — verified ✅ |
| `MergeSort.fst` (lines 1-14) | ✅ Accurate | Claims "NO admits. NO assumes." — verified ✅ |
| `MergeSort.Complexity.fst` (lines 5-18) | ✅ Accurate | Clearly states the bound and constant factor |
| `SortSpec.fst` (lines 1-14) | ✅ Accurate | Notes BoundedIntegers interaction — helpful |
| `Complexity.fst` (lines 1-20) | ⚠️ Partially stale | Claims "NO admits" ✅, but its `tick` uses `R.ref nat` not `GR.ref nat`, contradicting the "fully erased at runtime" claim made elsewhere |

### 6.2 README Accuracy

**`ch02-getting-started/README.md`:**

1. **Line 31, 57 — Signature mismatch.** README shows:
   ```
   pure (sorted s /\ is_permutation s0 s)
   ```
   Actual code uses `permutation` not `is_permutation`. The `is_permutation` name is from `Predicates.fst` which is not used by ch02.

2. **Line 29 — InsertionSort signature incomplete.** README omits the `ctr: GR.ref nat` parameter and the `#c0` ghost parameter. The actual signature (lines 92-110) includes complexity instrumentation.

3. **Line 55 — MergeSort parameter name.** README uses `n: SZ.t` but actual code uses `len: SZ.t` (line 551).

4. **Line 62 — Build path incorrect.** README says `cd /home/nswamy/workspace/clrs/ch02-getting-started` but the actual path is `/home/nswamy/workspace/everest/AutoCLRS/ch02-getting-started`.

5. **Line 13 — CLRS pseudocode.** README's pseudocode uses 0-indexed `for j = 1 to n-1` which doesn't match CLRS's 1-indexed `for j = 2 to A.length`. The implementation is 0-indexed, so the README matches the implementation but not CLRS.

### 6.3 Inline Comments

- **InsertionSort:** Comments are sparse but accurate. Line 30 section header, line 42 section header, line 76 section header, lines 84/86/91/126/138/147/171/213 — all accurate.
- **MergeSort:** Well-commented with section headers (`// ================================================================`). Strategy comments at lines 342-358 are helpful and accurate. The suffix-invariant approach is well-explained.
- **MergeSort.Complexity:** Extensive comments explaining the proof strategy. Lines 68-69 explain the bound rationale. Lines 234-246 provide practical interpretation. All accurate.

---

## 7. Task List

### High Priority

- `[ ] CH02-01: Bridge merge sort complexity to imperative code (Priority: High)`
  Add ghost tick counter to `merge_impl` and `merge_sort_aux`/`merge_sort` to prove that the imperative merge sort performs at most `merge_sort_ops(n)` comparisons. This closes the main spec gap — the O(n log n) bound is proved for the recurrence but not linked to the actual code.

- `[ ] CH02-02: Fix README signature mismatches (Priority: High)`
  Update `ch02-getting-started/README.md`:
  - Line 31/57: Change `is_permutation` → `permutation`
  - Line 29: Add `ctr` and `#c0` parameters to InsertionSort signature
  - Line 55: Change `n: SZ.t` → `len: SZ.t`
  - Line 62: Fix build path from `/home/nswamy/workspace/clrs/` to correct path

- `[ ] CH02-03: Unify tick counter approach (Priority: High)`
  `CLRS.Common.Complexity.fst` uses `R.ref nat` (runtime cost); `InsertionSort.fst` uses `GR.ref nat` (ghost, erased). Standardize on `GR.ref nat` in the common module since the counter should be ghost/erased. Update all downstream consumers.

### Medium Priority

- `[ ] CH02-04: Remove unused import in InsertionSort (Priority: Medium)`
  `CLRS.Ch02.InsertionSort.fst` line 28: `module Classical = FStar.Classical` is unused. Remove it.

- `[ ] CH02-05: Resolve Predicates.fst/fsti dead code (Priority: Medium)`
  `common/Predicates.fst` and `common/Predicates.fsti` define generic `sorted`, `is_permutation`, and heap predicates. These are not imported by any chapter. Either:
  (a) Migrate other chapters to use them (replacing per-chapter definitions), or
  (b) Remove them if `CLRS.Common.SortSpec.fst` is the canonical spec module.

- `[ ] CH02-06: Support empty arrays in InsertionSort (Priority: Medium)`
  The precondition `SZ.v len > 0` (line 102) rejects empty arrays. CLRS handles empty arrays trivially. Add an `if len = 0` early return to remove this restriction.

- `[ ] CH02-07: Reduce z3rlimit 80 in merge loop (Priority: Medium)`
  `CLRS.Ch02.MergeSort.fst` line 340: `--z3rlimit 80` is the highest in ch02. Try adding more explicit intermediate assertions or lemma calls in the merge loop body (lines 435-471) to reduce the rlimit, improving proof stability.

- `[ ] CH02-08: Reduce fuel 3 in seq_merge_count (Priority: Medium)`
  `CLRS.Ch02.MergeSort.fst` line 67: `--fuel 3 --ifuel 2` is high. The `seq_merge_count` proof (lines 79-99) may benefit from more explicit `Seq.head`/`Seq.tail` assertions to reduce fuel dependency.

- `[ ] CH02-09: Rename merge_impl to merge (Priority: Medium)`
  `merge_impl` (line 360) should be renamed to `merge` for consistency with CLRS naming. The `_impl` suffix suggests there's a spec-only version, but `seq_merge` already fills that role and has a different name.

### Low Priority

- `[ ] CH02-10: Document swap-vs-shift deviation (Priority: Low)`
  Add a comment in `CLRS.Ch02.InsertionSort.fst` near lines 180-184 noting that the implementation uses adjacent swaps instead of CLRS's shift-then-insert. Mention that comparison count is identical but write count differs.

- `[ ] CH02-11: Add SNIPPET markers to InsertionSort inner loop (Priority: Low)`
  InsertionSort has `SNIPPET_START/END` for the signature (lines 91, 110) but not for the inner loop. Add markers around the inner loop (lines 148-202) for documentation/extraction purposes.

- `[ ] CH02-12: Tighten merge sort complexity constant (Priority: Low)`
  The bound `4n⌈log₂ n⌉ + 4n` in `MergeSort.Complexity.fst` uses a constant factor of 4 (noted as deliberately loose at line 17). The tighter bound `n⌈log₂ n⌉` is achievable. This would make the bound more practically useful but requires a more complex proof.

- `[ ] CH02-13: Add practical test/extraction target (Priority: Low)`
  No executable test or extraction target exists in `ch02-getting-started/Makefile`. Consider adding a test that runs the sort on sample inputs to validate end-to-end correctness.

- `[ ] CH02-14: Harmonize SortSpec and Predicates modules (Priority: Low)`
  `CLRS.Common.SortSpec` and `CLRS.Common.Predicates` both define `sorted` and `permutation`/`is_permutation`. The naming differs (`permutation` vs `is_permutation`), and SortSpec is `int`-specialized while Predicates is generic. Long-term, these should be unified: either make SortSpec generic or have SortSpec instantiate Predicates.

---

## Summary

**Overall Assessment: Strong implementation with minor gaps.**

The Chapter 2 implementation is high quality:
- **Zero admits/assumes** across all files — all proofs are complete.
- **Full functional correctness** for both algorithms (sorted + permutation).
- **Tight complexity proof** for insertion sort with ghost instrumentation.
- **Clean code organization** with well-separated concerns.
- **Reasonable Z3 resource limits** with no stability concerns.

The main gaps are:
1. The merge sort complexity proof is not linked to the imperative code (CH02-01).
2. The README has several stale signatures and an incorrect path (CH02-02).
3. The common tick counter module uses a non-ghost reference, inconsistent with InsertionSort's approach (CH02-03).

| Metric | Score |
|--------|-------|
| CLRS Fidelity | 8/10 — Swap variant + no sentinels are valid but differ from textbook |
| Specification Strength | 8/10 — Strong for InsertionSort; MergeSort lacks complexity linkage |
| Complexity Proofs | 7/10 — InsertionSort excellent; MergeSort unlinked |
| Code Quality | 8/10 — Clean organization; minor duplication issues |
| Proof Quality | 10/10 — No admits, reasonable rlimits, stable |
| Documentation | 6/10 — README has multiple inaccuracies |
