# Chapter 04: Divide and Conquer — Rubric Compliance

**Directory**: `ch04-divide-conquer/`
**Date**: 2025-07-18
**Baseline**: `RUBRIC.md` (canonical), `AUDIT_CH04.md` (existing audit)

---

## Current File Inventory

| File | Role | Rubric Category | Pulse/F\* | Lines |
|------|------|-----------------|-----------|-------|
| `CLRS.Ch04.BinarySearch.fst` | Impl + Spec + Complexity (monolith) | Impl / Spec / Complexity | Pulse | 185 |
| `CLRS.Ch04.MaxSubarray.Spec.fst` | Shared pure spec (`kadane_spec`, `sum_range`, optimality theorems) | Spec + Lemmas | F\* | 155 |
| `CLRS.Ch04.MaxSubarray.DivideConquer.fst` | D&C algorithm + correctness + complexity + equivalence | Spec + Lemmas + Complexity | F\* | 383 |
| `CLRS.Ch04.MaxSubarray.Kadane.fst` | Verified imperative Kadane | Impl | Pulse | 116 |
| `CLRS.Ch04.MatrixMultiply.fst` | Verified imperative matrix multiply (CLRS §4.2) | Impl + Spec + Complexity (monolith) | Pulse | 248 |
| `CLRS.Ch04.Strassen.fst` | Strassen algorithm + correctness + complexity | Spec + Lemmas + Complexity (monolith) | F\* | 978 |
| `Test.BinarySearch.fst` | Smoke tests (found / not-found) | Test | Pulse | 76 |
| `Test.MaxSubarray.fst` | Print-only example; no executable test | Test (stub) | F\* (ML) | 24 |

**No `.fsti` interface files exist in this directory.**

---

## Algorithms Covered

| # | Algorithm | CLRS Reference | Files |
|---|-----------|----------------|-------|
| 1 | **Binary Search** | Exercise 2.3-5 (iterative) | `CLRS.Ch04.BinarySearch.fst` |
| 2 | **Maximum Subarray — Kadane** | Exercise 4.1-5 (linear-time) | `CLRS.Ch04.MaxSubarray.Spec.fst`, `CLRS.Ch04.MaxSubarray.Kadane.fst` |
| 3 | **Maximum Subarray — D&C** | Section 4.1 (`FIND-MAXIMUM-SUBARRAY`) | `CLRS.Ch04.MaxSubarray.Spec.fst`, `CLRS.Ch04.MaxSubarray.DivideConquer.fst` |
| 4 | **Matrix Multiply (standard)** | Section 4.2, pp. 75–76 (`SQUARE-MATRIX-MULTIPLY`) | `CLRS.Ch04.MatrixMultiply.fst` |
| 5 | **Strassen's Matrix Multiply** | Section 4.2, pp. 79–82 | `CLRS.Ch04.Strassen.fst` |

---

## Rubric Compliance Matrix

### Expected file structure per RUBRIC.md

Per algorithm `AlgoName`, the rubric requires:

| Slot | Expected File |
|------|---------------|
| Spec.fst | `CLRS.Ch04.AlgoName.Spec.fst` |
| Lemmas.fst | `CLRS.Ch04.AlgoName.Lemmas.fst` |
| Lemmas.fsti | `CLRS.Ch04.AlgoName.Lemmas.fsti` |
| Complexity.fst | `CLRS.Ch04.AlgoName.Complexity.fst` |
| Complexity.fsti | `CLRS.Ch04.AlgoName.Complexity.fsti` |
| Impl.fst | `CLRS.Ch04.AlgoName.Impl.fst` |
| Impl.fsti | `CLRS.Ch04.AlgoName.Impl.fsti` |

### 1. Binary Search

| Slot | File | Status | Notes |
|------|------|--------|-------|
| Spec.fst | — | ❌ Missing | `is_sorted`, `log2f`, `complexity_bounded_log` are in `BinarySearch.fst` |
| Lemmas.fst | — | ❌ Missing | `lemma_log2f_mono`, `lemma_log2f_step` are in `BinarySearch.fst` |
| Lemmas.fsti | — | ❌ Missing | No interface file exists |
| Complexity.fst | — | ❌ Missing | Complexity proof is inlined in the Pulse loop invariant |
| Complexity.fsti | — | ❌ Missing | No interface file exists |
| Impl.fst | `CLRS.Ch04.BinarySearch.fst` | 🔶 Exists but monolithic | Contains spec + lemmas + impl in one file |
| Impl.fsti | — | ❌ Missing | No interface file exists |

### 2. Maximum Subarray — Kadane

| Slot | File | Status | Notes |
|------|------|--------|-------|
| Spec.fst | `CLRS.Ch04.MaxSubarray.Spec.fst` | ✅ Exists | `kadane_spec`, `max_subarray_spec`, `sum_range`, `max_suffix_sum`, `max_sub_sum` |
| Lemmas.fst | `CLRS.Ch04.MaxSubarray.Spec.fst` | 🔶 Merged into Spec | `lemma_kadane_correct`, `theorem_kadane_optimal`, `theorem_kadane_witness`, `lemma_max_suffix_ge`, `lemma_max_sub_ge`, witness functions |
| Lemmas.fsti | — | ❌ Missing | No interface file exists |
| Complexity.fst | — | ❌ Missing | `complexity_bounded_linear` is in `Kadane.fst` |
| Complexity.fsti | — | ❌ Missing | No interface file exists |
| Impl.fst | `CLRS.Ch04.MaxSubarray.Kadane.fst` | ✅ Exists | `max_subarray` Pulse fn |
| Impl.fsti | — | ❌ Missing | No interface file exists |

### 3. Maximum Subarray — D&C

| Slot | File | Status | Notes |
|------|------|--------|-------|
| Spec.fst | `CLRS.Ch04.MaxSubarray.Spec.fst` (shared) + `DivideConquer.fst` | 🔶 Partially | D&C algorithm functions are in DivideConquer.fst; shared spec in Spec.fst |
| Lemmas.fst | `CLRS.Ch04.MaxSubarray.DivideConquer.fst` | 🔶 Merged | `lemma_dc_sum_correct`, `lemma_dc_optimal`, `lemma_dc_nonempty`, `dc_kadane_equivalence`, crossing lemmas |
| Lemmas.fsti | — | ❌ Missing | No interface file exists |
| Complexity.fst | `CLRS.Ch04.MaxSubarray.DivideConquer.fst` | 🔶 Merged | `dc_ops_count`, `log2_ceil`, `lemma_dc_complexity_bound`, helper lemmas |
| Complexity.fsti | — | ❌ Missing | No interface file exists |
| Impl.fst | — | ❌ Missing | D&C is pure F\*, no Pulse impl exists |
| Impl.fsti | — | ❌ Missing | No interface file exists |

### 4. Matrix Multiply (Standard)

| Slot | File | Status | Notes |
|------|------|--------|-------|
| Spec.fst | — | ❌ Missing | `flat_index`, `dot_product_spec`, `mat_mul_correct`, `mat_mul_partial_k`, `mat_mul_partial_ij` are in `MatrixMultiply.fst` |
| Lemmas.fst | — | ❌ Missing | `index_bounds_lemma` is in `MatrixMultiply.fst` |
| Lemmas.fsti | — | ❌ Missing | No interface file exists |
| Complexity.fst | — | ❌ Missing | `complexity_bounded_cubic` is in `MatrixMultiply.fst` |
| Complexity.fsti | — | ❌ Missing | No interface file exists |
| Impl.fst | `CLRS.Ch04.MatrixMultiply.fst` | 🔶 Exists but monolithic | Contains spec + complexity + impl |
| Impl.fsti | — | ❌ Missing | No interface file exists |

### 5. Strassen's Matrix Multiply

| Slot | File | Status | Notes |
|------|------|--------|-------|
| Spec.fst | `CLRS.Ch04.Strassen.fst` | 🔶 Merged | `matrix` type, `standard_multiply`, `strassen_multiply`, matrix ops |
| Lemmas.fst | `CLRS.Ch04.Strassen.fst` | 🔶 Merged | ~25 lemmas including `lemma_strassen_correct`, `lemma_strassen_elem_correct`, `lemma_standard_multiply_correct`, all dot-product lemmas |
| Lemmas.fsti | — | ❌ Missing | No interface file exists |
| Complexity.fst | `CLRS.Ch04.Strassen.fst` | 🔶 Merged | `strassen_mult_count`, `standard_mult_count`, `pow7`, `log2_floor`, `lemma_strassen_better_than_cubic`, `lemma_strassen_mult_closed_form` |
| Complexity.fsti | — | ❌ Missing | No interface file exists |
| Impl.fst | — | ❌ Missing | Strassen is pure F\*, no Pulse impl exists |
| Impl.fsti | — | ❌ Missing | No interface file exists |

---

## Detailed Action Items

### Algorithm 1: Binary Search

#### [SPLIT] `CLRS.Ch04.BinarySearch.fst` → 4 files

**Create `CLRS.Ch04.BinarySearch.Spec.fst`** (pure F\*):
- Move `is_sorted` (line 67–68)
- Move `log2f` (line 42–44)
- Move `complexity_bounded_log` (line 72–73)

**Create `CLRS.Ch04.BinarySearch.Lemmas.fst`** (pure F\*):
- Move `lemma_log2f_mono` (lines 46–55)
- Move `lemma_log2f_step` (lines 57–63)
- `open CLRS.Ch04.BinarySearch.Spec`

**Create `CLRS.Ch04.BinarySearch.Lemmas.fsti`**:
- Export `val lemma_log2f_mono (a b: int) : Lemma (requires a >= 1 /\ b >= 1 /\ a <= b) (ensures log2f a <= log2f b)`
- Export `val lemma_log2f_step (old_range new_range: int) : Lemma (requires ...) (ensures ...)`

**[RENAME]** `CLRS.Ch04.BinarySearch.fst` → `CLRS.Ch04.BinarySearch.Impl.fst`:
- Change module declaration to `CLRS.Ch04.BinarySearch.Impl`
- Add `open CLRS.Ch04.BinarySearch.Spec`
- Add `open CLRS.Ch04.BinarySearch.Lemmas`
- Remove moved definitions (`is_sorted`, `log2f`, `complexity_bounded_log`, `lemma_log2f_mono`, `lemma_log2f_step`)
- Keep `incr_nat`, `tick`, `binary_search`

**[CREATE] `CLRS.Ch04.BinarySearch.Impl.fsti`**:
- Export `val binary_search (a: array int) ... : ...` with the full signature from lines 80–107

**[UPDATE] `Test.BinarySearch.fst`**:
- Change `open CLRS.Ch04.BinarySearch` → `open CLRS.Ch04.BinarySearch.Impl`

---

### Algorithm 2: Maximum Subarray — Kadane

#### [SPLIT] Spec.fst: extract lemmas

**[RENAME]** `CLRS.Ch04.MaxSubarray.Spec.fst` — keep only specs:
- Keep: `max_int` (line 18), `initial_min` (line 21), `kadane_spec` (lines 26–38), `max_subarray_spec` (lines 41–43), `sum_range` (lines 48–54), `max_suffix_sum` (lines 69–72), `max_sub_sum` (lines 75–78), `elements_bounded` (lines 81–82)
- Keep: `lemma_sum_range_append` (lines 57–64) — used by both downstream modules

**[CREATE] `CLRS.Ch04.MaxSubarray.Lemmas.fst`** (pure F\*):
- Move `lemma_max_suffix_ge` (lines 87–95)
- Move `max_suffix_witness` (lines 98–106)
- Move `lemma_max_sub_ge` (lines 109–114)
- Move `max_sub_witness` (lines 117–125)
- Move `lemma_kadane_correct` (lines 128–137)
- Move `theorem_kadane_optimal` (lines 140–145)
- Move `theorem_kadane_witness` (lines 148–155)
- `open CLRS.Ch04.MaxSubarray.Spec`

**[CREATE] `CLRS.Ch04.MaxSubarray.Lemmas.fsti`**:
- Export:
  - `val lemma_kadane_correct ...`
  - `val theorem_kadane_optimal (s: Seq.seq int) (i j: nat) : Lemma (requires ...) (ensures max_subarray_spec s >= sum_range s i j)`
  - `val theorem_kadane_witness (s: Seq.seq int) : Lemma (requires ...) (ensures exists ...)`
  - `val max_suffix_witness (s: Seq.seq int) (i: nat) : Pure nat ...`
  - `val max_sub_witness (s: Seq.seq int) (i: nat) : Pure (nat & nat) ...`
  - `val lemma_max_suffix_ge ...`
  - `val lemma_max_sub_ge ...`

#### [SPLIT] Kadane.fst: extract complexity

**[CREATE] `CLRS.Ch04.MaxSubarray.Kadane.Complexity.fst`** (pure F\*):
- Move `complexity_bounded_linear` (line 43) from `Kadane.fst`

**[CREATE] `CLRS.Ch04.MaxSubarray.Kadane.Complexity.fsti`**:
- Export `let complexity_bounded_linear (cf c0 n: nat) : prop`

**[RENAME]** `CLRS.Ch04.MaxSubarray.Kadane.fst` → `CLRS.Ch04.MaxSubarray.Kadane.Impl.fst`:
- Change module declaration
- Add `open CLRS.Ch04.MaxSubarray.Kadane.Complexity`
- Remove `complexity_bounded_linear`

**[CREATE] `CLRS.Ch04.MaxSubarray.Kadane.Impl.fsti`**:
- Export `val max_subarray (a: array int) ...` with the full signature from lines 49–65

**[UPDATE] `Test.MaxSubarray.fst`**:
- Change `open CLRS.Ch04.MaxSubarray.Kadane` → `open CLRS.Ch04.MaxSubarray.Kadane.Impl`

---

### Algorithm 3: Maximum Subarray — D&C

#### [SPLIT] `CLRS.Ch04.MaxSubarray.DivideConquer.fst` → 3 files

**[CREATE] `CLRS.Ch04.MaxSubarray.DivideConquer.Spec.fst`** (pure F\*):
- Move `find_max_crossing_left` (lines 32–46)
- Move `find_max_crossing_right` (lines 50–61)
- Move `find_max_crossing_subarray` (lines 64–75)
- Move `find_maximum_subarray_dc` (lines 81–102)
- Move `find_maximum_subarray_sum` (lines 106–111)
- `open CLRS.Ch04.MaxSubarray.Spec`

**[CREATE] `CLRS.Ch04.MaxSubarray.DivideConquer.Lemmas.fst`** (pure F\*):
- Move all correctness lemmas:
  - `lemma_dc_base_case` (lines 183–188)
  - `lemma_dc_empty_case` (lines 191–196)
  - `lemma_crossing_left_sum` (lines 199–218)
  - `lemma_crossing_right_sum` (lines 221–237)
  - `lemma_crossing_sum_correct` (lines 240–261)
  - `lemma_dc_sum_correct` (lines 265–287)
  - `lemma_crossing_left_opt` (lines 295–308)
  - `lemma_crossing_right_opt` (lines 310–323)
  - `lemma_dc_nonempty` (lines 327–335)
  - `lemma_dc_optimal` (lines 337–351)
  - `dc_kadane_equivalence` (lines 360–374)
- Remove `lemma_dc_equals_kadane` (lines 377–382) — dead code, duplicates `dc_kadane_equivalence`
- `open CLRS.Ch04.MaxSubarray.DivideConquer.Spec`
- `open CLRS.Ch04.MaxSubarray.Lemmas` (for `max_sub_witness` etc.)

**[CREATE] `CLRS.Ch04.MaxSubarray.DivideConquer.Lemmas.fsti`**:
- Export:
  - `val lemma_dc_sum_correct (s: Seq.seq int) (low high: nat) : Lemma ...`
  - `val lemma_dc_optimal (s: Seq.seq int) (low high qi qj: nat) : Lemma ...`
  - `val lemma_dc_nonempty (s: Seq.seq int) (low high: nat) : Lemma ...`
  - `val dc_kadane_equivalence (s: Seq.seq int) : Lemma ...`

**[CREATE] `CLRS.Ch04.MaxSubarray.DivideConquer.Complexity.fst`** (pure F\*):
- Move `dc_ops_count` (lines 118–124)
- Move `log2_ceil` (lines 127–129)
- Move `lemma_log2_ceil_bounds` (lines 132–141)
- Move `log2_ceil_monotone` (lines 144–152)
- Move `log2_ceil_halving` (lines 155–158)
- Move `lemma_dc_complexity_bound` (lines 163–178)

**[CREATE] `CLRS.Ch04.MaxSubarray.DivideConquer.Complexity.fsti`**:
- Export:
  - `val dc_ops_count (n: nat) : Tot nat`
  - `val log2_ceil (n: pos) : Tot nat`
  - `val lemma_dc_complexity_bound (n: pos) : Lemma (ensures dc_ops_count n <= op_Multiply 4 (op_Multiply n (log2_ceil n + 1)))`

**Refactor remaining `CLRS.Ch04.MaxSubarray.DivideConquer.fst`**:
- Remove `min_int` (line 26) — dead code, never used
- Remove all moved definitions
- This file becomes empty and can be deleted (all content moved to `.Spec`, `.Lemmas`, `.Complexity`)

---

### Algorithm 4: Matrix Multiply (Standard)

#### [SPLIT] `CLRS.Ch04.MatrixMultiply.fst` → 4 files

**[CREATE] `CLRS.Ch04.MatrixMultiply.Spec.fst`** (pure F\*):
- Move `flat_index` (line 45)
- Move `index_bounds_lemma` (line 48–51)
- Move `dot_product_spec` (lines 54–61)
- Move `mat_mul_correct` (lines 67–70)
- Move `mat_mul_partial_k` (lines 74–76)
- Move `mat_mul_partial_ij` (lines 79–82)
- Move `complexity_bounded_cubic` (lines 88–89)

**[CREATE] `CLRS.Ch04.MatrixMultiply.Spec.fsti`**:
- Export all spec definitions above

**[CREATE] `CLRS.Ch04.MatrixMultiply.Lemmas.fst`**:
- Move `index_bounds_lemma` (line 48–51) if considered a lemma rather than spec
- (Currently no other lemmas; file can be minimal or omitted)

**[RENAME]** `CLRS.Ch04.MatrixMultiply.fst` → `CLRS.Ch04.MatrixMultiply.Impl.fst`:
- Change module declaration
- Add `open CLRS.Ch04.MatrixMultiply.Spec`
- Remove moved definitions
- Keep `incr_nat`, `tick`, `matrix_multiply`

**[CREATE] `CLRS.Ch04.MatrixMultiply.Impl.fsti`**:
- Export `val matrix_multiply (#pa #pb: perm) (a b c: array int) ...` with the full signature from lines 96–128

---

### Algorithm 5: Strassen's Matrix Multiply

#### [SPLIT] `CLRS.Ch04.Strassen.fst` (978 lines) → 3+ files

**[CREATE] `CLRS.Ch04.Strassen.Spec.fst`** (pure F\*):
- Move `matrix` type (lines 52–57)
- Move `rows`, `cols`, `is_square`, `get_elem` (lines 59–68)
- Move `is_pow2`, `pow2_size` (lines 73–79)
- Move `matrix_add`, `matrix_sub` (lines 100–120)
- Move `dot_product`, `standard_multiply` (lines 123–139)
- Move `submatrix`, `assemble_quadrants` (lines 142–192)
- Move `strassen_multiply` (lines 195–271)
- Move `log2_floor`, `pow7`, `strassen_mult_count`, `standard_mult_count` (lines 273–290)

**[CREATE] `CLRS.Ch04.Strassen.Lemmas.fst`** (pure F\*):
- Move `lemma_pow2_half`, `lemma_pow2_double`, `lemma_submatrix_pow2` (lines 82–98)
- Move `dot_product_aux` (lines 343–349)
- Move `lemma_dot_product_split` (lines 351–380)
- Move `lemma_standard_multiply_correct` (lines 382–385)
- Move `lemma_submatrix_elem` (lines 387–394)
- Move `lemma_matrix_add_elem`, `lemma_matrix_sub_elem` (lines 396–406)
- Move `lemma_assemble_quadrants_elem` (lines 408–446)
- Move `lemma_dot_product_add_left`, `lemma_matrix_product_add_left` (lines 448–469)
- Move `lemma_dot_product_add_right`, `lemma_matrix_product_add_right` (lines 471–491)
- Move `lemma_dot_product_sub_right`, `lemma_matrix_product_sub_right` (lines 493–513)
- Move `lemma_dot_product_sub_left`, `lemma_matrix_product_sub_left` (lines 515–537)
- Move `lemma_dot_product_quadrant_split` (lines 538–549)
- Move `lemma_submatrix_square_pow2` (lines 551–569)
- Move `lemma_dot_product_submatrix_first` (lines 571–601)
- Move `lemma_dot_product_aux_submatrix_second` (lines 603–632)
- Move `lemma_standard_multiply_quadrant_decomp` (lines 634–673)
- Move `lemma_strassen_elem_correct` (lines 675–961)
- Move `lemma_strassen_correct` (lines 965–973)

**[CREATE] `CLRS.Ch04.Strassen.Lemmas.fsti`**:
- Export:
  - `val lemma_strassen_correct (a b:matrix{...}) : Lemma (ensures forall i j. get_elem (strassen_multiply a b) i j == get_elem (standard_multiply a b) i j)`

**[CREATE] `CLRS.Ch04.Strassen.Complexity.fst`** (pure F\*):
- Move `lemma_strassen_better_than_cubic` (lines 292–302)
- Move `lemma_pow2_log2_inverse` (lines 304–313)
- Move `lemma_log2_half` (lines 315–318)
- Move `lemma_pow7_succ` (lines 320–324)
- Move `lemma_strassen_mult_closed_form` (lines 326–341)

**[CREATE] `CLRS.Ch04.Strassen.Complexity.fsti`**:
- Export:
  - `val lemma_strassen_better_than_cubic (n:pos{is_pow2 n /\ n > 1}) : Lemma (ensures strassen_mult_count n < standard_mult_count n)`
  - `val lemma_strassen_mult_closed_form (n:pos{is_pow2 n}) : Lemma (ensures strassen_mult_count n == pow7 (log2_floor n))`

---

### Cross-Cutting Action Items

#### [DEDUP] Ghost tick infrastructure

**[CREATE] `CLRS.Common.GhostComplexity.fst`** (in `common/`):
- Extract shared `incr_nat`, `tick` ghost fn, `complexity_bounded_linear`, `complexity_bounded_log`, `complexity_bounded_cubic`
- Currently duplicated in: `BinarySearch.fst` (lines 30–38), `Kadane.fst` (lines 31–39), `MatrixMultiply.fst` (lines 30–38)

**[UPDATE]** After creating `CLRS.Common.GhostComplexity`:
- Remove `incr_nat`/`tick` from `CLRS.Ch04.BinarySearch.Impl.fst`
- Remove `incr_nat`/`tick` from `CLRS.Ch04.MaxSubarray.Kadane.Impl.fst`
- Remove `incr_nat`/`tick` from `CLRS.Ch04.MatrixMultiply.Impl.fst`
- Add `open CLRS.Common.GhostComplexity` to each

#### [DELETE] Dead code

- `min_int` in `CLRS.Ch04.MaxSubarray.DivideConquer.fst` line 26 — defined but never used
- `lemma_dc_equals_kadane` in `CLRS.Ch04.MaxSubarray.DivideConquer.fst` lines 377–382 — trivial wrapper of `dc_kadane_equivalence` with identical spec

---

## Quality Checks

### Admits / Assumes / Axioms

| File | `admit()` | `admit_` | `assume` | `assume val` | `sorry` |
|------|-----------|----------|----------|--------------|---------|
| `CLRS.Ch04.BinarySearch.fst` | 0 | 0 | 0 | 0 | 0 |
| `CLRS.Ch04.MaxSubarray.Spec.fst` | 0 | 0 | 0 | 0 | 0 |
| `CLRS.Ch04.MaxSubarray.DivideConquer.fst` | 0 | 0 | 0 | 0 | 0 |
| `CLRS.Ch04.MaxSubarray.Kadane.fst` | 0 | 0 | 0 | 0 | 0 |
| `CLRS.Ch04.MatrixMultiply.fst` | 0 | 0 | 0 | 0 | 0 |
| `CLRS.Ch04.Strassen.fst` | 0 | 0 | 0 | 0 | 0 |
| `Test.BinarySearch.fst` | 0 | 0 | 0 | 0 | 0 |
| `Test.MaxSubarray.fst` | 0 | 0 | 0 | 0 | 0 |

**All 8 files are admit-free.** ✅

### Solver Hints

| File | Directive | Location |
|------|-----------|----------|
| `CLRS.Ch04.BinarySearch.fst` | `--z3rlimit 20` | Line 77 |
| `CLRS.Ch04.MatrixMultiply.fst` | `--z3rlimit 50 --fuel 2 --ifuel 2` | Line 25 |
| `CLRS.Ch04.Strassen.fst` | `--fuel 2 --ifuel 1 --z3rlimit 20` | Line 46 |

No `--retry`, `--z3seed`, `--quake` directives. Proof stability is excellent.

### Interface Coverage

| Category | Count | Expected | Gap |
|----------|-------|----------|-----|
| `.fsti` files present | 0 | 12 (min: 5 Impl.fsti + 5 Lemmas.fsti + 2 Complexity.fsti) | **0 / 12** |
| Monolithic files needing split | 4 | 0 | BinarySearch, MatrixMultiply, Strassen, DivideConquer |
| Algorithms fully rubric-compliant | 0 | 5 | — |
| Algorithms partially compliant | 3 | — | MaxSubarray.Kadane (has Spec), MaxSubarray.DivideConquer (has Spec), Strassen (conceptual separation within file) |
| Algorithms non-compliant | 2 | — | BinarySearch, MatrixMultiply (fully monolithic) |

### Test Coverage

| Algorithm | Has Tests? | Quality |
|-----------|-----------|---------|
| Binary Search | ✅ `Test.BinarySearch.fst` | Basic (2 cases: found, not-found). Missing: single element, duplicates, boundaries. |
| MaxSubarray Kadane | ❌ | `Test.MaxSubarray.fst` only prints strings; no actual call to `max_subarray` |
| MaxSubarray D&C | ❌ | No test file |
| Matrix Multiply | ❌ | No test file |
| Strassen | ❌ | No test file |

### Code Duplication

| Duplicated Code | Locations | Action |
|----------------|-----------|--------|
| `incr_nat` definition | `BinarySearch.fst:30`, `Kadane.fst:31`, `MatrixMultiply.fst:30` | Extract to `CLRS.Common.GhostComplexity` |
| `tick` ghost function | `BinarySearch.fst:32–38`, `Kadane.fst:33–39`, `MatrixMultiply.fst:32–38` | Extract to `CLRS.Common.GhostComplexity` |
| `complexity_bounded_*` | `BinarySearch.fst:72`, `Kadane.fst:43`, `MatrixMultiply.fst:88` | Extract to `CLRS.Common.GhostComplexity` |

### Summary

| Dimension | BinarySearch | Kadane | D&C | MatrixMultiply | Strassen |
|-----------|:---:|:---:|:---:|:---:|:---:|
| Rubric file layout | ❌ Monolith | 🔶 Partial | 🔶 Partial | ❌ Monolith | ❌ Monolith |
| .fsti interfaces | ❌ None | ❌ None | ❌ None | ❌ None | ❌ None |
| Spec strength | Strong | Strong | Strong | Strong | Strong |
| Complexity proof | O(log n) ✅ | O(n) ✅ | O(n log n) ✅ | O(n³) ✅ | O(n^{lg 7}) ✅ |
| Admits | 0 ✅ | 0 ✅ | 0 ✅ | 0 ✅ | 0 ✅ |
| Tests | Basic | ❌ None | ❌ None | ❌ None | ❌ None |
| Dead code | None | None | 2 items | None | None |
| Duplication | `tick`/`incr_nat` | `tick`/`incr_nat` | None | `tick`/`incr_nat` | None |

---

*End of rubric compliance report.*
