# Ch04 C Code — Specification Review

Comparison of C code specifications vs. CLRS.Ch04.*.Impl.fsti interfaces.

## BinarySearch.c vs CLRS.Ch04.BinarySearch.Impl.fsti

### Impl.fsti specifies:
- [x] `SZ.v result <= SZ.v len` — result in bounds
- [x] `SZ.v result < SZ.v len ==> Seq.index s0 (SZ.v result) == key` — found → correct index
- [x] `SZ.v result == SZ.v len ==> forall i. Seq.index s0 i =!= key` — not found → absent
- [x] `is_sorted s0` precondition
- [ ] `complexity_bounded_log cf c0 (SZ.v len)` — O(log n) complexity (NOT wanted in C)

### C code proves:
- [x] `return <= len`
- [x] `return < len ==> a[return] == key`
- [x] `return == len ==> forall i. a[i] != key`
- [x] Sorted precondition

### Verdict: ✅ ALIGNED (complexity bound intentionally omitted)

---

## Kadane.c vs CLRS.Ch04.MaxSubarray.Kadane.fsti

### Impl.fsti specifies:
- [x] `result == max_subarray_spec s0` — functional correctness
- [ ] `complexity_bounded_linear cf c0 (SZ.v len)` — O(n) complexity (NOT wanted in C)
- [x] `SZ.v len > 0` precondition

### C code proves:
- [x] `return >= a[i]` for all i — result dominates all elements
- [x] `Int32.v return == max_subarray_spec_c (array_value_of a)` — functional correctness via bridge
- [x] Element bounds [-1000000, 1000000] and len <= 2000 (overflow prevention, C-specific)

### Verdict: ✅ ALIGNED (complexity bound intentionally omitted)

---

## MatrixMultiply.c vs CLRS.Ch04.MatrixMultiply.Impl.fsti

### Impl.fsti specifies:
- [x] `mat_mul_correct sa sb sc' n` — each `c[i][j] == dot_product_spec sa sb n i j n`
- [ ] `complexity_bounded_cubic cf c0 (SZ.v n)` — O(n³) complexity (NOT wanted in C)
- [x] `SZ.v n > 0`, `SZ.fits (n*n)`, length preconditions

### C code proves:
- [x] Memory safety and array bounds
- [x] Absence of integer overflow (via bound tracking)
- [x] Array length preservation
- [ ] **`dot_product` result == `dot_product_spec_c`** — NOT PROVEN
- [ ] **`mat_mul_correct_c sa sb sc' n`** — NOT PROVEN

### Status: ✅ FIXED (hand-edited .fst with functional correctness)

The `.fst` file is hand-edited (not c2pulse-generated) because c2pulse cannot generate
the `pinned_array`, `id #int`, and opaque interface patterns needed for functional correctness.

### What was fixed:
- [x] `dot_product` k-loop invariant proves `var_sum == dot_product_spec_c sa sb n i j k`
- [x] `dot_product` postcondition proves return value equals `dot_product_spec_c sa sb n i j n`
- [x] `matrix_multiply` i/j-loop invariants track `mat_mul_partial_ij_c` progress
- [x] `matrix_multiply` postcondition proves `mat_mul_correct_c sa sb sc' n`
- [x] Bridge lemmas (`.fsti` interface) make `dot_product_spec_c` opaque to prevent Z3 blowup
- [x] `pinned_array` helper fixes ghost sequences across loop iterations
- [x] All verification conditions discharged, all 6 C tests pass

### Root causes of c2pulse limitations:
1. `Int32.v` returns `int_t 32`, not `int` — need `id #int` wrapping
2. Recursive spec definitions pollute SMT — need opaque `.fsti` interface
3. `live_array` re-existentializes ghost sequences — need `pinned_array`
