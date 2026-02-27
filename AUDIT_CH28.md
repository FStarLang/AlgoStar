# Audit Report: Chapter 28 — Matrix Operations

**Scope**: `ch28-matrix-ops/` (2 files, 1217 LOC total)  
**Date**: 2025-02-26  
**Auditor**: Automated audit  

---

## 0. Executive Summary

This chapter provides a **high-quality**, **fully verified** implementation of:
1. **Standard matrix multiply** (SQUARE-MATRIX-MULTIPLY) — imperative Pulse, 242 LOC
2. **Strassen's algorithm** — pure F* specification, 975 LOC

Both files have **zero admits** and **zero assumes**. Verification artifacts (`.checked` files) exist in `_cache/`. Functional correctness and complexity are proven for the naive algorithm; functional correctness and a closed-form multiplication count are proven for Strassen. This is one of the cleanest chapters in the library.

**Overall grade: A−** (minor documentation inaccuracies, no proof gaps)

---

## 1. CLRS Fidelity

### 1.1 SQUARE-MATRIX-MULTIPLY (`CLRS.Ch28.MatrixMultiply.fst`)

| Aspect | CLRS (§4.2, p.75–76) | Implementation | Match? |
|--------|----------------------|----------------|--------|
| Structure | Triple-nested `for i,j,k` | Triple-nested `while` loops with mutable refs | ✅ Yes |
| Indexing | 1-based `i,j,k = 1..n` | 0-based `i,j,k = 0..n-1` | ✅ (conventional) |
| Init | `c_ij = 0` (line 5) | `A.op_Array_Assignment c idx_c 0` (line 176) | ✅ |
| Accumulate | `c_ij = c_ij + a_ik * b_kj` (line 7) | `c_val + a_val * b_val` (line 223) | ✅ |
| Storage | 2D matrix | Flat row-major array (`i*n+j`) | ✅ (valid encoding) |

**Verdict**: Faithful translation of CLRS SQUARE-MATRIX-MULTIPLY. The flat-array encoding is a standard choice for Pulse (no 2D array primitive).

### 1.2 Strassen's Algorithm (`CLRS.Ch28.Strassen.fst`)

| Aspect | CLRS (§4.2, pp.79–82) | Implementation | Match? |
|--------|------------------------|----------------|--------|
| Precondition | n is power of 2 | `pow2_size a` refinement | ✅ |
| Base case | 1×1 scalar multiply | `standard_multiply a b` when `n=1` | ✅ |
| Quadrant split | A₁₁,A₁₂,A₂₁,A₂₂ | `submatrix a 0 half 0 half`, etc. | ✅ |
| P1 = A₁₁(B₁₂−B₂₂) | S1=B₁₂−B₂₂, P1=A₁₁·S1 | `strassen_multiply a11 (matrix_sub b12 b22)` (line 217) | ✅ |
| P2 = (A₁₁+A₁₂)B₂₂ | S2=A₁₁+A₁₂, P2=S2·B₂₂ | `strassen_multiply (matrix_add a11 a12) b22` (line 219) | ✅ |
| P3 = (A₂₁+A₂₂)B₁₁ | S3=A₂₁+A₂₂, P3=S3·B₁₁ | `strassen_multiply (matrix_add a21 a22) b11` (line 221) | ✅ |
| P4 = A₂₂(B₂₁−B₁₁) | S4=B₂₁−B₁₁, P4=A₂₂·S4 | `strassen_multiply a22 (matrix_sub b21 b11)` (line 223) | ✅ |
| P5 = (A₁₁+A₂₂)(B₁₁+B₂₂) | S5=A₁₁+A₂₂, S6=B₁₁+B₂₂, P5=S5·S6 | `strassen_multiply (matrix_add a11 a22) (matrix_add b11 b22)` (line 225) | ✅ |
| P6 = (A₁₂−A₂₂)(B₂₁+B₂₂) | S7=A₁₂−A₂₂, S8=B₂₁+B₂₂, P6=S7·S8 | `strassen_multiply (matrix_sub a12 a22) (matrix_add b21 b22)` (line 227) | ✅ |
| P7 = (A₁₁−A₂₁)(B₁₁+B₁₂) | S9=A₁₁−A₂₁, S10=B₁₁+B₁₂, P7=S9·S10 | `strassen_multiply (matrix_sub a11 a21) (matrix_add b11 b12)` (line 229) | ✅ |
| C₁₁ = P5+P4−P2+P6 | Eq in CLRS p.80 | `matrix_add (matrix_sub (matrix_add p5 p4) p2) p6` (line 244) | ✅ |
| C₁₂ = P1+P2 | Eq in CLRS p.81 | `matrix_add p1 p2` (line 246) | ✅ |
| C₂₁ = P3+P4 | Eq in CLRS p.81 | `matrix_add p3 p4` (line 248) | ✅ |
| C₂₂ = P5+P1−P3−P7 | Eq in CLRS p.81 | `matrix_sub (matrix_sub (matrix_add p5 p1) p3) p7` (line 250) | ✅ |

**Verdict**: All 7 products and 4 result formulas match CLRS exactly. The S₁–S₁₀ intermediate matrices are inlined rather than named, which is cleaner.

### 1.3 Chapter Numbering Issue

⚠️ **CLRS Ch28** covers LUP decomposition, matrix inversion, and least-squares — **not** matrix multiplication. SQUARE-MATRIX-MULTIPLY and Strassen are in **CLRS §4.2** (Divide and Conquer). The library groups them under `ch28-matrix-ops/` for thematic convenience, and the documentation (README, `.rst`) references "§28.1" and "§28.2" which are incorrect CLRS section numbers. This is a documentation-only issue; the algorithms themselves are correct.

---

## 2. Specification Strength

### 2.1 MatrixMultiply — Functional Correctness

The specification is **strong and complete**:

```fstar
// Dot product: Σ_{k=0}^{limit-1} sa[i*n+k] * sb[k*n+j]
let rec dot_product_spec (sa sb: Seq.seq int) (n i j: nat) (limit: nat) ...

// Full correctness: ∀ i j. sc[i*n+j] == dot_product_spec sa sb n i j n
let mat_mul_correct (sa sb sc: Seq.seq int) (n: nat) : prop = ...
```

**Strengths**:
- `mat_mul_correct` states element-wise equality for all (i,j) pairs
- Intermediate predicates (`mat_mul_partial_k`, `mat_mul_partial_ij`) enable incremental proof via loop invariants
- The spec uses `int` (unbounded integers) — no overflow concerns in the logical spec
- Input arrays `a`, `b` use fractional permissions (read-only); output `c` has full permission

**Potential concern**: The `dot_product_spec` has defensive guards (returns 0 when indices are out of bounds or `n=0`). This is sound but means the spec is technically weaker than necessary for the out-of-bounds case — however, the `mat_mul_correct` predicate constrains indices to `i < n /\ j < n`, so this doesn't matter in practice.

### 2.2 Strassen — Functional Correctness

```fstar
// Strassen equals standard multiply element-wise
let lemma_strassen_correct (a b:matrix{...})
  : Lemma (ensures (forall (i:nat) (j:nat). i < rows a /\ j < cols b ==>
                    get_elem (strassen_multiply a b) i j == 
                    get_elem (standard_multiply a b) i j))
```

**Strengths**:
- Proves pointwise equivalence to `standard_multiply` (which is definitionally the textbook formula)
- The `standard_multiply` reference spec is clean and clearly correct
- Proof handles all 4 quadrant cases with explicit algebraic expansion

**Specification completeness**: The correctness theorem ties Strassen to `standard_multiply`, which in turn is definitionally `Σ_k a[i,k]*b[k,j]`. The chain is:
```
strassen_multiply == standard_multiply == Σ_k a[i,k]*b[k,j]
```
This is the strongest possible specification.

---

## 3. Complexity

### 3.1 MatrixMultiply — O(n³)

The complexity is proven **exactly** (not just asymptotically):

```fstar
let complexity_bounded_cubic (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n * n * n
```

The ghost counter `ctr` is incremented once per multiply-add via `tick` (line 228). The loop invariant tracks:
```
vc - c0 == vi * n * n + vj * n + vk
```
At loop exit (`vi=n, vj=0, vk=0`), this yields `cf - c0 = n³`. This is **exact** — not an upper bound but an equality.

**Verdict**: ✅ Exactly n³ multiply-add operations proven.

### 3.2 Strassen — O(n^{lg 7})

The complexity analysis proves:

1. **Recurrence**: `strassen_mult_count n = 7 * strassen_mult_count (n/2)`, `T(1) = 1` (line 281–283)
2. **Better than cubic**: `strassen_mult_count n < n³` for `n > 1` (lines 289–293)
3. **Closed form**: `strassen_mult_count n == pow7 (log2_floor n) == 7^{log₂ n} = n^{lg 7}` (lines 323–334)

**Strengths**:
- The closed-form proof is clean induction
- `pow7`, `log2_floor`, `is_pow2` are all well-defined
- `lemma_pow2_log2_inverse` connects `pow2(log2_floor n) == n`

**Note**: The complexity counts only **scalar multiplications**, not additions. This matches the CLRS analysis which focuses on the recurrence for multiplications. The Θ(n²) additions at each level are not counted, but the asymptotic class O(n^{lg 7}) ≈ O(n^{2.807}) is correctly characterized since n^{lg 7} dominates n².

---

## 4. Code Quality

### 4.1 MatrixMultiply (Pulse, 242 LOC)

| Aspect | Assessment |
|--------|-----------|
| **Readability** | Excellent. Clean triple-loop with clear variable names. |
| **Modularity** | Good. Spec, complexity, and implementation are clearly separated by comments and snippet markers. |
| **Naming** | Good. `flat_index`, `dot_product_spec`, `mat_mul_correct` are descriptive. |
| **Permission model** | Exemplary. Fractional read on inputs, full write on output. |
| **Index arithmetic** | Sound. `SZ.fits` checks prevent machine-integer overflow. `index_bounds_lemma` helper is clean. |
| **Style** | Idiomatic Pulse. Explicit array operations (`A.op_Array_Access`, `A.op_Array_Assignment`). |

### 4.2 Strassen (Pure F*, 975 LOC)

| Aspect | Assessment |
|--------|-----------|
| **Readability** | Very good. Well-commented with CLRS formula references. |
| **Modularity** | Excellent. Clear separation: matrix type → operations → algorithm → complexity → correctness. |
| **Proof structure** | Well-organized. Helper lemmas factored out (`lemma_submatrix_square_pow2`, connection lemmas). |
| **VC management** | Good. Uses `--split_queries always` and `smt_sync'` to avoid timeouts. Push/pop options are scoped. |
| **Length** | 975 LOC for algorithm + full algebraic correctness proof is reasonable. |

**Minor issues**:
- The `matrix` type uses seq-of-seq which is clean for pure specs but would need flattening for an imperative implementation
- The Strassen function is pure (not Pulse) — it cannot be extracted to executable code without further work

---

## 5. Proof Quality — Admits and Assumes

### 5.1 `CLRS.Ch28.MatrixMultiply.fst`

**Zero admits. Zero assumes.** ✅

Every obligation is discharged by Z3 with `--z3rlimit 50 --fuel 2 --ifuel 2`. The file is fully verified (`.checked` file dated 2025-02-26).

### 5.2 `CLRS.Ch28.Strassen.fst`

**Zero admits. Zero assumes.** ✅

All 975 lines verify without any proof gaps. The `.checked` file is dated 2025-02-23.

**Note on stale comment**: Line 34 of `CLRS.Ch28.Strassen.fst` says:
> "One admit: structural property that submatrix quadrants preserve square/pow2."

This comment is **outdated/incorrect**. The property is fully proven via `lemma_submatrix_square_pow2` (lines 549–556) and verified by F*. The comment should be updated.

### 5.3 Proof Techniques Used

| Technique | Where |
|-----------|-------|
| Ghost counter (`GhostReference`) | MatrixMultiply complexity |
| Fractional permissions | MatrixMultiply read-only inputs |
| `smt_sync'` tactic (20 uses) | Strassen quadrant case proofs |
| `--split_queries always` | Strassen main correctness lemma |
| Structural induction on `rows a` | `strassen_multiply`, `lemma_strassen_elem_correct` |
| Algebraic distributivity lemmas (4) | Strassen: `{add,sub}_{left,right}` |
| Connection lemmas for submatrix dot products | `lemma_dot_product_submatrix_first`, `lemma_dot_product_aux_submatrix_second` |

---

## 6. Documentation Accuracy

### 6.1 `README.md`

| Claim | Accurate? | Notes |
|-------|-----------|-------|
| "No admit() or assume statements" | ✅ | Verified by grep |
| "170 lines" | ❌ | File is 242 lines (243 with blank). Minor. |
| "Verified Pulse implementation" | ✅ | |
| "All array accesses are within bounds" | ✅ | `SZ.fits` + `index_bounds_lemma` |
| Only mentions MatrixMultiply | ⚠️ | Should also describe Strassen file |

### 6.2 `doc/ch28_matrix_ops.rst`

| Claim | Accurate? | Notes |
|-------|-----------|-------|
| "§28.1" / "§28.2" section references | ❌ | Should be §4.2 (CLRS Ch4, not Ch28) |
| "zero admits" for both files | ✅ | Correct |
| References `CLRS.Ch28.MatrixMultiply.Complexity.fst` | ❌ | **File does not exist** — complexity is integrated into `CLRS.Ch28.MatrixMultiply.fst`. The `.rst` has 4 `literalinclude` directives pointing to a nonexistent file (lines 100–115). |
| "smt_sync' for quadrant proofs" | ✅ | 20 uses confirmed |
| Proof technique descriptions | ✅ | Accurate and detailed |

### 6.3 Strassen file header comment (lines 1–36)

| Claim | Accurate? | Notes |
|-------|-----------|-------|
| P1–P7 formulas | ✅ | Match CLRS exactly |
| C11–C22 result formulas | ✅ | Match CLRS exactly |
| "One admit: structural property..." (line 34) | ❌ | **Stale comment**. Property is fully proven. |
| "All algebraic/arithmetic properties are fully proven" (line 35) | ✅ | |

---

## 7. Task List

### Priority 1 (High) — Documentation Bugs

| # | Task | File | Line(s) | Effort |
|---|------|------|---------|--------|
| 1 | Remove stale "One admit" comment — the property is fully proven | `CLRS.Ch28.Strassen.fst` | 34 | 1 min |
| 2 | Fix `.rst` references to nonexistent `CLRS.Ch28.MatrixMultiply.Complexity.fst` — point to `CLRS.Ch28.MatrixMultiply.fst` instead | `doc/ch28_matrix_ops.rst` | 100–115 | 5 min |
| 3 | Fix CLRS section references: "§28.1"/"§28.2" → "§4.2" | `doc/ch28_matrix_ops.rst` | 9, 20, 128 | 2 min |
| 4 | Update README line count "170 lines" → "~240 lines" | `README.md` | 21 | 1 min |
| 5 | Add Strassen description to README (currently only mentions MatrixMultiply) | `README.md` | — | 10 min |
| 6 | Note that Strassen complexity counts multiplications only, not additions | `doc/ch28_matrix_ops.rst` | ~190 | 2 min |
| 7 | Add an imperative (Pulse) Strassen implementation for extractable code | New file | Large |
| 10 | Reconcile the two dot product definitions (`dot_product_spec` in MatrixMultiply vs `dot_product` in Strassen) — they are equivalent but defined independently | Both files | Small |

## Defer

| 8 | Prove Strassen for non-power-of-2 matrices (CLRS Exercise 4.2-3) | `CLRS.Ch28.Strassen.fst` | Medium |
| 9 | Add `matrix_extensional_equality` lemma (two matrices equal iff all elements equal) to strengthen the correctness theorem from pointwise to structural equality | `CLRS.Ch28.Strassen.fst` | Small |

---

## 8. Summary Table

| Dimension | MatrixMultiply | Strassen |
|-----------|---------------|----------|
| **CLRS Fidelity** | ✅ Faithful | ✅ Faithful (all 7 products + 4 results exact) |
| **Spec Strength** | ✅ Strong (∀ i j. c[i,j] = Σ_k a[i,k]*b[k,j]) | ✅ Strong (pointwise == standard_multiply) |
| **Complexity** | ✅ Exact: cf−c0 = n³ | ✅ Closed form: 7^{log₂ n} < n³ |
| **Admits** | 0 | 0 |
| **Assumes** | 0 | 0 |
| **LOC** | 242 | 975 |
| **Verified** | ✅ (.checked 2025-02-26) | ✅ (.checked 2025-02-23) |
| **Executable** | ✅ (Pulse, can extract to C) | ❌ (Pure spec only) |
