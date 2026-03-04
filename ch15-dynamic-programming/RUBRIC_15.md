# Chapter 15: Dynamic Programming — Rubric Compliance

## Current File Inventory

| File | Role | Rubric Category | Pulse/F\* | Lines |
|------|------|-----------------|-----------|-------|
| `CLRS.Ch15.RodCutting.DPSpec.fst` | Shared DP recurrence definitions | Spec (shared) | F\* | 112 |
| `CLRS.Ch15.RodCutting.Spec.fst` | Optimality & substructure proofs | Lemmas | F\* | 340 |
| `CLRS.Ch15.RodCutting.fst` | Bottom-up DP impl + O(n²) ghost ticks | Impl + Complexity | Pulse | 274 |
| `CLRS.Ch15.RodCutting.Extended.fst` | EXTENDED-BOTTOM-UP-CUT-ROD (revenue + cuts `s[]`) | Impl (extended) | Pulse | 561 |
| `CLRS.Ch15.RodCutting.Test.fst` | CLRS example test | Test | Pulse | 55 |
| `CLRS.Ch15.MatrixChain.fst` | MATRIX-CHAIN-ORDER impl | Impl | Pulse | 293 |
| `CLRS.Ch15.MatrixChain.Spec.fst` | Recursive spec (Eq. 15.7), optimality, sentinel discharge | Spec + Lemmas | F\* | 768 |
| `CLRS.Ch15.MatrixChain.Complexity.fst` | O(n³) bound, exact (n³−n)/6 | Complexity | F\* | 106 |
| `CLRS.Ch15.MatrixChain.Extended.fst` | Extended impl with split-point table `s[i,j]` | Impl (extended) | Pulse | 446 |
| `CLRS.Ch15.MatrixChain.Test.fst` | CLRS example test | Test | Pulse | 55 |
| `CLRS.Ch15.LCS.fst` | LCS-LENGTH impl + O(mn) ghost ticks | Impl + Complexity | Pulse | 302 |
| `CLRS.Ch15.LCS.Spec.fst` | Subsequence defs, optimality + witness | Spec + Lemmas | F\* | 329 |

---

## Algorithms Covered

| Algorithm | CLRS Section | CLRS Procedure | Status |
|-----------|-------------|----------------|--------|
| Rod Cutting | §15.1 | BOTTOM-UP-CUT-ROD | ✅ Fully verified |
| Rod Cutting (Extended) | §15.1 | EXTENDED-BOTTOM-UP-CUT-ROD | ✅ Fully verified |
| Matrix Chain Multiplication | §15.2 | MATRIX-CHAIN-ORDER | ✅ Fully verified |
| Matrix Chain (Extended) | §15.2 | MATRIX-CHAIN-ORDER with `s` table | ✅ Cost verified |
| Longest Common Subsequence | §15.4 | LCS-LENGTH | ✅ Fully verified |

---

## Rubric Compliance Matrix

The canonical rubric requires seven artifacts per algorithm:
`Spec.fst` | `Lemmas.fst` | `Lemmas.fsti` | `Complexity.fst` | `Complexity.fsti` | `Impl.fst` | `Impl.fsti`

| Artifact | RodCutting | MatrixChain | LCS |
|----------|-----------|-------------|-----|
| **Spec** | 🔶 `DPSpec.fst` (shared defs) + defs inlined in `RodCutting.fst` | ✅ `MatrixChain.Spec.fst` (768 lines) | 🔶 Defs inlined in `LCS.fst` |
| **Lemmas** | 🔶 `RodCutting.Spec.fst` (named `Spec`, not `Lemmas`) | 🔶 In `MatrixChain.Spec.fst` (merged with Spec) | 🔶 `LCS.Spec.fst` (named `Spec`, not `Lemmas`) |
| **Lemmas.fsti** | ❌ Missing | ❌ Missing | ❌ Missing |
| **Complexity** | 🔶 Embedded in `RodCutting.fst` (ghost ticks) | ✅ `MatrixChain.Complexity.fst` | 🔶 Embedded in `LCS.fst` (ghost ticks) |
| **Complexity.fsti** | ❌ Missing | ❌ Missing | ❌ Missing |
| **Impl** | ✅ `RodCutting.fst` (Pulse) | ✅ `MatrixChain.fst` (Pulse) | ✅ `LCS.fst` (Pulse) |
| **Impl.fsti** | ❌ Missing | ❌ Missing | ❌ Missing |

### Legend
- ✅ = Exists as a separate file matching rubric naming
- 🔶 = Content exists but naming/structure deviates from rubric
- ❌ = File does not exist

### Notes
- **Extended files** (`RodCutting.Extended.fst`, `MatrixChain.Extended.fst`) contain enhanced Pulse implementations with additional output arrays (cuts `s[]`, split-point table). These go beyond the rubric scope.
- **`DPSpec.fst`** is a shared definitions module factored out of three files to eliminate duplication. It serves the Spec role for RodCutting but does not follow the canonical `AlgoName.Spec.fst` naming.
- All three algorithms merge Spec+Lemmas into a single file rather than separating them per rubric.
- RodCutting and LCS embed complexity proofs (ghost tick counting) inside their Impl files rather than in standalone `Complexity.fst` files.

---

## Detailed Action Items

### \[RENAME\] — Align file names with rubric conventions

| Current Name | Target Name | Rationale |
|-------------|-------------|-----------|
| `CLRS.Ch15.RodCutting.DPSpec.fst` | `CLRS.Ch15.RodCutting.Spec.fst` | Rubric requires `AlgoName.Spec.fst`; move `accum_max`, `build_opt`, `optimal_revenue`, `dp_correct`, etc. here |
| `CLRS.Ch15.RodCutting.Spec.fst` | `CLRS.Ch15.RodCutting.Lemmas.fst` | Contains optimality proofs (`cutting_revenue_le_optimal`, `construct_optimal_cutting`, `optimal_revenue_achievable`, substructure); these are lemma content |
| `CLRS.Ch15.LCS.Spec.fst` | `CLRS.Ch15.LCS.Lemmas.fst` | Contains `lcs_optimal`, `build_lcs`, `lcs_length_is_longest`; these are lemma content |

### \[SPLIT\] — Separate merged concerns

| File | Split Into | Content to Move |
|------|-----------|----------------|
| `CLRS.Ch15.MatrixChain.Spec.fst` | `MatrixChain.Spec.fst` + `MatrixChain.Lemmas.fst` | Keep `mc_cost`, `min_splits`, `split_cost` defs in Spec; move `mc_cost_le_paren_cost`, `mc_cost_achievable`, `discharge_all_costs_bounded`, `dp_correct_upto` to Lemmas |
| `CLRS.Ch15.RodCutting.fst` | `RodCutting.Impl.fst` + `RodCutting.Complexity.fst` | Move ghost tick definitions (`incr_nat`, `tick`), `triangle` def, and complexity postcondition to Complexity; keep `rod_cutting` Pulse fn in Impl |
| `CLRS.Ch15.LCS.fst` | `LCS.Impl.fst` + `LCS.Complexity.fst` + `LCS.Spec.fst` | Move `lcs_length` pure spec to `Spec.fst`; move ghost ticks and `lcs_complexity_bounded` to `Complexity.fst`; keep Pulse `lcs` fn in `Impl.fst` |

### \[CREATE\] — Missing interface files

| File to Create | Content |
|----------------|---------|
| `CLRS.Ch15.RodCutting.Lemmas.fsti` | Signatures: `val cutting_revenue_le_optimal`, `val construct_optimal_cutting`, `val optimal_revenue_achievable`, `val optimal_substructure` |
| `CLRS.Ch15.RodCutting.Complexity.fsti` | Signature: `val triangle (n: nat) : nat`; postcondition spec `val rod_cutting_complexity : n:nat → Lemma (triangle n == n*(n+1)/2)` |
| `CLRS.Ch15.RodCutting.Impl.fsti` | Signature: `val rod_cutting (prices: A.array nat) (n: SZ.t) (ctr: GR.ref nat) : ...` with full Pulse spec |
| `CLRS.Ch15.MatrixChain.Lemmas.fsti` | Signatures: `val mc_cost_le_paren_cost`, `val mc_cost_achievable`, `val discharge_all_costs_bounded`, `val dp_correct_upto` |
| `CLRS.Ch15.MatrixChain.Complexity.fsti` | Signatures: `val mc_iterations (n: nat) : nat`, `val mc_iterations_cubic`, `val mc_iterations_exact` |
| `CLRS.Ch15.MatrixChain.Impl.fsti` | Signature: `val matrix_chain_order (dims: A.array int) (n: SZ.t) : ...` with full Pulse spec |
| `CLRS.Ch15.LCS.Spec.fst` | Pure spec: `val lcs_length (x y: Seq.seq int) (i j: nat) : int` (currently inlined in `LCS.fst`) |
| `CLRS.Ch15.LCS.Lemmas.fsti` | Signatures: `val lcs_optimal`, `val lcs_length_is_longest`, `val build_lcs` |
| `CLRS.Ch15.LCS.Complexity.fsti` | Signature: `val lcs_complexity_bounded` |
| `CLRS.Ch15.LCS.Impl.fsti` | Signature: `val lcs (x: A.array int) (y: A.array int) (m n: SZ.t) (ctr: GR.ref nat) : ...` |

### \[ADD\_INTERFACE\] — Extended files (optional, beyond rubric)

These are not strictly required by the rubric but would improve modularity:

| File | Interface to Add |
|------|-----------------|
| `CLRS.Ch15.RodCutting.Extended.fst` | `RodCutting.Extended.fsti` — `val extended_rod_cutting` signature |
| `CLRS.Ch15.MatrixChain.Extended.fst` | `MatrixChain.Extended.fsti` — `val extended_matrix_chain_order` signature |

---

## Quality Checks

### Admits & Assumes

**0 admits. 0 assumes across all 12 files.** (Verified via `grep -i 'admit\|assume'` in the audit.)

### rlimit Settings

| File | Setting | Assessment |
|------|---------|------------|
| `RodCutting.fst` | `--z3rlimit 50 --fuel 2 --ifuel 2` | ✅ Moderate |
| `RodCutting.Extended.fst` | `--z3rlimit 80 --fuel 2 --ifuel 2` | ✅ Moderate |
| `MatrixChain.fst` | `--z3rlimit 40` | ✅ Low |
| `MatrixChain.Spec.fst` | `--z3rlimit 60`, `--split_queries always` (localized) | ✅ Moderate |
| `MatrixChain.Extended.fst` | `--z3rlimit 80` | ✅ Moderate |
| `LCS.fst` | `--z3rlimit 20` (localized) | ✅ Low |
| `LCS.Spec.fst` | `--z3rlimit 30` (localized) | ✅ Low |
| All others | Defaults | ✅ |

All rlimits ≤ 80. No extreme settings.

### Decreases Clauses

All recursive functions have explicit `decreases` annotations:

| Function | File | Decreases |
|----------|------|-----------|
| `lcs_length` | `LCS.fst` | `i + j` |
| `is_subseq` | `LCS.Spec.fst` | `k + n` |
| `lcs_optimal` | `LCS.Spec.fst` | `i + j` |
| `build_lcs` | `LCS.Spec.fst` | `i + j` |
| `mc_cost` / `min_splits` | `MatrixChain.Spec.fst` | `%[(j - i); 1; 0]` / `%[(j - i); 0; (j - start)]` |
| `mc_inner_sum` | `MatrixChain.Complexity.fst` | `n + 1 - l` |
| `accum_max` | `RodCutting.DPSpec.fst` | `limit` |
| `build_opt` | `RodCutting.DPSpec.fst` | `len` |
| `valid_cutting` | `RodCutting.Spec.fst` | (structural on `cuts` list) |
| `accum_argmax` | `RodCutting.Extended.fst` | `limit` |

### Postconditions

All Pulse implementations have functional-correctness postconditions tying results to pure specs:

| Function | File | Postcondition |
|----------|------|--------------|
| `rod_cutting` | `RodCutting.fst` | `result == optimal_revenue prices n` ∧ `cf - c0 == triangle(n)` |
| `extended_rod_cutting` | `RodCutting.Extended.fst` | `revenue == optimal_revenue prices n` ∧ `cuts_are_optimal` |
| `matrix_chain_order` | `MatrixChain.fst` | `result == mc_result dims n` |
| `extended_matrix_chain_order` | `MatrixChain.Extended.fst` | `cost == mc_result dims n` |
| `lcs` | `LCS.fst` | `result == lcs_length x y m n` ∧ `cf - c0 == (m+1)*(n+1)` |
