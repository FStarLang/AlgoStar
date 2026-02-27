# Audit Report — Chapter 15: Dynamic Programming

**Scope**: Rod Cutting, Matrix Chain Multiplication, Longest Common Subsequence  
**Directory**: `ch15-dynamic-programming/` (10 files)  
**Date**: 2025-07-17  
**Auditor**: Copilot  

---

## Executive Summary

Chapter 15 is the strongest chapter in the library. All 10 files are **admit-free and assume-free**. Each algorithm has a Pulse implementation with a full correctness proof tied to a pure specification, and complexity is formally verified for rod cutting (O(n²)) and LCS (O(mn)). Matrix chain has a separate `Complexity.fst` proving the O(n³) bound on a pure model. The specification files go further: Rod Cutting proves optimal substructure (CLRS Eq. 15.2), and LCS proves full optimality (upper bound + witness construction). The only significant gap is that the matrix chain spec depends on a sentinel bound precondition (`all_costs_bounded dims n n 1000000000`), which is a practical but not universal assumption.

**Admits/Assumes**: **0** across all 10 files.

---

## 1. CLRS Fidelity

### 1.1 Rod Cutting — BOTTOM-UP-CUT-ROD / EXTENDED-BOTTOM-UP-CUT-ROD

| CLRS Element | Implementation | Fidelity |
|---|---|---|
| `r[0..n]` array, `r[0]=0` | `V.alloc (0 <: nat) n_plus_1` | ✅ Exact |
| Outer loop `j = 1 to n` | `while (!j <=^ n)` starting at 1sz | ✅ Exact |
| Inner loop `i = 1 to j` | `while (!i <=^ vj)` starting at 1sz | ✅ Exact |
| `q = max(q, p[i] + r[j-i])` | `candidate = price_i + r_j_minus_i; new_q = if candidate > vq then candidate else vq` | ✅ Exact |
| `r[j] = q` | `V.op_Array_Assignment r vj final_q` | ✅ Exact |
| Return `r[n]` | `V.op_Array_Access r n` | ✅ Exact |
| CLRS uses `q = -∞` init | Code uses `q = 0` (valid since prices are `nat`) | ✅ Equivalent |
| 1-indexed prices `p[1..n]` | 0-indexed `prices[0..n-1]` (i.e., `prices[i-1]`) | ✅ Adapted correctly |

**Extended version** (`RodCutting.Extended.fst`):
| CLRS Element | Implementation | Fidelity |
|---|---|---|
| Additional `s[0..n]` array | `s_cuts = V.alloc 0sz n_plus_1` | ✅ Exact |
| `s[j] = i` when `q < p[i]+r[j-i]` | `best_i` tracks argmax, stored via `V.op_Array_Assignment s_cuts vj final_best_i` | ✅ Exact |
| Returns `(r, s)` | Returns `(result, s_cuts)` | ✅ Exact |

**Verdict**: Faithful implementation of CLRS BOTTOM-UP-CUT-ROD and EXTENDED-BOTTOM-UP-CUT-ROD with 0-based indexing adaptation.

### 1.2 Matrix Chain Multiplication — MATRIX-CHAIN-ORDER

| CLRS Element | Implementation | Fidelity |
|---|---|---|
| Input `p[0..n]` with n+1 entries | `dims: A.array int` with `SZ.v n + 1 == A.length dims` | ✅ Exact |
| Table `m[1..n, 1..n]` | Flat `V.alloc 0 table_size` with 0-based indexing | ✅ Adapted (0-based) |
| `m[i,i] = 0` for all i | Implicit: `V.alloc 0` initializes all to 0 | ✅ Exact |
| Outer loop `l = 2 to n` | `while (!l <=^ n)` starting at 2sz | ✅ Exact |
| Middle loop `i = 1 to n-l+1` | `while (!i <^ n - vl + 1sz)` starting at 0sz | ⚠️ 0-based |
| `j = i + l - 1` | `j = vi + vl - 1sz` | ✅ Exact |
| `m[i,j] = ∞` | `min_cost := 1000000000` (sentinel) | ⚠️ Finite sentinel |
| Inner loop `k = i to j-1` | `while (!k <^ j)` starting at vi | ✅ Exact |
| `q = m[i,k] + m[k+1,j] + p_{i-1}*p_k*p_j` | `q = cost_ik + cost_k1j + dim_i * dim_k1 * dim_j1` | ✅ Exact (0-based dims) |
| Return `m[1, n]` | `V.op_Array_Access m result_idx` where `result_idx = 0*n + (n-1)` | ✅ Exact (0-based) |
| CLRS also returns `s` table | **Not implemented** — only computes cost | ⚠️ Partial |

**CLRS indexing note**: CLRS uses 1-based indices (`m[1..n]`), implementation uses 0-based (`m[0..n-1]`). The mapping is consistent throughout.

**Sentinel issue**: CLRS uses `m[i,j] = ∞`; the implementation uses `1000000000`. This is handled correctly by the `all_costs_bounded` precondition in the spec, but limits the algorithm to inputs where optimal costs fit within 10⁹.

**Verdict**: Faithful to CLRS MATRIX-CHAIN-ORDER with 0-based adaptation and finite sentinel. Missing `s` table (parenthesization reconstruction).

### 1.3 LCS — LCS-LENGTH

| CLRS Element | Implementation | Fidelity |
|---|---|---|
| Input sequences `X[1..m]`, `Y[1..n]` | `x: A.array int`, `y: A.array int` with lengths m, n | ✅ Exact |
| Table `c[0..m, 0..n]` | Flat `V.alloc 0 table_size` where `table_size = (m+1)*(n+1)` | ✅ Exact |
| `c[i,0] = c[0,j] = 0` | Implicit from `V.alloc 0`; `value_to_store = 0` when `vi=0 ∨ vj=0` | ✅ Exact |
| Outer loop `i = 1 to m` | `while (!i <=^ m)` starting at 0sz | ✅ Processes row 0 explicitly |
| Inner loop `j = 1 to n` | `while (!j <=^ n)` starting at 0sz | ✅ Processes col 0 explicitly |
| Match: `c[i,j] = c[i-1,j-1]+1` | `if xi = yj then val_diag + 1` | ✅ Exact |
| Mismatch: `c[i,j] = max(c[i-1,j], c[i,j-1])` | `else if val_up >= val_left then val_up else val_left` | ✅ Exact |
| Return `c[m, n]` | `V.op_Array_Access table result_idx` | ✅ Exact |
| CLRS also returns `b` table | **Not implemented** — only computes length | ⚠️ Partial |

**Note**: The implementation starts both loops at 0 (not 1 as in CLRS) and handles the boundary cases with the conditional `if vi = 0sz || vj = 0sz then 0`. This correctly computes the same table.

**Verdict**: Faithful to CLRS LCS-LENGTH. Missing `b` table (backtracking arrows), but `LCS.Spec.fst` provides a pure `build_lcs` that reconstructs the witness.

---

## 2. Specification Strength

### 2.1 Rod Cutting

| Property | Status | Location |
|---|---|---|
| `optimal_revenue` defined as DP recurrence | ✅ Proven | `RodCutting.Spec.fst:76` |
| DP table prefix consistency | ✅ Proven | `RodCutting.Spec.fst:84` |
| `accum_max` extensionality | ✅ Proven | `RodCutting.Spec.fst:106` |
| `dp_correct` ⟹ `optimal_revenue` | ✅ Proven | `RodCutting.Spec.fst:128` |
| Optimal substructure (CLRS Eq. 15.2) | ✅ Proven | `RodCutting.Spec.fst:246` |
| `dp_table_correct` (all entries) | ✅ Proven | `RodCutting.Spec.fst:169` |
| `valid_cutting` / `cutting_revenue` | ✅ Defined | `RodCutting.Spec.fst:23-36` |
| Optimality over all valid cuttings | ⚠️ **Not proven** | See note below |

**Gap**: The specification defines `optimal_revenue` via the DP recurrence (`build_opt`/`accum_max`) and proves `optimal_substructure` connecting it to `max_over_range`. It also defines `valid_cutting` and `cutting_revenue`. However, there is **no lemma** proving that `optimal_revenue prices n` equals `max { cutting_revenue prices cuts | valid_cutting n cuts }`. The DP recurrence is proven self-consistent and matches the CLRS recurrence (Eq. 15.2), but the link from that recurrence to "maximum over all valid cuttings" is implicit via the CLRS argument, not machine-checked.

**Extended Rod Cutting** (`RodCutting.Extended.fst`):
| Property | Status | Location |
|---|---|---|
| Revenue = `optimal_revenue` | ✅ Proven | `Extended.fst:394` |
| `cuts_are_valid`: `1 ≤ s[j] ≤ j` | ✅ Proven | `Extended.fst:302` |
| `cuts_are_optimal`: decomposition achieves optimum | ✅ Proven | `Extended.fst:311` |
| `reconstruct_cutting_sums`: pieces sum to j | ✅ Proven | `Extended.fst:342` |

### 2.2 Matrix Chain Multiplication

| Property | Status | Location |
|---|---|---|
| `mc_cost` recursive spec (CLRS Eq. 15.7) | ✅ Defined | `MatrixChain.Spec.fst:51` |
| `mc_result == mc_cost dims 0 (n-1)` | ✅ Proven | `MatrixChain.Spec.fst:516` |
| `dp_correct_upto` induction | ✅ Proven | `MatrixChain.Spec.fst:446-501` |
| Sentinel bridge (`mc_inner_k ↔ min_splits`) | ✅ Proven | `MatrixChain.Spec.fst:188-262` |
| `all_costs_bounded` precondition | ⚠️ **Assumed** | `MatrixChain.Spec.fst:519` |

**Gap**: The main theorem `mc_spec_equiv` requires `all_costs_bounded dims n n 1000000000` — that all optimal costs fit within 10⁹. This is a practical limitation (realistic for any problem fitting in machine integers) but not a universal proof. The Pulse implementation `matrix_chain_order` postcondition is `result == mc_result s_dims (SZ.v n)`, which is the imperative mirror spec — correctness relative to the recursive `mc_cost` requires going through `mc_spec_equiv` with its sentinel bound.

**Missing**: No optimality proof showing `mc_cost` equals the minimum over all parenthesizations. The `mc_cost` definition is the standard recurrence, so this is implicitly correct by the CLRS argument, but not machine-checked.

### 2.3 LCS

| Property | Status | Location |
|---|---|---|
| `lcs_length` defined (CLRS Eq. 15.9) | ✅ Defined | `LCS.fst:49` |
| `lcs_length` non-negativity | ✅ Proven | `LCS.fst:68` |
| `is_subsequence` / `is_common_subsequence` | ✅ Defined | `LCS.Spec.fst:22-38` |
| **Optimality**: `lcs_length ≥ |sub|` for all common subsequences | ✅ Proven | `LCS.Spec.fst:44-76` |
| **Witness**: `∃ sub. |sub| == lcs_length ∧ is_common_subsequence sub x y` | ✅ Proven | `LCS.Spec.fst:302-312` |
| **Combined**: `lcs_length_is_longest` (upper bound + achievability) | ✅ Proven | `LCS.Spec.fst:315-329` |
| `build_lcs` constructs witness | ✅ Proven | `LCS.Spec.fst:143-290` |
| `is_subseq` prefix/weakening monotonicity | ✅ Proven | `LCS.Spec.fst:83-138` |

**LCS has the strongest specification in the entire chapter.** The `lcs_length_is_longest` theorem is a complete characterization: no common subsequence is longer AND a common subsequence of that exact length exists. This is the gold standard for DP optimality proofs.

---

## 3. Complexity Analysis

### 3.1 Rod Cutting — O(n²)

| Aspect | Status | Location |
|---|---|---|
| Ghost tick counter (`GR.ref nat`) | ✅ | `RodCutting.fst:38-44` |
| `triangle(n) = n(n+1)/2` | ✅ Defined | `RodCutting.fst:153` |
| `triangle(n) + (n+1) == triangle(n+1)` | ✅ Proven | `RodCutting.fst:155` |
| Loop invariant: `vc - c0 == triangle(vj - 1)` | ✅ | `RodCutting.fst:211` |
| Inner loop: `vc_inner - c0 == triangle(vj-1) + (vi-1)` | ✅ | `RodCutting.fst:236` |
| Postcondition: `cf - c0 == triangle(n)` | ✅ | `RodCutting.fst:191` |

**Exactness**: The proof establishes the **exact** iteration count `n(n+1)/2`, which is tighter than the O(n²) claim. Each inner-loop iteration is ghost-ticked once.

### 3.2 Matrix Chain — O(n³)

| Aspect | Status | Location |
|---|---|---|
| `mc_iterations(n)` pure model | ✅ Defined | `MatrixChain.Complexity.fst:22-28` |
| Term bound: `(n-l+1)(l-1) ≤ n²` | ✅ Proven | `Complexity.fst:38-43` |
| Sum bound: `mc_inner_sum n l ≤ (n-l+1)·n²` | ✅ Proven | `Complexity.fst:48-57` |
| **Main**: `mc_iterations n ≤ n³` | ✅ Proven | `Complexity.fst:62-80` |
| `mc_iterations n > 0` for `n ≥ 2` | ✅ Proven | `Complexity.fst:93-101` |

**Note**: The complexity is proven on a pure iteration-count model, **not** via ghost ticks in the Pulse code. The Pulse implementation does not carry a tick counter. This is a weaker form: the O(n³) bound is about the pure loop structure, not about the actual imperative execution. The comment at line 106 notes the exact sum is `(n³-n)/6` but this is not formally proven.

### 3.3 LCS — O(mn)

| Aspect | Status | Location |
|---|---|---|
| Ghost tick counter (`GR.ref nat`) | ✅ | `LCS.fst:36-41` |
| `lcs_complexity_bounded cf c0 m n` ≡ `cf - c0 == (m+1)*(n+1)` | ✅ Defined | `LCS.fst:170` |
| Outer invariant: `vc - c0 == vi * (n+1)` | ✅ | `LCS.fst:228` |
| Inner invariant: `vc_inner - c0 == vi * (n+1) + vj` | ✅ | `LCS.fst:249` |
| Postcondition: `cf - c0 == (m+1)*(n+1)` | ✅ | `LCS.fst:204` |

**Exactness**: The proof establishes **exactly** `(m+1)·(n+1)` cell evaluations. This counts boundary cells (row 0, col 0) as well, which is slightly more than the CLRS `m·n` count for the non-trivial cells, but is the true iteration count of the implementation.

---

## 4. Code Quality

### 4.1 Architecture

| Aspect | Assessment |
|---|---|
| Separation of concerns | ✅ **Excellent**: Spec/Impl/Test/Complexity cleanly separated |
| Module structure | ✅ Clear naming: `CLRS.Ch15.{Algorithm}.{Aspect}` |
| Code duplication | ⚠️ `accum_max`, `build_opt`, etc. duplicated between `RodCutting.fst`, `RodCutting.Spec.fst`, and `RodCutting.Extended.fst`. These are defined identically in 3 files. |
| Makefile | ✅ Simple, uses shared test.mk with targeted OTHERFLAGS override |

### 4.2 Implementation Patterns

- **Ghost ticks**: Used in RodCutting and LCS; clean pattern with `GR.ref nat`, fully erased at runtime.
- **Flat 2D arrays**: MatrixChain and LCS use `i*n+j` flat indexing — appropriate for Pulse.
- **Vector allocation/free**: Consistent use of `V.alloc`/`V.free` with proper ownership tracking.
- **Loop invariants**: Well-structured, carry exactly the needed state.
- **`opaque_to_smt`**: Good use in `Extended.fst` (lines 301, 311) to prevent Z3 context pollution.

### 4.3 Issues

1. **Code duplication** (Medium): `accum_max`, `build_opt`, `optimal_revenue`, `build_opt_prefix`, `optimal_revenue_consistent`, `accum_max_ext`, `dp_correct`, `accum_max_dp_correct` are copy-pasted identically across `RodCutting.fst`, `RodCutting.Spec.fst`, and `RodCutting.Extended.fst`. Should be factored into a shared module.

2. **Sentinel constant** (Low): `1000000000` as a magic number in `MatrixChain.fst:191` and throughout `MatrixChain.Spec.fst`. Could be a named constant.

3. **Safe index workaround** (Low): `Extended.fst:123-124` defines `seq_index_or_zero` but it's not used in the final code — dead code.

4. **LCS returns `int` not `nat`** (Low): `lcs_length` returns `int` despite being proven non-negative. The Pulse function signature matches. Using `nat` would be more precise but requires `lcs_length_nonneg` at every use site.

5. **Test files don't assert expected values** (Low): `RodCutting.Test.fst` computes the revenue but doesn't assert it equals 30 (the CLRS expected answer). Similarly `MatrixChain.Test.fst` doesn't assert 15125.

---

## 5. Proof Quality

### 5.1 Admits and Assumes

**ZERO admits. ZERO assumes.** Verified across all 10 files via `grep -i 'admit\|assume'`.

### 5.2 SMT Settings

| File | Settings | Assessment |
|---|---|---|
| `RodCutting.fst` | `--z3rlimit 50 --fuel 2 --ifuel 2` | ✅ Moderate |
| `RodCutting.Spec.fst` | (none beyond default) | ✅ |
| `RodCutting.Extended.fst` | `--z3rlimit 80 --fuel 2 --ifuel 2` | ✅ Moderate |
| `MatrixChain.fst` | `--z3rlimit 40` | ✅ Low |
| `MatrixChain.Spec.fst` | `--z3rlimit 60`, `--split_queries always` (localized) | ✅ Moderate |
| `MatrixChain.Complexity.fst` | (none) | ✅ |
| `LCS.fst` | `--z3rlimit 20` (localized) | ✅ Low |
| `LCS.Spec.fst` | `--z3rlimit 30` (localized) | ✅ Low |

All rlimits are reasonable (≤80). No extreme settings. `--split_queries always` is used only in `MatrixChain.Spec.fst` for one lemma (`lemma_mc_inner_i_fills_correctly`), which is appropriate for a complex inductive proof.

### 5.3 Proof Techniques

| Technique | Used In | Assessment |
|---|---|---|
| Ghost tick counting | RodCutting, LCS | ✅ Elegant, zero runtime overhead |
| Imperative mirror spec | MatrixChain | ✅ Standard; Pulse postcondition matches pure recursive unfolding |
| `opaque_to_smt` predicates | Extended.fst | ✅ Good practice for complex postconditions |
| Bridge lemmas (`_intro`) | Extended.fst:357 | ✅ Clean separation of proof obligations |
| `Classical.forall_intro` | Spec files | ✅ Standard |
| Extensionality arguments | `accum_max_ext`, `is_subseq_ext` | ✅ Well-structured |
| Mutual recursion (`and`) | `mc_cost`/`min_splits` | ✅ Necessary, well-handled with `%[...]` decreases |

### 5.4 Proof Gaps (non-admit)

1. **Rod Cutting**: No proof that `optimal_revenue` equals max over all `valid_cutting` decompositions. The DP recurrence is proven equivalent to `max_over_range` of first-cut revenues (optimal substructure), but the link to the enumerative definition is missing.

2. **Matrix Chain**: No proof that `mc_cost` equals minimum over all parenthesizations. The recurrence is standard but not connected to an enumerative definition.

3. **Matrix Chain**: The `all_costs_bounded` precondition is not discharged — it's a caller obligation. In practice, any input with dimensions fitting in machine integers will satisfy it, but it's an open proof obligation.

---

## 6. Documentation Accuracy

| Claim | Location | Accurate? |
|---|---|---|
| "NO admits. NO assumes." | `RodCutting.fst:16`, `LCS.fst:13`, `MatrixChain.fst:12` | ✅ **True** |
| "ADMITS: 0" | `Extended.fst:15` | ✅ **True** |
| "result == optimal_revenue prices n" | `RodCutting.fst:11` | ✅ **True** |
| "exactly n*(n+1)/2 inner-loop iterations" | `RodCutting.fst:12` | ✅ **True** |
| "result == mc_outer ..." | `MatrixChain.fst:9` | ✅ **True** |
| "exactly (m+1)*(n+1) cell evaluations" | `LCS.fst:10` | ✅ **True** |
| "Correctness: result == lcs_length x y m n" | `LCS.fst:9` | ✅ **True** |
| PROOF_SUMMARY.md: "logically complete" | Line 46 | ⚠️ Slightly misleading — sentinel bound is a real assumption |
| "Optimal cost should be 15,125" | `MatrixChain.Test.fst:9` | ✅ Matches CLRS |

**PROOF_SUMMARY.md** is well-written and accurately describes the proof approach, though it could note that `all_costs_bounded` is an externally-imposed assumption.

---

## 7. Task List

### Priority 1 (High) — Specification Gaps

| # | Task | File | Effort |
|---|---|---|---|
| 1 | **Factor out shared Rod Cutting spec** into a single module. `accum_max`, `build_opt`, `optimal_revenue`, `build_opt_prefix`, `optimal_revenue_consistent`, `accum_max_ext`, `dp_correct`, `accum_max_dp_correct` are copy-pasted in 3 files. | `RodCutting.fst`, `Spec.fst`, `Extended.fst` | Medium |
| 2 | **Prove `optimal_revenue` = max over `valid_cutting`**: Bridge the DP recurrence to the enumerative definition. This would close the main specification gap. | `RodCutting.Spec.fst` | Hard |
| 3 | **Prove `mc_cost` = min over all parenthesizations**: Define an explicit parenthesization type and prove equivalence. | `MatrixChain.Spec.fst` | Hard |
| 4 | **Eliminate sentinel assumption**: Either prove `all_costs_bounded` from dimension bounds, or restructure to use `option int` / unbounded comparison. | `MatrixChain.Spec.fst` | Medium |
| 5 | **Add `s` table to Matrix Chain** (parenthesization reconstruction, like CLRS). | `MatrixChain.fst` | Medium |
| 6 | **Add ghost ticks to Matrix Chain Pulse code**: Currently complexity is proven only on the pure model, not in the implementation. | `MatrixChain.fst` | Low |
| 7 | **Add `b` table to LCS** (backtracking arrows, like CLRS) or document that `build_lcs` in Spec serves this role. | `LCS.fst` | Low |
| 8 | **Remove dead code** `seq_index_or_zero` | `Extended.fst:123` | Trivial |
| 9 | **Name the sentinel constant** `1000000000` → `sentinel`, better use an option type | `MatrixChain.fst`, `Spec.fst` | Trivial |
| 12 | **Exact MC complexity**: Prove `mc_iterations n == (n³-n)/6` (mentioned but unproven in `Complexity.fst:106`) | `Complexity.fst` | Low |

### Defer

| 10 | **Add assertions to test files** (e.g., `assert (revenue == 30)` for rod cutting) | `Test.fst` files | Low |
| 11 | **Consider `nat` return for LCS** instead of `int` | `LCS.fst` | Low |

---

## Appendix: File-by-File Summary

| File | Lines | Admits | Complexity | Key Properties |
|---|---|---|---|---|
| `CLRS.Ch15.RodCutting.fst` | 273 | 0 | O(n²) ghost-ticked | `result == optimal_revenue`, `cf-c0 == triangle(n)` |
| `CLRS.Ch15.RodCutting.Spec.fst` | 271 | 0 | — | Optimal substructure (Eq. 15.2), DP correctness |
| `CLRS.Ch15.RodCutting.Extended.fst` | 560 | 0 | — | Revenue + cuts array, `cuts_are_optimal` |
| `CLRS.Ch15.RodCutting.Test.fst` | 56 | 0 | — | CLRS example (p=[1,5,8,9,10,17,17,20,24,30]) |
| `CLRS.Ch15.MatrixChain.fst` | 285 | 0 | — | `result == mc_result`, imperative mirror |
| `CLRS.Ch15.MatrixChain.Spec.fst` | 537 | 0 | — | `mc_result == mc_cost` (with sentinel bound) |
| `CLRS.Ch15.MatrixChain.Complexity.fst` | 107 | 0 | O(n³) | `mc_iterations n ≤ n³` |
| `CLRS.Ch15.MatrixChain.Test.fst` | 56 | 0 | — | CLRS example (dims=[30,35,15,5,10,20,25]) |
| `CLRS.Ch15.LCS.fst` | 301 | 0 | O(mn) ghost-ticked | `result == lcs_length`, `cf-c0 == (m+1)*(n+1)` |
| `CLRS.Ch15.LCS.Spec.fst` | 330 | 0 | — | **Full optimality**: upper bound + witness |
