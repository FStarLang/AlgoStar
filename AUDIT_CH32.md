# Audit Report — Chapter 32: String Matching

**Scope**: `ch32-string-matching/` — 10 source files  
**Date**: 2025-02-26  
**Auditor**: Copilot  

---

## 0. File Inventory

| File | Lines | Role | Element type | Admits? |
|------|-------|------|-------------|---------|
| `CLRS.Ch32.NaiveStringMatch.fst` | 239 | Pulse impl + spec + complexity | eqtype | **No** |
| `CLRS.Ch32.RabinKarp.fst` | 407 | Pulse impl (sum-hash variant) | Char.char | **No** |
| `CLRS.Ch32.RabinKarp.Spec.fst` | 369 | Pure F* spec (polynomial hash) | nat | **No** |
| `CLRS.Ch32.RabinKarp.Complexity.fst` | 114 | Complexity analysis (pure) | — | **No** |
| `CLRS.Ch32.KMP.fst` | 519 | Pulse impl: prefix fn + matcher | int | **No** |
| `CLRS.Ch32.KMP.Spec.fst` | 602 | Pure completeness proof | int | **No** |
| `CLRS.Ch32.KMP.StrengthenedSpec.fst` | 259 | Spec sketch (conceptual) | int | See §5 |
| `CLRS.Ch32.KMP.Test.fst` | 119 | Pulse test cases | int | **No** |
| `reference.fst` | 431 | Reference impl from FStar examples | eqtype/nat | **No** |
| `test_without_lemma.fst` | 9 | Smoke test for RabinKarp.Spec | nat | **No** |

---

## 1. CLRS Fidelity

### 1.1 NAIVE-STRING-MATCHER (CLRS §32.1, p. 988)

**CLRS pseudocode:**
```
NAIVE-STRING-MATCHER(T, P)
1  n = T.length
2  m = P.length
3  for s = 0 to n − m
4    if P[1..m] == T[s+1..s+m]
5      print "Pattern occurs with shift" s
```

**`NaiveStringMatch.fst`**: Faithful. The outer `while` loop iterates `s` from 0 to `n−m` (line 154). The inner `while` loop (line 176) performs character-by-character comparison, exactly matching the implicit loop in CLRS line 4. Instead of printing, the implementation *counts* matches, which is a natural strengthening.

- ✅ 0-indexed (CLRS is 1-indexed; the shift is consistent)
- ✅ All positions checked: `s ≤ n−m`
- ✅ Generic `eqtype` — works for any alphabet
- ✅ Returns count rather than printing (strictly stronger)

**Verdict: Fully faithful.**

### 1.2 RABIN-KARP-MATCHER (CLRS §32.2, pp. 993–994)

**CLRS pseudocode:**
```
RABIN-KARP-MATCHER(T, P, d, q)
1  n = T.length; m = P.length
3  h = d^(m−1) mod q
4-8  Compute p, t₀ via Horner's rule
9  for s = 0 to n − m
10   if p == tₛ
11     if P[1..m] == T[s+1..s+m]
12       print match
13   if s < n − m
14     t_{s+1} = (d·(tₛ − T[s+1]·h) + T[s+m+1]) mod q
```

There are **two separate Rabin-Karp implementations** with different design choices:

#### `RabinKarp.fst` (Pulse, Char.char, sum-hash)
- **Hash function**: Simple character-value sum (line 83–88). This is **not** the CLRS polynomial hash `h(x) = Σ x[i]·d^(m−1−i) mod q`. The sum hash has **no** base `d` or prime modulus `q`. 
- **Rolling update**: Subtract old char, add new char (line 388). Correct for the sum hash but this is not CLRS eq. 32.2.
- **Verification on match**: Character-by-character comparison (lines 316–355). ✅ Matches CLRS line 11.
- **Correctness**: Proves `count == count_matches_up_to` (full count). ✅
- **Deviation**: The sum hash has more collisions than the polynomial hash; in the worst case every position triggers verification. This doesn't affect correctness but misses the point of Rabin-Karp's hash design.

#### `RabinKarp.Spec.fst` (Pure F*, nat, polynomial hash)
- **Hash function**: `hash x d q i j` via Horner's rule (line 32–36). ✅ Faithful to CLRS.
- **Rolling hash**: `rolling_hash_step` (line 50–52) implements CLRS eq. 32.2. ✅
- **`pow_mod`**: Computes `d^(m−1) mod q`. ✅ Matches CLRS line 3.
- **Correctness**: Proves no-false-positives AND no-false-negatives (lines 285–367). ✅
- **`rolling_hash_step_correct`**: Proves the rolling update equals the direct hash (lines 179–195). ✅

**Issue**: The two RK implementations are independent — the Pulse version uses an inferior hash while the Spec version has the CLRS-faithful hash but no Pulse implementation. They should be unified.

#### `reference.fst` (FStar examples port)
- Directly adapted from `FStar/examples/algorithms/StringMatching.fst`.
- Uses the CLRS polynomial hash with full rolling-hash correctness proofs.
- Both `rabin_karp_matcher_nat` (for nat seqs) and `rabin_karp_matcher` (generic with `as_digit`).
- Returns `option nat` (first match) vs. CLRS "all matches" — partial fidelity.
- Also includes a verified `naive_string_matcher` returning `option nat`.

**Verdict: Partially faithful.** The Spec has the correct CLRS hash; the Pulse impl uses a simplified hash.

### 1.3 COMPUTE-PREFIX-FUNCTION (CLRS §32.4, p. 1006)

**CLRS pseudocode:**
```
COMPUTE-PREFIX-FUNCTION(P)
1  m = P.length
2  let π[1..m] be a new array
3  π[1] = 0
4  k = 0
5  for q = 2 to m
6    while k > 0 and P[k+1] ≠ P[q]
7      k = π[k]
8    if P[k+1] == P[q]
9      k = k + 1
10   π[q] = k
11  return π
```

**`KMP.fst` `compute_prefix_function`** (lines 150–288):
- ✅ Outer loop: `q` from 1 to `m−1` (0-indexed; matches CLRS `q` from 2 to `m`)
- ✅ Inner while: follows failure chain when `k > 0` and mismatch (lines 234–258)
- ✅ Extension check: if `P[k] == P[q]`, increment `k` (lines 268–271)
- ✅ Store `π[q] = k` (line 276)
- ✅ Init: `π[0] = 0`, `k = 0` (implicit from `V.alloc 0sz` and line 185)

The inner while is restructured as a `done_inner` flag loop (lines 211–258) to avoid stateful reads in Pulse's ghost context. This is a standard Pulse pattern and preserves the algorithm's logic.

**Verdict: Fully faithful (0-indexed adaptation).**

### 1.4 KMP-MATCHER (CLRS §32.4, p. 1005)

**CLRS pseudocode:**
```
KMP-MATCHER(T, P)
1  n = T.length; m = P.length
3  π = COMPUTE-PREFIX-FUNCTION(P)
4  q = 0
5  for i = 1 to n
6    while q > 0 and P[q+1] ≠ T[i]
7      q = π[q]
8    if P[q+1] == T[i]
9      q = q + 1
10   if q == m
11     print "Pattern occurs with shift" i − m
12     q = π[q]
```

**`KMP.fst` `kmp_matcher`** (lines 297–455):
- ✅ Outer loop: `i` from 0 to `n−1` (0-indexed; matches CLRS `i` from 1 to `n`)
- ✅ Inner while: failure chain follow when `q > 0` and mismatch (lines 370–413)
- ✅ Extension: `if P[q] == T[i]` then `q++` (lines 422–423)
- ✅ Match detection: `if q == m` then increment count (lines 429–433)
- ✅ Match reset: `q = π[m−1]` (lines 435–437)

**Combined `kmp_string_match`** (lines 462–516):
- Allocates `π`, runs `compute_prefix_function`, then `kmp_matcher`, frees `π`. ✅

**Verdict: Fully faithful (0-indexed adaptation).**

---

## 2. Specification Strength

### 2.1 Naive — ✅ Complete (finds ALL matches)

The postcondition (line 145) states:
```
SZ.v result == count_matches_up_to s_text s_pat (SZ.v n - SZ.v m + 1)
```
where `count_matches_up_to` exhaustively checks all `n−m+1` positions. **This is the strongest possible spec: the returned count equals the exact number of all matches.**

### 2.2 Rabin-Karp Pulse (`RabinKarp.fst`) — ✅ Complete

Postcondition (line 272):
```
result == count_matches_up_to s_text s_pat (SZ.v n - SZ.v m + 1)
```
Same full-count specification as Naive. **Complete.**

### 2.3 Rabin-Karp Spec (`RabinKarp.Spec.fst`) — ✅ Complete

Proves both directions:
- `rabin_karp_find_all_no_false_positives` (line 342): every returned position is a valid match
- `rabin_karp_find_all_no_false_negatives` (line 349): every valid match is returned

Combined theorem `rabin_karp_find_all_correct` (line 358) gives full bidirectional correctness. **Complete.**

### 2.4 KMP Matcher — ⚠️ Weak postcondition (bounds only, no count==spec)

The `kmp_matcher` postcondition (lines 334–337) is:
```
SZ.v count >= 0 /\
SZ.v count <= SZ.v n + 1 /\
matcher_complexity_bound cf (reveal c0) (SZ.v n)
```

**This only proves the count is bounded, NOT that it equals the correct match count.** The matcher proves:
- Memory safety ✅
- Complexity ≤ 2n comparisons ✅
- **Does NOT prove**: `count == count_matches_spec text pattern n m`

### 2.5 KMP Prefix Function — ✅ Correct but not maximal

Postcondition (lines 177–179):
```
pi_correct s_pat s_pi /\ prefix_function_complexity_bound cf (reveal c0) (SZ.v m)
```
where `pi_correct` (line 113) asserts `is_prefix_suffix pattern q (SZ.v (Seq.index pi q))` for all `q`.

**Issue**: `pi_correct` only proves π[q] is **a** valid prefix-suffix, not the **longest** one. The CLRS definition requires π[q] = max{k : k < q ∧ P_k ⊑ P_q}. The maximality property is defined as `pi_max` in `KMP.Spec.fst` (line 39) but never connected to the Pulse implementation.

### 2.6 KMP.Spec.fst — ✅ Strong pure-F* completeness proof

`KMP.Spec.fst` provides a strong pure-F* proof that KMP finds all matches:
- `kmp_step_maximal` (line 269): each KMP step produces the maximum matched prefix
- `kmp_match_iff` (line 412): `q_new = m ⟺ matches_at text pattern (i+1−m)` 
- `kmp_count_step` (line 530): count tracking invariant preserved
- `count_before_eq_spec` (line 595): `count_before == count_matches_spec`

**However, this proof operates on the PURE specification of KMP, not on the Pulse implementation.** The connection between the Pulse code and the pure spec is not formally established. The Pulse `kmp_matcher` does not use `pi_max`, and the `pi_correct` property it proves is weaker.

### 2.7 KMP.StrengthenedSpec.fst — ⚠️ Conceptual sketch

Despite the header claiming "zero admits", this file is a **design document**, not a verification:
- `kmp_count_correct_aux` (line 132): `ensures True` — trivially true
- `kmp_count_correct` (line 141): `ensures True` — trivially true
- `failure_link_preserves_matches` (line 188): ensures only a tautology (line 200: `is_prefix_suffix ... j ==> is_prefix_suffix ... j`)
- Lines 229–258: Large comment block describing what the strengthened postcondition *would* look like, not an actual implementation

**This file has no false statements but proves nothing beyond `True`.**

### 2.8 Summary

| Algorithm | Count = Spec? | All matches? | Proof gap? |
|-----------|:---:|:---:|---|
| Naive | ✅ | ✅ | None |
| RabinKarp Pulse | ✅ | ✅ | Sum-hash ≠ CLRS hash |
| RabinKarp.Spec | ✅ | ✅ | No Pulse impl |
| KMP.fst (Pulse) | ❌ | Unproven | Postcondition is only bounds |
| KMP.Spec (pure) | ✅ | ✅ | Not connected to Pulse impl |

---

## 3. Complexity

### 3.1 Naive — ✅ O((n−m+1)·m) proven

`string_match_complexity_bounded` (line 105–106):
```
cf >= c0 /\ cf - c0 <= (n - m + 1) * m
```
Ghost `tick` called once per character comparison (line 204). The loop invariant (line 166) tracks `vc - c0 ≤ vs * m`. **Tight and correct.**

### 3.2 Rabin-Karp — ✅ Pure analysis

`RabinKarp.Complexity.fst`:
- `rk_best_case` = m + (n−m+1) ∈ O(n+m) — proven linear (line 35)
- `rk_worst_case` = m + (n−m+1)·m ∈ O(nm) — proven quadratic (line 46)
- `rk_best_le_worst` — best ≤ worst (line 82)

**Note**: The Pulse `RabinKarp.fst` has **no ghost tick counter** and therefore no runtime complexity bound in the postcondition. The complexity analysis is only in the separate pure file.

### 3.3 KMP — ✅ O(n + m) proven via amortized analysis

**Prefix function** (`compute_prefix_function`):
- Amortized invariant (line 206): `vc − c0 + k ≤ 2·(q−1)`
- Postcondition (line 179): `prefix_function_complexity_bound cf c0 m` where `cf − c0 ≤ 2·(m−1)`

**Matcher** (`kmp_matcher`):
- Amortized invariant (line 362): `vc − c0 + q ≤ 2·i`
- Postcondition (line 337): `matcher_complexity_bound cf c0 n` where `cf − c0 ≤ 2·n`

**Combined** (`kmp_string_match`):
- `kmp_total_complexity_bound` (line 142): `cf − c0 ≤ 2n + 2m` ∈ O(n+m) ✅

**This is a high-quality amortized analysis using Φ = k (resp. q) as the potential function, matching CLRS §32.4's aggregate analysis.**

---

## 4. Code Quality

### 4.1 Dead / redundant code

| File | Status | Notes |
|------|--------|-------|
| `reference.fst` | **Dead code** | Port of `FStar/examples/algorithms/StringMatching.fst`. Not imported by any other file. Returns `option nat` (first match only). Useful as a reference but contributes no verified guarantees to the library. |
| `test_without_lemma.fst` | **Dead code** | 9-line smoke test calling `rabin_karp_find_all`. Not referenced elsewhere. |
| `RabinKarp.Spec.fst.backup`, `.v2`, `.v3` | **Dead code** | Development artifacts. Should be removed from the repo. |

### 4.2 Code duplication

The following definitions are **copy-pasted across 3+ files** with minor type variations:
- `matches_at` / `matches_at_dec` / `check_match_at` / `check_match_at_correct` — duplicated in NaiveStringMatch, RabinKarp.fst, KMP.fst, KMP.Spec, KMP.StrengthenedSpec
- `count_matches_up_to` / `count_matches_up_to_unfold` / `count_matches_up_to_bounded` — duplicated in NaiveStringMatch, RabinKarp.fst, KMP.StrengthenedSpec

Each copy uses a different element type:
- `NaiveStringMatch`: generic `#a: eqtype`
- `RabinKarp.fst`: `FStar.Char.char`
- `KMP.fst`: `int`
- `RabinKarp.Spec.fst`: `nat`
- `reference.fst`: `eqtype`/`nat`

**Recommendation**: Extract a shared `CLRS.Ch32.StringMatchSpec.fst` parameterized by `#a: eqtype`.

### 4.3 Type inconsistencies

The three algorithms use different element types, making them impossible to compose or compare directly:
- Naive: `eqtype` (generic) — best
- KMP: `int` — restrictive (excludes unsigned types, chars)
- RabinKarp Pulse: `Char.char` — overly specific
- RabinKarp Spec: `nat` — needed for hash arithmetic

### 4.4 Makefile

Line 4 disables `optimize_let_vc` and `fly_deps` — documented as needed for proof stability. Acceptable.

### 4.5 README.md

- Lists only NaiveStringMatch, KMP, and KMP.Test
- **Missing**: RabinKarp (all 3 files), KMP.Spec, KMP.StrengthenedSpec, reference.fst, test_without_lemma.fst
- Build instructions reference only KMP, not the full directory

---

## 5. Proof Quality — Admits and Assumes

### 5.1 Explicit `admit` / `assume`

**None found.** A grep of all `.fst` files in the directory for `admit\b`, `assume\b`, `Admit`, `Assume`, and `sorry` returns zero hits (excluding comments).

### 5.2 Vacuous or trivially-true postconditions

These are effectively "semantic admits" — lemmas that claim to prove something but whose postcondition is `True` or a tautology:

| File | Line | Function | Issue |
|------|------|----------|-------|
| `KMP.StrengthenedSpec.fst` | 132–139 | `kmp_count_correct_aux` | `ensures True` |
| `KMP.StrengthenedSpec.fst` | 141–157 | `kmp_count_correct` | `ensures True` |
| `KMP.Spec.fst` | 560–566 | `kmp_correct_statement` | `ensures True` |
| `KMP.StrengthenedSpec.fst` | 188–224 | `failure_link_preserves_matches` | Ensures a tautology: `is_prefix_suffix p q j ==> is_prefix_suffix p q j` |

### 5.3 Documentation claims vs. reality

| Claim | Location | Accurate? |
|-------|----------|-----------|
| "NO admits. NO assumes." | NaiveStringMatch.fst:10 | ✅ True |
| "NO admits. NO assumes." | RabinKarp.fst:11 | ✅ True |
| "NO admits. NO assumes." | KMP.fst:17 | ✅ True |
| "zero admits" | KMP.StrengthenedSpec.fst:10 | ⚠️ Technically true (no literal admits) but **misleading**: postconditions are `ensures True`, proving nothing. |
| "The two strategic admits above" | KMP.StrengthenedSpec.fst:252 | ❌ **Inaccurate**: the comment references admits that don't exist in the code; the functions have `ensures True` instead. |
| "Proves both functional correctness and O(n+m) comparison complexity" | KMP.fst:9 | ⚠️ **Partially inaccurate**: O(n+m) complexity is proven, but functional correctness (count == spec) is NOT proven in the Pulse implementation. |

### 5.4 Module coherence issue in KMP.Spec

`KMP.Spec.fst` references `check_match_at` (line 71), `count_matches_up_to` with 5 arguments (lines 573–574), and `count_matches_spec` (line 599), none of which are defined in the file itself or in its only opened dependency `CLRS.Ch32.KMP`. These identifiers exist in `CLRS.Ch32.KMP.StrengthenedSpec` but that module is not imported. A `.checked` file exists but may be stale or may reflect F* module resolution behavior. **This should be verified by a clean rebuild.**

---

## 6. Documentation Accuracy

### README.md issues:
1. **Incomplete file listing**: Only mentions 3 of 10+ files
2. **No mention of Rabin-Karp**: The directory contains 3 RK files but the README doesn't acknowledge them
3. **Claims "No admits/assumes"**: True for the files listed but doesn't cover the full directory
4. **Missing KMP.Spec**: The most important correctness proof file is not documented
5. **Build instructions**: `make verify FSTAR_FILES="..."` syntax should be validated

### Header comment issues:
- `KMP.fst` line 9: Claims "functional correctness" which is only partially proven (complexity yes, count==spec no)
- `KMP.StrengthenedSpec.fst` lines 8–10: Claims "zero admits" — technically true but semantically misleading
- `RabinKarp.fst` line 8: "Hash function: Simple sum of characters for verification tractability" — accurate self-description

---

## 7. Task List

### P0 — Critical (proof gap)

| ID | Task | Impact |
|----|------|--------|
| P0.1 | **Strengthen KMP matcher postcondition** to `count == count_matches_spec`. Currently only proves bounds. The pure `KMP.Spec.fst` has all the ingredients (`kmp_count_step`, `count_before_eq_spec`); they need to be wired into the Pulse loop invariant. | KMP's raison d'être as a verified algorithm is incomplete without this. |
| P0.2 | **Prove `pi_max`** (maximality) in the Pulse `compute_prefix_function`, or connect `pi_correct` to `pi_max` via a bridging lemma. Currently the Pulse impl only proves π is **a** valid prefix-suffix, not the **longest**. `KMP.Spec.fst` requires `pi_max` as a precondition. | Blocks formal connection between Pulse impl and pure correctness proof. |
| P0.3 | **Verify `KMP.Spec.fst` references are resolved**: Clean-rebuild to confirm `check_match_at`, `count_matches_up_to` (5-arg), and `count_matches_spec` are actually in scope. If the `.checked` file is stale, fix imports. | May invalidate the completeness proof. |

### P1 — High (CLRS fidelity)

| ID | Task | Impact |
|----|------|--------|
| P1.1 | **Unify Rabin-Karp**: Replace `RabinKarp.fst`'s sum-hash with the CLRS polynomial hash from `RabinKarp.Spec.fst`, or create a new Pulse implementation using the correct hash. | CLRS fidelity; the sum-hash is not the Rabin-Karp algorithm. |
| P1.2 | **Fix `KMP.StrengthenedSpec.fst`**: Either complete the proofs (replace `ensures True` with actual postconditions) or demote the file to a design document with clear naming (e.g., `KMP.SpecSketch.fst`). | Misleading proof claims. |

### P2 — Medium (code quality)

| ID | Task | Impact |
|----|------|--------|
| P2.1 | **Extract shared spec module**: Create `CLRS.Ch32.StringMatchSpec.fst` with generic `matches_at`, `count_matches_up_to`, etc. parameterized by `#a: eqtype`. | Eliminates ~5 copies of identical definitions. |
| P2.2 | **Unify element types**: Make KMP work on `eqtype` (like Naive) instead of `int`. | Consistency and reusability. |
| P2.3 | **Delete backup files**: Remove `RabinKarp.Spec.fst.backup`, `.v2`, `.v3`. | Repo hygiene. |
| P2.4 | **Add complexity to RabinKarp Pulse**: Add ghost tick counter to `RabinKarp.fst` and prove the O((n−m+1)·m) worst-case bound inline. | Parity with Naive and KMP. |

### P3 — Low (documentation / tests)

| ID | Task | Impact |
|----|------|--------|
| P3.1 | **Update README.md**: Document all 10 files, add RabinKarp section, fix build instructions. | Discoverability. |
| P3.2 | **Fix misleading header comments**: Remove "functional correctness" claim from KMP.fst:9 (or prove it); clarify KMP.StrengthenedSpec.fst's status. | Accuracy. |
| P3.3 | **Add KMP matcher tests**: `KMP.Test.fst` only tests `compute_prefix_function`. Add tests for `kmp_matcher` / `kmp_string_match` with known texts and patterns. | Test coverage. |
| P3.4 | **Decide fate of `reference.fst`**: Either integrate its proofs (e.g., bridge to Pulse impls) or move to a `reference/` directory. | Clarity of purpose. |
| P3.5 | **Decide fate of `test_without_lemma.fst`**: Either expand into a real test suite or remove. | 9 lines of dead code. |

---

## 8. Strengths

1. **NaiveStringMatch**: Gold standard — full correctness + tight complexity, zero admits, clean generic code.
2. **KMP amortized complexity proof**: Textbook-quality use of ghost tick counters and potential function argument (Φ = k / q). Matches CLRS §32.4's aggregate analysis precisely.
3. **RabinKarp.Spec**: Excellent pure-F* formalization of the CLRS polynomial hash with full rolling-hash correctness (`rolling_hash_step_correct`) and bidirectional correctness (`rabin_karp_find_all_correct`).
4. **KMP.Spec completeness proof**: The `kmp_step_maximal` → `kmp_match_iff` → `kmp_count_step` chain is a thorough formal proof that KMP finds all matches, with clean separation of concerns.
5. **No literal admits or assumes** in any production file.

---

## 9. Summary

Chapter 32 contains **high-quality verified implementations** of all three CLRS algorithms. The Naive matcher is fully verified. The KMP implementation has excellent complexity proofs but a **critical gap**: the Pulse postcondition does not prove correctness (count == spec), even though the pure-F* `KMP.Spec` file contains all the necessary lemmas. Closing this gap (P0.1 + P0.2) is the single highest-priority task. The Rabin-Karp Pulse implementation uses a simplified hash that deviates from CLRS; unifying it with the faithful `RabinKarp.Spec` hash (P1.1) would complete the chapter's CLRS fidelity.
