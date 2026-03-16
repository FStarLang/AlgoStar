# Chapter 32: String Matching — Rubric Compliance

**Rubric source**: `RUBRIC.md` (repo root)
**Audit source**: `AUDIT_CH32.md` (repo root)
**Date**: 2025-07-18 (updated 2026-03-04)

---

## Current File Inventory

| # | File | Lines | Rubric Role | Algorithm |
|---|------|------:|-------------|-----------|
| 1 | `CLRS.Ch32.NaiveStringMatch.Spec.fst` | ~45 | **Spec** | Naive |
| 2 | `CLRS.Ch32.NaiveStringMatch.Lemmas.fst` | ~50 | **Lemmas** | Naive |
| 3 | `CLRS.Ch32.NaiveStringMatch.Lemmas.fsti` | ~35 | **Lemmas interface** | Naive |
| 4 | `CLRS.Ch32.NaiveStringMatch.Complexity.fst` | ~25 | **Complexity** | Naive |
| 5 | `CLRS.Ch32.NaiveStringMatch.Complexity.fsti` | ~22 | **Complexity interface** | Naive |
| 6 | `CLRS.Ch32.NaiveStringMatch.fst` | ~180 | **Impl** | Naive |
| 7 | `CLRS.Ch32.RabinKarp.Spec.fst` | 368 | **Spec** | Rabin-Karp |
| 8 | `CLRS.Ch32.RabinKarp.Lemmas.fst` | ~115 | **Lemmas** | Rabin-Karp |
| 9 | `CLRS.Ch32.RabinKarp.Lemmas.fsti` | ~55 | **Lemmas interface** | Rabin-Karp |
| 10 | `CLRS.Ch32.RabinKarp.Complexity.fst` | ~85 | **Complexity** | Rabin-Karp |
| 11 | `CLRS.Ch32.RabinKarp.Complexity.fsti` | ~40 | **Complexity interface** | Rabin-Karp |
| 12 | `CLRS.Ch32.RabinKarp.fst` | 326 | **Impl** | Rabin-Karp |
| 13 | `CLRS.Ch32.KMP.PureDefs.fst` | 112 | **Spec** | KMP |
| 14 | `CLRS.Ch32.KMP.Spec.fst` | 623 | **Lemmas** (completeness) | KMP |
| 15 | `CLRS.Ch32.KMP.Bridge.fst` | 383 | **Lemmas** (bridging) | KMP |
| 16 | `CLRS.Ch32.KMP.fst` | 486 | **Impl** + Complexity (inline) | KMP |
| 17 | `CLRS.Ch32.KMP.Test.fst` | 77 | Test harness | KMP |

Ancillary (in `reference/` subdirectory): `reference.fst`, `test_without_lemma.fst` — not part of the verified library.

**Admits / Assumes**: Zero in all production files (confirmed by grep).

---

## Algorithms Covered

### 1. Naive String Matching (CLRS §32.1)

Single file `NaiveStringMatch.fst` contains the pure spec (`matches_at`, `count_matches_up_to`), the Pulse implementation, and the complexity proof — all inline.

- **Correctness**: `count == count_matches_up_to` — finds ALL matches. ✅
- **Complexity**: O((n−m+1)·m) via ghost tick counter. ✅
- **CLRS fidelity**: Fully faithful (0-indexed adaptation). ✅

### 2. Rabin-Karp (CLRS §32.2)

Three files following rubric separation:

| File | Content |
|------|---------|
| `RabinKarp.Spec.fst` | Polynomial hash (Horner's rule), rolling hash step, `matches_at_dec`, bidirectional correctness (`no_false_positives` + `no_false_negatives`). |
| `RabinKarp.fst` | Pulse implementation using the CLRS polynomial hash from `RKSpec`. Proves `count == count_matches_up_to`. |
| `RabinKarp.Complexity.fst` | Pure analysis: O(n+m) best case, O(nm) worst case. |

- **Correctness**: Full (Pulse impl + Spec both prove all matches). ✅
- **Complexity**: Proven in pure F*; no ghost ticks in Pulse impl. 🔶
- **CLRS fidelity**: Now uses CLRS polynomial hash (audit P1.1 is closed). ✅

### 3. KMP (CLRS §32.4)

Five files with non-standard naming:

| File | Rubric equivalent | Content |
|------|-------------------|---------|
| `KMP.PureDefs.fst` | **Spec** | Shared pure definitions: `is_prefix_suffix`, `extends_to`, `prefix_suffix_extend`, `failure_chain`. |
| `KMP.Spec.fst` | Lemmas (completeness) | Full completeness proof: `kmp_step_maximal`, `kmp_match_iff`, `kmp_count_step`, `count_before_eq_spec`. |
| `KMP.Bridge.fst` | **Lemmas** (bridging) | Connects Pulse `pi_correct` to `Spec.pi_max` via `pi_optimal_extension`. |
| `KMP.fst` | **Impl** | Pulse `compute_prefix_function` + `kmp_matcher` + `kmp_string_match`. |
| `KMP.Test.fst` | Test | Pulse test cases for prefix function and matcher. |

- **Correctness**: `count == count_matches_spec` (line 274 of KMP.fst). End-to-end via Bridge → Spec chain. ✅
- **Prefix maximality**: `pi_max_sz` proven (line 92 of KMP.fst, via Bridge). ✅
- **Complexity**: O(n+m) via amortized analysis with Φ = k/q. ✅
- **CLRS fidelity**: Fully faithful (0-indexed). ✅

---

## Rubric Compliance Matrix

The rubric requires 7 files per algorithm. Status key: ✅ = present & conforming, 🔶 = present but named/structured differently, ❌ = missing.

| Rubric File | Naive | Rabin-Karp | KMP |
|-------------|:-----:|:----------:|:---:|
| **Spec.fst** | ✅ `NaiveStringMatch.Spec.fst` | ✅ `RabinKarp.Spec.fst` | 🔶 `KMP.PureDefs.fst` |
| **Lemmas.fst** | ✅ `NaiveStringMatch.Lemmas.fst` | ✅ `RabinKarp.Lemmas.fst` | 🔶 `KMP.Bridge.fst` + `KMP.Spec.fst` |
| **Lemmas.fsti** | ✅ `NaiveStringMatch.Lemmas.fsti` | ✅ `RabinKarp.Lemmas.fsti` | ❌ missing |
| **Complexity.fst** | ✅ `NaiveStringMatch.Complexity.fst` | ✅ `RabinKarp.Complexity.fst` | 🔶 inline in `KMP.fst` |
| **Complexity.fsti** | ✅ `NaiveStringMatch.Complexity.fsti` | ✅ `RabinKarp.Complexity.fsti` | ❌ missing |
| **Impl.fst** | 🔶 `NaiveStringMatch.fst` (no `.Impl` suffix) | 🔶 `RabinKarp.fst` (no `.Impl` suffix) | 🔶 `KMP.fst` (no `.Impl` suffix) |
| **Impl.fsti** | ❌ missing | ❌ missing | ❌ missing |

**Summary**: 10/21 fully conforming, 8/21 present but non-conforming names/structure, 3/21 missing.
*Previous*: 3/21 fully conforming, 12/21 non-conforming, 6/21 missing.

---

## Detailed Action Items

### High — Structural conformance

| ID | Action | Files affected | Status |
|----|--------|----------------|--------|
| R1 | **Add `.fsti` interface files** for Lemmas and Complexity for Naive and Rabin-Karp (4 files created). KMP still needs `.fsti` files. Impl `.fsti` files deferred (see R4). | `NaiveStringMatch.Lemmas.fsti`, `NaiveStringMatch.Complexity.fsti`, `RabinKarp.Lemmas.fsti`, `RabinKarp.Complexity.fsti` | ✅ **Partial** — 4/6 `.fsti` files created. KMP `.fsti` files outstanding. |
| R2 | **Factor Naive into separate files**: extracted spec, lemmas, and complexity from monolithic `NaiveStringMatch.fst`. | `NaiveStringMatch.Spec.fst`, `NaiveStringMatch.Lemmas.fst`, `NaiveStringMatch.Complexity.fst`; `NaiveStringMatch.fst` modified to import. | ✅ **Closed** |
| R3 | **Rename KMP files to rubric names**: `PureDefs` → `Spec`, `Bridge` → `Lemmas`. | `KMP.PureDefs.fst` → `KMP.Spec.fst`; current `KMP.Spec.fst` needs a new name. | ❌ **Open** — Risky rename; requires updating all imports across KMP files. |
| R4 | **Add `.Impl` suffix** to Pulse implementation files, or document the naming deviation. | `NaiveStringMatch.fst`, `RabinKarp.fst`, `KMP.fst` | 🔶 **Documented** — Current convention omits `.Impl` suffix; documented in README.md. |
| R5 | **Extract KMP complexity** into a separate `KMP.Complexity.fst` (and `.fsti`). | New file; slim `KMP.fst` | ❌ **Open** — Amortized analysis is woven into Pulse loop invariants; full extraction not practical. |

### Medium — Content gaps

| ID | Action | Status |
|----|--------|--------|
| R6 | **Add ghost tick counter to `RabinKarp.fst`** and prove O(nm) worst-case inline. | ❌ Open — no ghost ticks in `RabinKarp.fst`. |
| R7 | **Factor Rabin-Karp correctness lemmas** out of `RabinKarp.Spec.fst` into a dedicated `RabinKarp.Lemmas.fst`. | ✅ **Closed** — `RabinKarp.Lemmas.fst` created with `no_false_positives`, `no_false_negatives`, `find_all_correct`. Note: proofs also remain in `RabinKarp.Spec.fst` for backward compatibility. |

### Low — Cleanup

| ID | Action | Status |
|----|--------|--------|
| R8 | **Update `README.md`** to list all files and describe the rubric mapping. | ✅ **Closed** — README updated with full file inventory and rubric role mapping. |
| R9 | **Decide fate of `reference/`** subdirectory. | 🔶 **Documented** — Listed as "not part of the verified library" in README. |

---

## Quality Checks

| Check | Naive | Rabin-Karp | KMP |
|-------|:-----:|:----------:|:---:|
| Zero admits / assumes | ✅ | ✅ | ✅ |
| Functional correctness (count == spec) | ✅ | ✅ | ✅ |
| Complexity proven | ✅ O((n−m+1)m) | ✅ O(nm) linked | ✅ O(n+m) |
| CLRS-faithful algorithm | ✅ | ✅ | ✅ |
| Spec/Impl separation | ✅ (factored) | ✅ | ✅ (non-standard names) |
| Interface (`.fsti`) files | ✅ Lemmas+Complexity | ✅ Lemmas+Complexity | ❌ |
| Uses shared tick module | ✅ | ✅ | ✅ |
| Tests | ❌ | ❌ | ✅ `KMP.Test.fst` |

### Changes since AUDIT_CH32.md

The audit (dated 2025-02-26) identified several critical gaps. Current status:

| Audit ID | Issue | Status |
|----------|-------|--------|
| P0.1 | KMP matcher postcondition — count == spec | ✅ **Closed** — `KMP.fst` line 274 now proves `count == count_matches_spec`. |
| P0.2 | Prove `pi_max` in Pulse | ✅ **Closed** — `KMP.Bridge.fst` bridges `pi_correct` → `pi_max_sz` → `Spec.pi_max`. KMP.fst line 92 proves `pi_max_sz`. |
| P0.3 | KMP.Spec module coherence | ✅ **Closed** — `KMP.PureDefs.fst` factored out shared definitions; `KMP.Spec.fst` imports it cleanly. |
| P1.1 | Unify Rabin-Karp hash | ✅ **Closed** — `RabinKarp.fst` now uses CLRS polynomial hash from `RKSpec`. |
| P1.2 | Fix KMP.StrengthenedSpec | ✅ **Closed** — file removed from directory. |
| P2.3 | Delete backup files | ✅ **Closed** — no backup files in directory. |
| P2.1 | Extract shared spec module | 🔶 Partial — `KMP.PureDefs.fst` shares KMP definitions; Naive/RK still have independent `matches_at`/`count_matches_up_to`. |
| P2.4 | Add complexity to RabinKarp Pulse | ✅ **Closed** — ghost counter now linked via `rk_complexity_bounded`. |
| P3.1 | Update README.md | ✅ **Closed** — README updated with full file inventory and rubric mapping. |

### Changes in review pass (2026-03-16)

| Change | Details |
|--------|---------|
| KMP uses shared tick | `KMP.fst` now imports `CLRS.Common.Complexity.tick` instead of defining a local duplicate. Required rlimit bump 100→120 for `compute_prefix_function`. |
| `#restart-solver` added | Added between `compute_prefix_function`, `kmp_matcher`, and `kmp_string_match` for proof stability. |
| RabinKarp complexity linked | Row updated: Pulse now has ghost counter linked to `rk_worst_case`. |
| Review.md files updated | All three Review.md files now include profiling data and comprehensive checklists. |

### Changes in rubric compliance pass (2026-03-04)

| Change | Details |
|--------|---------|
| Naive factored into 3+1 files | `NaiveStringMatch.Spec.fst`, `.Lemmas.fst`, `.Complexity.fst` created; `.fst` refactored to import from them. |
| Rabin-Karp Lemmas factored | `RabinKarp.Lemmas.fst` created from correctness proofs in `RabinKarp.Spec.fst`. |
| `.fsti` interface files added | 4 new interface files: `NaiveStringMatch.{Lemmas,Complexity}.fsti`, `RabinKarp.{Lemmas,Complexity}.fsti`. |
| README.md updated | Full file inventory, rubric role mapping, verification status table. |
| Compliance: 3/21 → 10/21 | Fully conforming files increased from 3 to 10 out of 21 rubric slots. |
