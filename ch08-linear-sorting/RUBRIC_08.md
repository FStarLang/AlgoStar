# Chapter 08: Linear-Time Sorting — Rubric Compliance

**Generated:** 2025-07-18
**Source files:** 14 `.fst` files, 5 421 lines total
**Canonical rubric:** `RUBRIC.md` (root)
**Audit reference:** `AUDIT_CH08.md` (root)

---

## Current File Inventory

| # | Rubric Slot | File | Lines | Lang | Status |
|---|-------------|------|------:|------|--------|
| 1 | **CountingSort.Spec** | `CLRS.Ch08.CountingSort.Lemmas.fst` | 309 | F* | ✅ Pure spec + definitions (`sorted`, `permutation`, `in_range`, invariants) |
| 2 | **CountingSort.Lemmas** | *(merged into Lemmas.fst above)* | — | — | 🔶 Spec and lemmas are in the same file, not separated |
| 3 | **CountingSort.Lemmas.fsti** | *(does not exist)* | — | — | ❌ Missing |
| 4 | **CountingSort.Impl** | `CLRS.Ch08.CountingSort.fst` | 178 | Pulse | 🔶 In-place variant (not CLRS); see Stable for faithful version |
| 5 | **CountingSort.Impl (CLRS)** | `CLRS.Ch08.CountingSort.Stable.fst` | 277 | Pulse | ✅ CLRS-faithful 4-phase impl (A→B, backward pass) |
| 6 | **CountingSort.Impl.fsti** | *(does not exist)* | — | — | ❌ Missing |
| 7 | **CountingSort.Lemmas (Stable)** | `CLRS.Ch08.CountingSort.StableLemmas.fst` | 583 | F* | ✅ Phase-specific lemmas for stable variant |
| 8 | **CountingSort.Complexity** | `CLRS.Ch08.CountingSort.Complexity.fst` | 32 | F* | ✅ Θ(n+k) upper + lower bounds |
| 9 | **CountingSort.Complexity.fsti** | *(does not exist)* | — | — | ❌ Missing |
| 10 | **RadixSort.Spec** | `CLRS.Ch08.RadixSort.Spec.fst` | 722 | F* | ✅ Abstract multi-digit correctness via stable-sort steps |
| 11 | **RadixSort.Spec (concrete)** | `CLRS.Ch08.RadixSort.MultiDigit.fst` | 1 119 | F* | 🔶 Requires `distinct` — not full CLRS generality |
| 12 | **RadixSort.Base** | `CLRS.Ch08.RadixSort.Base.fst` | 139 | F* | ✅ Shared definitions (pow, digit, count, permutation) |
| 13 | **RadixSort.Lemmas (Stability)** | `CLRS.Ch08.RadixSort.Stability.fst` | 502 | F* | ✅ Core CLRS Lemma 8.3 stability proof |
| 14 | **RadixSort.Lemmas (FullSort)** | `CLRS.Ch08.RadixSort.FullSort.fst` | 450 | F* | ✅ digit decomposition → lex → numeric bridge |
| 15 | **RadixSort.Lemmas.fsti** | *(does not exist)* | — | — | ❌ Missing |
| 16 | **RadixSort.Bridge** | `CLRS.Ch08.RadixSort.Bridge.fst` | 167 | F* | ✅ CountingSort ↔ RadixSort.Base equivalences (d=0) |
| 17 | **RadixSort.Complexity** | `CLRS.Ch08.RadixSort.Complexity.fst` | 146 | F* | ✅ Θ(d(n+k)) bounds |
| 18 | **RadixSort.Complexity.fsti** | *(does not exist)* | — | — | ❌ Missing |
| 19 | **RadixSort.Impl** | `CLRS.Ch08.RadixSort.fst` | 75 | Pulse | 🔶 d=1 only, delegates to non-stable CountingSort |
| 20 | **RadixSort.Impl.fsti** | *(does not exist)* | — | — | ❌ Missing |
| 21 | **BucketSort.Spec+Impl** | `CLRS.Ch08.BucketSort.fst` | 722 | F* | 🔶 Pure only (no Pulse impl); generalized (int, not [0,1) reals) |
| 22 | **BucketSort.Lemmas.fsti** | *(does not exist)* | — | — | ❌ Missing |
| 23 | **BucketSort.Complexity** | *(inline in BucketSort.fst, lines 608–695)* | — | F* | 🔶 Inline, not a separate module |

---

## Algorithms Covered

| Algorithm | CLRS Section | CLRS Pseudocode | Status |
|-----------|:------------:|-----------------|--------|
| **COUNTING-SORT** | §8.2 | 4-phase: init C, count, prefix-sum, backward placement | ✅ `Stable.fst` is faithful; `CountingSort.fst` is a simplified in-place variant |
| **RADIX-SORT** | §8.3 | `for i = 1 to d: stable sort on digit i` | 🔶 Pure spec complete (Spec, Stability, FullSort, MultiDigit); Pulse impl is d=1 only |
| **BUCKET-SORT** | §8.4 | distribute into n buckets → insertion-sort each → concatenate | 🔶 Pure impl only; generalized to int range with k buckets (not [0,1) uniform reals) |

---

## Rubric Compliance Matrix

The canonical rubric requires seven file slots per algorithm. Status for each:

### CountingSort

| Rubric Slot | Required File | Exists? | Notes |
|-------------|--------------|:-------:|-------|
| `Spec.fst` | `CLRS.Ch08.CountingSort.Spec.fst` | ❌ | Spec definitions live in `Lemmas.fst`; no separate `Spec.fst` |
| `Lemmas.fst` | `CLRS.Ch08.CountingSort.Lemmas.fst` | ✅ | Also contains spec definitions (dual-purpose) |
| `Lemmas.fsti` | `CLRS.Ch08.CountingSort.Lemmas.fsti` | ❌ | No interface file |
| `Complexity.fst` | `CLRS.Ch08.CountingSort.Complexity.fst` | ✅ | 32 lines, Θ(n+k) |
| `Complexity.fsti` | `CLRS.Ch08.CountingSort.Complexity.fsti` | ❌ | No interface file |
| `Impl.fst` | `CLRS.Ch08.CountingSort.Stable.fst` | 🔶 | Named `Stable` not `Impl`; faithful to CLRS |
| `Impl.fsti` | `CLRS.Ch08.CountingSort.Stable.fsti` | ❌ | No interface file |

**Extra files (not in rubric template):**
- `CLRS.Ch08.CountingSort.fst` — In-place non-CLRS variant (Pulse). Could be kept as a bonus or documented as supplementary.
- `CLRS.Ch08.CountingSort.StableLemmas.fst` — Lemmas specific to the stable variant. Fine as a support module.

### RadixSort

| Rubric Slot | Required File | Exists? | Notes |
|-------------|--------------|:-------:|-------|
| `Spec.fst` | `CLRS.Ch08.RadixSort.Spec.fst` | ✅ | Abstract multi-digit correctness |
| `Lemmas.fst` | `CLRS.Ch08.RadixSort.Stability.fst` / `FullSort.fst` | 🔶 | Split across Stability + FullSort; no single `Lemmas.fst` |
| `Lemmas.fsti` | `CLRS.Ch08.RadixSort.Lemmas.fsti` | ❌ | No interface file |
| `Complexity.fst` | `CLRS.Ch08.RadixSort.Complexity.fst` | ✅ | Θ(d(n+k)) |
| `Complexity.fsti` | `CLRS.Ch08.RadixSort.Complexity.fsti` | ❌ | No interface file |
| `Impl.fst` | `CLRS.Ch08.RadixSort.fst` | 🔶 | d=1 only; uses non-stable CountingSort |
| `Impl.fsti` | `CLRS.Ch08.RadixSort.Impl.fsti` | ❌ | No interface file |

**Extra files (valuable, not in rubric template):**
- `RadixSort.Base.fst` — Shared definitions (eliminates duplication). Keep.
- `RadixSort.Bridge.fst` — Pulse ↔ pure spec bridge. Keep.
- `RadixSort.MultiDigit.fst` — Concrete spec with insertion-sort-by-digit. Candidate to merge with `Spec.fst` or document as alternative track.

### BucketSort

| Rubric Slot | Required File | Exists? | Notes |
|-------------|--------------|:-------:|-------|
| `Spec.fst` | `CLRS.Ch08.BucketSort.Spec.fst` | ❌ | Spec + impl + lemmas all in single file |
| `Lemmas.fst` | `CLRS.Ch08.BucketSort.Lemmas.fst` | ❌ | Inline in `BucketSort.fst` |
| `Lemmas.fsti` | `CLRS.Ch08.BucketSort.Lemmas.fsti` | ❌ | No interface file |
| `Complexity.fst` | `CLRS.Ch08.BucketSort.Complexity.fst` | ❌ | Inline in `BucketSort.fst` (lines 608–695) |
| `Complexity.fsti` | `CLRS.Ch08.BucketSort.Complexity.fsti` | ❌ | No interface file |
| `Impl.fst` | `CLRS.Ch08.BucketSort.Impl.fst` | ❌ | Pure functional only; no Pulse impl |
| `Impl.fsti` | `CLRS.Ch08.BucketSort.Impl.fsti` | ❌ | No interface file |

---

## Rubric Compliance Summary

| Criterion | CountingSort | RadixSort | BucketSort |
|-----------|:---:|:---:|:---:|
| **Spec.fst** (pure specification) | 🔶 In `Lemmas.fst` | ✅ `Spec.fst` | ❌ Monolithic |
| **Lemmas.fst** (correctness proofs) | ✅ `Lemmas.fst` + `StableLemmas.fst` | 🔶 Split: `Stability` + `FullSort` | ❌ Inline |
| **Lemmas.fsti** (interface) | ❌ Missing | ❌ Missing | ❌ Missing |
| **Complexity.fst** | ✅ Standalone | ✅ Standalone | 🔶 Inline |
| **Complexity.fsti** (interface) | ❌ Missing | ❌ Missing | ❌ Missing |
| **Impl.fst** (Pulse impl) | 🔶 Named `Stable.fst` | 🔶 d=1 only | ❌ No Pulse impl |
| **Impl.fsti** (interface) | ❌ Missing | ❌ Missing | ❌ Missing |
| **Sorted postcondition** | ✅ | ✅ | ✅ |
| **Permutation postcondition** | ✅ | ✅ | ✅ (added) |
| **Stability postcondition** | ❌ Not proven | ✅ Abstract only | N/A |
| **Zero admits** | ✅ | ✅ | ✅ |
| **Zero assumes** | ✅ | ✅ | ✅ |
| **CLRS fidelity** | ✅ (Stable) / 🔶 (in-place) | 🔶 Pulse=d=1; pure=full | 🔶 Generalized |
| **Complexity connected to code** | ❌ Paper only | ❌ Paper only | ❌ Paper only |
| **SNIPPET markers** | ✅ Key signatures | ✅ Key signatures | ✅ Key signatures |

---

## Detailed Action Items

### Already Conformant ✅

1. **Zero admits/assumes across all 14 files** — fully verified.
2. **CountingSort.Stable.fst** faithfully implements all 4 CLRS phases with backward pass.
3. **RadixSort.Spec.fst** provides complete abstract correctness for CLRS Lemma 8.3.
4. **RadixSort.Stability.fst + FullSort.fst** prove the full inductive invariant: digit-by-digit → numeric order.
5. **RadixSort.Base.fst** centralizes shared definitions, eliminating ~340 lines of prior duplication.
6. **RadixSort.Bridge.fst** connects Pulse counting sort to abstract stability spec (d=0).
7. **Complexity modules** (CountingSort, RadixSort) have correct asymptotic bounds with upper + lower proofs.
8. **BucketSort permutation** postcondition has been added (audit T2 ✅ Done).
9. **SNIPPET markers** present on all key function signatures and definitions.
10. **Module headers** in all 14 files are accurate (stale doc claims fixed per audit T9).

### Needs Adjustment 🔶

| ID | Item | Affected Files | Rubric Gap | Effort |
|----|------|---------------|------------|--------|
| R1 | **Create `CountingSort.Spec.fst`** — Extract pure spec definitions (`sorted`, `permutation`, `in_range`) from `Lemmas.fst` into a dedicated Spec module. `Lemmas.fst` should then import and re-export or prove properties about the spec. | New `Spec.fst`, edit `Lemmas.fst` | Spec/Lemma separation | Low (1 day) |
| R2 | **Rename `CountingSort.Stable.fst` → `CountingSort.Impl.fst`** — or create `Impl.fst` that re-exports the stable variant as the canonical implementation. Keep `CountingSort.fst` (in-place) as a supplementary file. | `Stable.fst` → `Impl.fst` | Naming convention | Low (½ day) |
| R3 | **Create `.fsti` interface files** for all three algorithms. At minimum: `CountingSort.Lemmas.fsti`, `CountingSort.Complexity.fsti`, `RadixSort.Lemmas.fsti` (or `Stability.fsti` + `FullSort.fsti`), `RadixSort.Complexity.fsti`, `BucketSort.Lemmas.fsti`. | 5–7 new `.fsti` files | Interface files | Low–Med (1–2 days) |
| R4 | **Split `BucketSort.fst`** into `Spec.fst` (pure spec + `sorted`, `in_range`, `bucket_index`), `Lemmas.fst` (correctness proofs), `Complexity.fst` (cost analysis, currently lines 608–695), and eventually `Impl.fst` (Pulse). | Refactor 1 file → 3–4 files | File structure | Med (1–2 days) |
| R5 | **Consolidate RadixSort lemma files** — Either create a single `RadixSort.Lemmas.fst` that re-exports `Stability` + `FullSort`, or document that these two files together constitute the "Lemmas" slot. | `Stability.fst`, `FullSort.fst` | Rubric naming | Low (½ day) |

### Needs Work ❌

| ID | Item | Affected Files | Rubric Gap | Effort |
|----|------|---------------|------------|--------|
| R6 | **Prove stability in CountingSort.Stable postcondition** — The `ensures` clause proves `sorted ∧ permutation` but NOT stability (equal-key order preservation). The backward-pass implementation *is* stable; the proof must track input positions through Phase 4. This is the most critical spec gap. | `Stable.fst`, `StableLemmas.fst` | Correctness | High (2–3 days) |
| R7 | **Implement multi-digit Pulse RadixSort (d > 1)** — Current `RadixSort.fst` is d=1 only, using the non-stable in-place counting sort. Must loop `d` times calling `CountingSort.Stable` per digit. | `RadixSort.fst` (rewrite), possibly new files | Completeness | High (3–5 days) |
| R8 | **Remove `distinct` requirement from `RadixSort.MultiDigit`** — `radix_sort_correct` requires `distinct s`. CLRS handles duplicates. Generalize or document as a known limitation. | `MultiDigit.fst` | Generality | High (2–4 days) |
| R9 | **Create Pulse BucketSort implementation** — Currently pure F* only. Rubric requires a Pulse `Impl.fst` proven equivalent to the spec. | New `BucketSort.Impl.fst` | Impl slot | High (3–5 days) |
| R10 | **Connect complexity to code** — All three complexity modules are standalone arithmetic. No ghost ticks or cost instrumentation in any Pulse code. (Audit T8 attempted ghost ticks for CountingSort but reverted due to Z3 issues.) | All `Complexity.fst` files, Pulse files | Complexity connection | High (research) |

### Deferred / Low Priority

| ID | Item | Notes |
|----|------|-------|
| R11 | **Formalize uniform distribution for BucketSort** — CLRS assumes [0,1) uniform input. Current impl uses arbitrary int ranges. | Research-level; low priority |
| R12 | **Merge or deprecate one RadixSort proof track** — Three independent proofs of CLRS Lemma 8.3 (Spec, Stability, MultiDigit) is excessive. After R5, decide which to keep. | Depends on R5, R8 |

---

## Quality Checks

### Proof Integrity

| Check | Result |
|-------|--------|
| `admit()` calls | **0** across all 14 files ✅ |
| `assume` calls | **0** across all 14 files ✅ |
| `sorry` / `magic` | **0** ✅ |
| Max `z3rlimit` | 200 (Stability, Spec, BucketSort) — acceptable |
| `opaque_to_smt` usage | Correct: `permutation`, `phase4_c_inv`, `phase4_b_inv`, `sorted_up_to_digit`, `is_stable_sort_on_digit`, `is_stable_sort_by_digit` — all have explicit reveal helpers |

### Code Quality

| Check | Result |
|-------|--------|
| Duplication | 🔶 Reduced by `RadixSort.Base.fst` (audit T6 ✅) but some remains across `Spec`/`MultiDigit`/`FullSort` (~400 lines). See audit Appendix B. |
| Naming consistency | 🔶 Standardized on `sorted_on_digit` / `is_stable_sort_on_digit` (audit T11 ✅). Minor variants persist between `Spec` and `Stability`. |
| Module headers | ✅ All 14 files have accurate descriptions. Stale doc fixed (audit T9 ✅). |
| SNIPPET markers | ✅ Present on key signatures: `counting_sort_iterations`, `counting_sort_linear`, `counting_sort_stable_sig`, `radix_sort_sig`, `radix_sort_ops`, `radix_sort_theta_bound`, `radix_sort_multi`, `radix_sort_correct_multi`, `bucket_sort_sig`, `bucket_sort_sorted`, `append_sorted_disjoint`, `bucket_sort_linear_cost`, `counting_sort_lemma_defs`, `is_stable_sort_by` |

### Dependency Structure

```
CountingSort.Lemmas ←── CountingSort.fst  (in-place, Pulse)
         │
         └──────── CountingSort.Stable.fst  (CLRS-faithful, Pulse)
         │              │
CountingSort.StableLemmas ──┘
                            
CountingSort.Complexity     (standalone)

RadixSort.Base ←── RadixSort.Stability ←── RadixSort.FullSort   (Track B)
       │                    │
       │           RadixSort.Bridge ──→ CountingSort.Lemmas      (A↔B bridge)
       │
       ├── RadixSort.Spec                                        (Track C)
       ├── RadixSort.MultiDigit                                  (Track D)
       └── RadixSort.Complexity ──→ CountingSort.Complexity

RadixSort.fst ──→ CountingSort.fst  (Pulse, d=1)

BucketSort.fst                       (standalone, pure F*)
```

### Overall Rubric Score

| Rubric Dimension | Score | Notes |
|-----------------|:-----:|-------|
| File structure (7 slots × 3 algos = 21) | **8/21** slots filled | Missing: 7 `.fsti`, 2 `Spec.fst`, 2 naming mismatches, 1 Impl, 1 Complexity split |
| Proof completeness | **9/10** | Zero admits; stability postcondition is the one gap |
| CLRS fidelity | **8/10** | CountingSort.Stable excellent; RadixSort Pulse incomplete; BucketSort generalized |
| Complexity analysis | **6/10** | Correct bounds proven; not connected to implementations |
| Code quality | **7/10** | Duplication reduced but not eliminated; good opaque discipline |
| Documentation | **9/10** | Accurate headers, SNIPPET markers, stale docs fixed |
