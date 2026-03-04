# Chapter 08: Linear-Time Sorting — Rubric Compliance

**Updated:** 2025-07-23
**Source files:** 16 `.fst`/`.fsti` files (all verified, zero admits)
**Canonical rubric:** `RUBRIC.md` (root)

---

## Current File Inventory

| # | File | Lang | Status |
|---|------|------|--------|
| 1 | `CLRS.Ch08.CountingSort.Spec.fst` | F* | ✅ Core spec: sorted, sorted_prefix, permutation (opaque), in_range |
| 2 | `CLRS.Ch08.CountingSort.Lemmas.fst` | F* | ✅ Proof helpers + lemma proofs; imports Spec |
| 3 | `CLRS.Ch08.CountingSort.Lemmas.fsti` | F* | ✅ Interface: `let` defs + `val` lemma sigs |
| 4 | `CLRS.Ch08.CountingSort.StableLemmas.fst` | F* | ✅ Phase-specific lemmas for CLRS stable variant |
| 5 | `CLRS.Ch08.CountingSort.Impl.fst` | Pulse | ✅ CLRS-faithful 4-phase stable + in-place variant |
| 6 | `CLRS.Ch08.CountingSort.Impl.fsti` | Pulse | ✅ Interface for both counting_sort_impl and counting_sort_inplace |
| 7 | `CLRS.Ch08.RadixSort.Spec.fst` | F* | ✅ Abstract multi-digit correctness |
| 8 | `CLRS.Ch08.RadixSort.Lemmas.fst` | F* | ✅ Aggregates Stability + FullSort |
| 9 | `CLRS.Ch08.RadixSort.Base.fst` | F* | ✅ Shared definitions |
| 10 | `CLRS.Ch08.RadixSort.Stability.fst` | F* | ✅ Core CLRS Lemma 8.3 stability proof |
| 11 | `CLRS.Ch08.RadixSort.FullSort.fst` | F* | ✅ Digit decomposition → numeric bridge |
| 12 | `CLRS.Ch08.RadixSort.Bridge.fst` | F* | ✅ CountingSort ↔ RadixSort.Base equivalences |
| 13 | `CLRS.Ch08.RadixSort.MultiDigit.fst` | F* | 🔶 Requires `distinct` |
| 14 | `CLRS.Ch08.RadixSort.fst` | Pulse | ✅ d=1 radix sort using counting_sort_inplace |
| 15 | `CLRS.Ch08.BucketSort.Spec.fst` | F* | ✅ Actual definitions: sorted, insert, bucket fns |
| 16 | `CLRS.Ch08.BucketSort.Lemmas.fst` | F* | ✅ Actual proofs + bucket_sort main fn |

---

## Files Removed (intentional)

| File | Reason |
|------|--------|
| `CountingSort.fst` | In-place variant moved into `Impl.fst` as `counting_sort_inplace` |
| `CountingSort.Stable.fst` | Renamed to `Impl.fst` |
| `CountingSort.Complexity.fst` + `.fsti` | Trivial (user-requested removal) |
| `RadixSort.Complexity.fst` + `.fsti` | Trivial, nothing depends on them |
| `BucketSort.fst` | Subsumed by Spec.fst + Lemmas.fst split |
| `BucketSort.Complexity.fst` | Trivial (user-requested removal) |

---

## Rubric Compliance Matrix

### CountingSort

| Rubric Slot | File | Status |
|-------------|------|:------:|
| `Spec.fst` | `CountingSort.Spec.fst` | ✅ |
| `Lemmas.fst` | `CountingSort.Lemmas.fst` | ✅ |
| `Lemmas.fsti` | `CountingSort.Lemmas.fsti` | ✅ |
| `Complexity.fst` | — | ❌ Removed (trivial) |
| `Complexity.fsti` | — | ❌ Removed (trivial) |
| `Impl.fst` | `CountingSort.Impl.fst` | ✅ |
| `Impl.fsti` | `CountingSort.Impl.fsti` | ✅ |

**5/7 slots filled** (Complexity removed as trivial per user request)

Extra: `CountingSort.StableLemmas.fst` — support module for stable variant lemmas.

### RadixSort

| Rubric Slot | File | Status |
|-------------|------|:------:|
| `Spec.fst` | `RadixSort.Spec.fst` | ✅ |
| `Lemmas.fst` | `RadixSort.Lemmas.fst` | ✅ |
| `Lemmas.fsti` | — | ❌ Deferred |
| `Complexity.fst` | — | ❌ Removed (trivial) |
| `Complexity.fsti` | — | ❌ Removed (trivial) |
| `Impl.fst` | `RadixSort.fst` | 🔶 d=1 only |
| `Impl.fsti` | — | ❌ Deferred |

**3/7 slots filled**

Extra: `Base.fst`, `Bridge.fst`, `Stability.fst`, `FullSort.fst`, `MultiDigit.fst` — valuable support modules.

### BucketSort

| Rubric Slot | File | Status |
|-------------|------|:------:|
| `Spec.fst` | `BucketSort.Spec.fst` | ✅ |
| `Lemmas.fst` | `BucketSort.Lemmas.fst` | ✅ |
| `Lemmas.fsti` | — | ❌ Deferred |
| `Complexity.fst` | — | ❌ Removed (trivial) |
| `Complexity.fsti` | — | ❌ Removed (trivial) |
| `Impl.fst` | — | ❌ Pure functional only |
| `Impl.fsti` | — | ❌ No Pulse impl |

**2/7 slots filled**

---

## Proof Integrity

| Check | Result |
|-------|--------|
| `admit()` calls | **0** across all 16 files ✅ |
| `assume` calls | **0** across all 16 files ✅ |
| Max `z3rlimit` | 400 (StableLemmas.fst, Impl.fst) — acceptable |
| All files verified | ✅ `make -j4` passes |

---

## Dependency Structure

```
CountingSort.Spec ←── CountingSort.Lemmas ←── CountingSort.StableLemmas ←── CountingSort.Impl
                                                                              (stable + inplace)

RadixSort.Base ←── RadixSort.Stability ←── RadixSort.FullSort
       │                    │
       │           RadixSort.Bridge ──→ CountingSort.Spec/Lemmas
       │
       ├── RadixSort.Spec
       └── RadixSort.MultiDigit

RadixSort.fst ──→ CountingSort.Impl (counting_sort_inplace)

BucketSort.Spec ←── BucketSort.Lemmas
```

---

## Overall Score

| Dimension | Score |
|-----------|:-----:|
| Rubric slots (7 × 3 = 21) | **10/21** (6 removed as trivial, 5 deferred) |
| Proof completeness | **10/10** Zero admits, zero assumes |
| CLRS fidelity | **8/10** CountingSort.Impl excellent; RadixSort d=1 only |
| Code quality | **9/10** No duplication, proper Spec/Lemmas/Impl split |
