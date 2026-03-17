# Floyd-Warshall All-Pairs Shortest Paths — Review (CLRS §25.2)

**Last reviewed:** 2026-03-16
**Reviewer:** Copilot agent
**Verification status:** All 9 modules verify. Zero admits, zero assumes.
**Total verification time:** ~2m38s (clean build)

---

## Priority Checklist

Items to address, in priority order, for a fully proven, high-quality
implementation:

- [x] P1: Fix Warning 328 in Paths.fst — `lemma_concat_is_walk` declared
  recursive but recursion not used in body.
- [x] P2: Update RUBRIC_25.md — file inventory missing `NegCycleDetect.fst`,
  neg-cycle detection status stale (shows 🔶, should be ✅).
- [x] P3: Update README.md — stale precondition (`SZ.v n > 0` was removed),
  stale neg-cycle detection status (shows ❌, should be ✅).
- [ ] P4: Investigate Impl.fst verification time (1m48s, 68% of total) —
  global `--z3rlimit 40` may be overly broad; consider scoping or adding
  intermediate assertions to guide the solver.
- [ ] P5: Predecessor matrix (Π) — CLRS §25.2 feature, not implemented.
- [ ] P6: Infinity sentinel — hardcoded `inf = 1000000`; could use `option int`
  for a more robust formalization.

---

## Top-Level Signature

From `CLRS.Ch25.FloydWarshall.Impl.fsti`:

```fstar
fn floyd_warshall
  (dist: array int)
  (#contents: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to dist contents **
    GR.pts_to ctr c0 **
    pure (
      Seq.length contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns _:unit
  ensures exists* contents' (cf: nat).
    A.pts_to dist contents' **
    GR.pts_to ctr cf **
    pure (
      Seq.length contents' == SZ.v n * SZ.v n /\
      contents' == fw_outer contents (SZ.v n) 0 /\
      fw_complexity_bounded cf (reveal c0) (SZ.v n)
    )
```

### Parameters

* `dist` — mutable flat `n×n` distance matrix (row-major `int` array).
  Ghost variable `contents` captures the initial state.
* `n` — number of vertices (`SZ.t`). Handles n = 0 (empty graph) trivially.
* `ctr` — ghost counter for relaxation operations. Initial value `c0`.

### Preconditions

* `Seq.length contents == SZ.v n * SZ.v n` — properly sized matrix.
* `SZ.fits (SZ.v n * SZ.v n)` — no `SZ.t` overflow.

### Postcondition

* `contents' == fw_outer contents (SZ.v n) 0` — **functional refinement**:
  output equals the pure FW computation.
* `fw_complexity_bounded cf (reveal c0) (SZ.v n)` — exactly n³ relaxations.

---

## Profiling (clean build, per-file)

| File | Time | % of total | Notes |
|------|------|-----------|-------|
| `Spec.fst` | 1.9s | 1% | Fast |
| `Paths.fst` | 16.1s | 10% | 694 lines, 9 sections |
| `Impl.fsti` | 3.6s | 2% | |
| `Impl.fst` | **1m48s** | **68%** | ⚠ Bottleneck — Pulse loops with ghost ticks |
| `Lemmas.fsti` | 3.2s | 2% | |
| `Lemmas.fst` | 22.3s | 14% | |
| `NegCycleDetect.fst` | 9.0s | 6% | |
| `SpecTest.fst` | 41.6s | 26%* | High fuel (8) for concrete eval |
| `Test.fst` | 7.6s | 5% | |
| **Total** | **2m38s** | | *SpecTest runs in parallel with Impl |

`Impl.fst` dominates: its global `--z3rlimit 40` applies to the entire file
including all three loop invariant proofs. The Pulse loop discharge for the
triple-nested loop with ghost tick counting is inherently expensive.

### Solver settings

* Max rlimit: 40 (Impl.fst global, Lemmas.fst § 5, Paths.fst § 7–8)
* Max fuel: 8 (SpecTest.fst only — concrete evaluation)
* Max ifuel: 2 (SpecTest.fst, Paths.fst § 8)
* No `--z3seed` hacks, no `--retry`, no `--quake`
* `--split_queries always` used in Lemmas.fst § 2 and SpecTest.fst

---

## Correctness Chain

1. **Pulse → pure spec:** `contents' == fw_outer contents n 0` (Impl.fst)
2. **Pure spec → recurrence:** `fw_outer` computes `fw_entry` at level n
   (`floyd_warshall_computes_shortest_paths` in Lemmas.fst)
3. **Recurrence → shortest paths:** `fw_entry adj n i j n` = min walk weight
   (`fw_entry_leq_any_walk` + `fw_entry_eq_some_walk` in Paths.fst)
4. **Simplified entry point:** `floyd_warshall_full_correctness` derives the
   full chain from `weights_bounded` alone (Lemmas.fst)

---

## Specification Gaps and Limitations

1. ~~**No negative-cycle detection.**~~ **RESOLVED.** `NegCycleDetect.fst`
   provides `check_no_negative_cycle` (runtime diagonal scan) and
   `floyd_warshall_safe` (wrapper with `weights_bounded` precondition).

2. **No predecessor matrix.** CLRS §25.2 also computes Π for path
   reconstruction. This implementation computes distances only.

3. **Infinity sentinel.** `inf = 1000000` is a finite sentinel. The
   `weights_bounded` predicate guards against overflow but conflates
   "unreachable" with "weight ≥ 1000000".

4. ~~**Precondition: `SZ.v n > 0`.**~~ **RESOLVED.** Removed; n = 0 works.

5. ~~**`weights_bounded` not in Pulse precondition.**~~ **RESOLVED.**
   `floyd_warshall_safe` wrapper closes the gap.

---

## Rubric Compliance

| Rubric Artifact | Actual File(s) | Status |
|---|---|---|
| **Spec.fst** | `Spec.fst` | ✅ |
| **Lemmas.fst** | `Lemmas.fst` + `Paths.fst` | ✅ |
| **Lemmas.fsti** | `Lemmas.fsti` | ✅ |
| **Complexity** | Merged into `Impl.fst` (ghost ticks) | ✅ |
| **Impl.fst** | `Impl.fst` | ✅ |
| **Impl.fsti** | `Impl.fsti` | ✅ |

All 7 rubric artifacts present. Complexity merged into Impl.

---

## Spec Validation (ImplTest)

**File:** `CLRS.Ch25.FloydWarshall.ImplTest.fst`
**Status:** ✅ Fully proven — zero admits, zero assumes

Validates the `floyd_warshall` API from `Impl.fsti` on a concrete 3×3
graph. Proves:

1. **Precondition satisfiability** — array-size and `SZ.fits` constraints
   are met.
2. **Postcondition precision** — `contents' == fw_outer contents n 0` is
   strong enough to determine all 9 output entries exactly (0, 5, 20,
   45, 0, 15, 30, 35, 0).
3. **Complexity precision** — ghost tick counter gives exactly n³ = 27
   relaxation operations.

**No spec weaknesses found.** The postcondition is maximally precise
(full functional refinement), the precondition is minimal, and no
admits or assumes were needed. See `ImplTest.md` for details.

---

## Files (11 total)

| File | LOC | Role |
|------|-----|------|
| `Impl.fsti` | 45 | Public interface |
| `Impl.fst` | 154 | Pulse implementation with ghost ticks |
| `Spec.fst` | 141 | Pure spec: `fw_outer`, `fw_entry`, safety predicates |
| `Lemmas.fsti` | 121 | Lemma signatures |
| `Lemmas.fst` | 388 | Correctness proofs |
| `Paths.fst` | 694 | Graph-theoretic shortest path proofs (9 sections) |
| `NegCycleDetect.fst` | 107 | Runtime neg-cycle check + safe wrapper |
| `SpecTest.fst` | 77 | Concrete 3×3 verification |
| `Test.fst` | 133 | Pulse runtime tests (3×3, neg-cycle, empty graph) |
| `ImplTest.fst` | ~180 | **Spec validation test** — Impl.fsti API test with output assertions |
| `ImplTest.md` | — | Spec validation report |
