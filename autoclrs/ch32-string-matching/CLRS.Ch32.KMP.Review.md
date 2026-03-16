# KMP String Matching (CLRS §32.4)

**Last reviewed**: 2026-03-16

## Top-Level Signature

The combined KMP entry point is `kmp_string_match` in `CLRS.Ch32.KMP.fst`:

```fstar
fn kmp_string_match
  (#p_text #p_pat: perm)
  (text: array int)
  (pattern: array int)
  (#s_text: Ghost.erased (Seq.seq int))
  (#s_pat: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (m: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s_text /\
      SZ.v m == Seq.length s_pat /\
      Seq.length s_text <= A.length text /\
      Seq.length s_pat <= A.length pattern /\
      SZ.v m > 0 /\
      SZ.v n >= SZ.v m /\
      SZ.fits (SZ.v n + 1) /\
      SZ.fits (SZ.v m + 1) /\
      SZ.fits (2 * SZ.v n) /\
      SZ.fits (2 * (SZ.v m - 1)) /\
      SZ.fits (2 * SZ.v n + 2 * SZ.v m)
    )
  returns count: SZ.t
  ensures exists* (cf: nat).
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    GR.pts_to ctr cf **
    pure (
      SZ.v count >= 0 /\
      SZ.v count <= SZ.v n + 1 /\
      SZ.v count == Spec.count_matches_spec (reveal s_text) (reveal s_pat) (SZ.v n) (SZ.v m) /\
      kmp_total_complexity_bound cf (reveal c0) (SZ.v n) (SZ.v m)
    )
```

### Parameters

* `text` and `pattern` are arrays of `int` (not generic `eqtype`). Ghost
  sequences `s_text` and `s_pat` capture their contents.

* `n` is text length, `m` is pattern length (both `SZ.t`).

* `ctr` is a **ghost counter** tracking character comparisons.

### Preconditions

* `SZ.v m > 0` and `SZ.v n >= SZ.v m` — non-empty pattern, text at least as
  long.
* `SZ.fits` constraints on `2n`, `2(m-1)`, and `2n + 2m` ensure machine
  arithmetic safety.

### Postcondition

* `SZ.v count == Spec.count_matches_spec s_text s_pat n m` — The result
  equals the exact count of all pattern occurrences in the text.

* `kmp_total_complexity_bound cf (reveal c0) n m` — The total comparisons
  satisfy `cf - c0 ≤ 2n + 2m`.

## Auxiliary Definitions

### `is_prefix_suffix` (from `CLRS.Ch32.KMP.PureDefs`)

```fstar
let is_prefix_suffix (#a: eqtype) (pattern: seq a) (q: nat{q < length pattern}) (k: nat) : prop =
  k <= q /\
  (forall (i: nat). i < k ==> index pattern i == index pattern (q - k + 1 + i))
```

Does `pattern[0..k-1]` equal `pattern[q-k+1..q]`? This is the prefix-suffix
property underlying the KMP failure function.

### `pi_correct` (from `CLRS.Ch32.KMP.PureDefs`)

```fstar
let pi_correct (#a: eqtype) (pattern: seq a) (pi: seq SZ.t) : prop =
  length pi == length pattern /\
  length pattern > 0 /\
  (forall (q: nat). q < length pattern ==>
    is_prefix_suffix pattern q (SZ.v (index pi q)))
```

Each `pi[q]` is a valid prefix-suffix length at position `q`.

### `kmp_total_complexity_bound` (from `CLRS.Ch32.KMP.PureDefs`)

```fstar
let kmp_total_complexity_bound (c_final c_init n m: nat) : prop =
  c_final >= c_init /\
  c_final - c_init <= 2 * n + 2 * m
```

### `count_matches_spec` (from `CLRS.Ch32.KMP.Spec`)

```fstar
let count_matches_spec (text pattern: seq int) (n m: nat) : nat =
  if m > 0 && n >= m then count_matches_up_to text pattern n m 0
  else 0
```

## What Is Proven

1. **Full functional correctness**: The returned count equals
   `count_matches_spec`, which is proven equivalent to the naive
   count-all-matches specification. This means KMP finds **every** occurrence
   — no false positives and no false negatives.

2. **Prefix function correctness** (`pi_correct`): The computed `pi` array is
   a valid prefix-suffix table.

3. **Prefix function maximality** (`pi_max_sz`): Each `pi[q]` is the
   **longest** proper prefix-suffix at position `q`. This is critical for
   proving completeness — the failure chain explores all valid prefix-suffix
   lengths.

4. **O(n + m) complexity**: The total comparison count satisfies
   `cf - c0 ≤ 2n + 2m`. This decomposes into:
   - Prefix function: at most `2(m - 1)` comparisons.
   - Matching phase: at most `2n` comparisons.

5. **Amortized analysis via potential function**: The proof uses the potential
   function Φ = k (current matched length) for both phases. Each comparison
   either extends the match (Φ increases by 1, cost 1) or follows the failure
   chain (Φ decreases, cost 1), so `cost + Φ ≤ 2 * position`.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **Restricted to `int` sequences.** The implementation uses `int` arrays,
   not generic `eqtype`. The prefix function computation
   (`compute_prefix_function`) is generic over `eqtype`, but the matcher and
   the Spec module are specialized to `int`.

2. **Complexity constant factor.** The bound `2n + 2m` is a constant-factor
   bound, not the tightest possible. The prefix function needs at most
   `2(m-1)` comparisons, and the matcher at most `2n`, giving `2n + 2m - 2`
   in the tightest analysis. The specification rounds up.

3. **No output of match positions.** Like the naive matcher, KMP returns the
   count of matches, not their positions. CLRS prints each shift.

4. **Bridge module required.** The connection between the Pulse implementation
   (which proves `pi_correct` and `pi_max_sz` over `seq SZ.t`) and the
   completeness specification (which requires `pi_max` over `seq int`) goes
   through `CLRS.Ch32.KMP.Bridge`. The bridge converts SZ.t sequences to int
   sequences and proves the maximality transfer. This is structurally sound
   but adds proof complexity.

5. **`kmp_total_complexity_bound` proven in aggregate.** The bound is proven
   via the ghost counter across both phases (prefix function + matching).
   The implementation allocates the `pi` vector, calls
   `compute_prefix_function`, then `kmp_matcher`, and the ghost counter
   accumulates both phases.

6. **Non-standard file naming.** `KMP.PureDefs.fst` serves as the Spec file
   and `KMP.Spec.fst` serves as the Lemmas file. The naming doesn't follow
   the RUBRIC convention. Renaming risks breaking all inter-module imports.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Prefix function comparisons | ≤ 2(m−1) | ✅ Ghost counter | Upper bound |
| Matching comparisons | ≤ 2n | ✅ Ghost counter | Upper bound |
| **Total comparisons** | **≤ 2n + 2m** | **✅ Ghost counter** | **Upper bound** |

The complexity is **fully linked**: `tick ctr` is called at each comparison
(both in the failure-chain inner loop and the extend-check step) across both
the prefix function and matching phases. The amortized potential Φ = k
(current prefix length) ensures each tick is accounted for.

## Proof Structure

### Prefix Function (`compute_prefix_function`)

Maintains the invariant that `pi` is correct and maximal for positions
`0..q-1`. The inner loop follows the failure chain from `pi[q-1]`, checking
each candidate. The `all_ps_above_mismatch` invariant tracks that all
prefix-suffix lengths above the current `k` have been checked and found to
mismatch `pattern[q]`.

Maximality is proven incrementally: `extend_maximality` in `Bridge.fst`
extends maximality from `0..q-1` to `0..q` after each outer iteration.

### Matching (`kmp_matcher`)

Maintains `is_max_prefix_below text pattern i q` — `q` is the longest prefix
of the pattern that matches a suffix of `text[0..i-1]`. On each text character:

1. Follow failure chain until `q = 0` or `pattern[q] = text[i]`.
2. Optionally extend `q`.
3. If `q = m`, record match and reset via `pi[m-1]`.

The connection to `count_matches_spec` goes through `Spec.kmp_count_step`,
which proves that the KMP step correctly tracks the count.

## Profiling

| File | Approx. time |
|------|-------------|
| `KMP.fst` | ~700s ⚠️ **major bottleneck** |
| `KMP.Spec.fst` | ~114s ⚠️ |
| `KMP.Bridge.fst` | ~8s |
| `KMP.PureDefs.fst` | ~1s |
| `KMP.Test.fst` | ~2s |

`KMP.fst` dominates the total build time (~700s / 12 minutes). The file
contains three major Pulse functions with nested while loops and complex
amortized invariants. The `compute_prefix_function` inner loop and `kmp_matcher`
inner loop each require `--z3rlimit 120`. `#restart-solver` between major
functions helps prevent solver state accumulation.

`KMP.Spec.fst` (~114s) contains the completeness proof with recursive
definitions and case-analysis lemmas. Uses `--z3refresh` for stability.

## Files

| File | Role |
|------|------|
| `CLRS.Ch32.KMP.fst` | Pulse: `compute_prefix_function`, `kmp_matcher`, `kmp_string_match` |
| `CLRS.Ch32.KMP.PureDefs.fst` | `is_prefix_suffix`, `pi_correct`, complexity bounds, lemmas |
| `CLRS.Ch32.KMP.Spec.fst` | Completeness spec: `is_max_prefix_below`, `follow_fail`, `kmp_count_step` |
| `CLRS.Ch32.KMP.Bridge.fst` | `pi_max_sz`, `pi_optimal_extension`, SZ↔int conversion |
| `CLRS.Ch32.KMP.Test.fst` | Runtime test: text=[0,1,0,1,0], pattern=[0,1,0] |

## Checklist

- [x] Functional correctness (count == count_matches_spec)
- [x] Prefix function correctness and maximality
- [x] O(n+m) complexity proven and linked via ghost counter
- [x] Amortized analysis with potential function
- [x] Zero admits / assumes
- [x] CLRS-faithful algorithm
- [x] Uses shared `CLRS.Common.Complexity.tick` (resolved 2026-03-16)
- [x] `#restart-solver` between major functions (added 2026-03-16)
- [ ] `KMP.fst` proof time (~700s) — nested loops with amortized invariants are expensive; the `compute_prefix_function` section needed rlimit bump from 100→120 after switching to common tick
- [ ] `KMP.Spec.fst` proof time (~114s) — recursive completeness proof is inherently complex
- [ ] Missing `Impl.fsti` — no public interface file for the Pulse implementation
- [ ] Non-standard file naming — `PureDefs` is Spec, `Spec` is Lemmas, `Bridge` is also Lemmas
- [ ] Missing `Complexity.fst` / `Complexity.fsti` — bounds inline in `PureDefs.fst` and `KMP.fst`
- [ ] Missing `Lemmas.fsti` — no interface file for the completeness/bridging lemmas
- [ ] Restricted to `int` — matcher and Spec not generic over `eqtype`
- [ ] `matches_at` defined locally — duplicates `NaiveStringMatch.Spec`
