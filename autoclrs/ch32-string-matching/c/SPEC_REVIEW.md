# Ch32 String Matching — C Specification Review

## Overview

This document compares the specifications proven in the Pulse implementations
(`CLRS.Ch32.*.fst`) against the specifications in the C implementations
(`c/*.c`) verified via c2pulse.

**Goal**: Ensure the C code has specifications that match (modulo representation
changes) what the Pulse implementations prove.

---

## 1. NaiveStringMatch

### Pulse Impl Spec (`CLRS.Ch32.NaiveStringMatch.fst :: naive_string_match`)

```
requires:  n == len(text), m == len(pattern), m > 0, m <= n, fits constraints
ensures:   result <= n - m + 1
           result == count_matches_up_to s_text s_pat (n - m + 1)
           string_match_complexity_bounded cf c0 n m
```

### C Spec (`NaiveStringMatch.c :: naive_string_match`)

```
requires:  text._length == n, pattern._length == m, m > 0, m <= n
ensures:   return <= n - m + 1
           SizeT.v return == count_matches_up_to (unwrap_seq text n) (unwrap_seq pattern m) (n - m + 1)
```

### Comparison

| Property | Pulse | C | Status |
|----------|-------|---|--------|
| Count bound (`<= n - m + 1`) | ✅ | ✅ | Match |
| Functional correctness (`count_matches_up_to`) | ✅ | ✅ | Match |
| Complexity bound | ✅ | ❌ (removed per task) | OK |

**Verdict: ✅ Specs match (modulo complexity, which is intentionally removed).**

---

## 2. KMP — `compute_prefix`

### Pulse Impl Spec (`CLRS.Ch32.KMP.fst :: compute_prefix_function`)

```
requires:  m == len(pattern), m > 0, fits constraints
ensures:   pi_correct s_pat s_pi          (each pi[q] is a valid prefix-suffix)
           Bridge.pi_max_sz s_pat s_pi    (each pi[q] is the LONGEST prefix-suffix)
           prefix_function_complexity_bound cf c0 m
```

### C Spec (`KMP.c :: compute_prefix`)

```
requires:  pattern._length == m, pi._length == m, m > 0, m < 2147483647
ensures:   pi._length == m, pattern._length == m
           forall j < m: pi[j] >= 0
           forall j < m: pi[j] <= j
           pi_max_up_to_int pattern pi m   (maximality: pi is longest prefix-suffix)
```

### Comparison

| Property | Pulse | C | Status |
|----------|-------|---|--------|
| pi bounds (`>= 0`, `<= j`) | ✅ | ✅ | Match |
| pi validity (each pi[q] is a prefix-suffix) | ✅ via `pi_correct` | ✅ via `pi_max_up_to_int` | Match |
| pi maximality (LONGEST prefix-suffix) | ✅ via `pi_max_sz` | ✅ via `pi_max_up_to_int` | Match |
| Complexity bound | ✅ | ❌ (removed per task) | OK |

**Verdict: ✅ Specs match.**

---

## 3. KMP — `kmp_count`

### Pulse Impl Spec (`CLRS.Ch32.KMP.fst :: kmp_matcher`)

```
requires:  pi_correct, Bridge.pi_max_sz, m > 0, n >= m, fits constraints
ensures:   count <= n - m + 1
           count == Spec.count_matches_spec text pat n m
           matcher_complexity_bound cf c0 n
```

### C Spec (`KMP.c :: kmp_count`)

```
requires:  text._length == n, pattern._length == m, pi._length == m
           m > 0, m <= n, m < 2147483647
           pi bounds (>= 0, <= j)
           pi_max (maximality of pi)
ensures:   return <= n - m + 1
           pi bounds preserved
           SizeT.v return == count_matches_spec (unwrap_int_seq text n) (unwrap_int_seq pattern m) n m
```

### Comparison

| Property | Pulse | C | Status |
|----------|-------|---|--------|
| Count bound (`<= n - m + 1`) | ✅ | ✅ | Match |
| Functional correctness (`count_matches_spec`) | ✅ | ✅ | Match |
| pi preservation in postcondition | implicit (read-only) | ✅ (explicit) | Match |
| Complexity bound | ✅ | ❌ (removed per task) | OK |

**Verdict: ✅ Specs match.**

---

## 4. RabinKarp

### Pulse Impl Spec (`CLRS.Ch32.RabinKarp.fst :: rabin_karp`)

```
requires:  n == len(text), m == len(pattern), m > 0, m <= n, fits constraints
ensures:   result >= 0, result <= n - m + 1
           result == count_matches_up_to s_text s_pat (n - m + 1)
           rk_complexity_bounded cf c0 n m
```

### C Spec (`RabinKarp.c :: rabin_karp`)

```
requires:  text._length == n, pattern._length == m
           m > 0, m <= n, d > 0, q > 1
           (d+1)*q < 2147483647, q*q < 2147483647
           forall i < n: text[i] >= 0 && text[i] < q
           forall i < m: pattern[i] >= 0 && pattern[i] < q
ensures:   return <= n - m + 1
           SizeT.v return == count_matches_up_to (unwrap_nat_seq text n) (unwrap_nat_seq pattern m) (n - m + 1)
```

### Comparison

| Property | Pulse | C | Status |
|----------|-------|---|--------|
| Count bound (`<= n - m + 1`) | ✅ | ✅ | Match |
| Functional correctness (`count_matches_up_to`) | ✅ | ✅ | Match |
| Complexity bound | ✅ | ❌ (removed per task) | OK |

### C Helper Functions

| Function | Spec Strength | Notes |
|----------|---------------|-------|
| `horner_hash` | Weak: only `0 <= return < q` | Does NOT prove `return == hash(arr, d, q, 0, hash_len)` |
| `compute_h` | Weak: only `0 <= return < q` | Does NOT prove `return == pow_mod(d, len-1, q)` |
| `check_match` | Weak: `return <= 1` + partial match | Not called from `rabin_karp` (dead code) |
| `rolling_hash_step` | Weak: only `0 <= return < q` | Not called from `rabin_karp` (dead code) |

**Note**: The helper functions' weak specs are not a problem because the main
`rabin_karp` function inlines the matching logic and proves correctness via
its own loop invariants. The dead helper functions (`check_match`,
`rolling_hash_step`) are retained because removing them causes Z3
non-determinism in the main function's verification.

**Verdict: ✅ Main spec matches. Helper specs are weak but not needed for top-level correctness.**

---

## 5. `_include_pulse` Block Analysis

All three C files use `_include_pulse` only for `open` statements:

- `NaiveStringMatch.c`: `open Spec`, `open Lemmas`, `open C.BridgeLemmas`
- `KMP.c`: `open PureDefs`, `open Spec`, `open C.BridgeLemmas`, `open Bridge`
- `RabinKarp.c`: `open Spec`, `open C.BridgeLemmas`

**No computationally relevant code in `_include_pulse` blocks. ✅**

---

## 6. Complexity Instrumentation

None of the three C files contain complexity-related code (no `tick`, no
ghost counters, no complexity bounds in postconditions).

**✅ Already removed.**

---

## 7. Dead Code

- `RabinKarp.c`: `check_match` and `rolling_hash_step` are defined but never
  called from the main `rabin_karp` function. These are vestigial helpers.
  Note: Removing them causes Z3 non-determinism (the verification of
  `rabin_karp` becomes unstable without the helpers present as context),
  so they are left in place.

---

## 8. Action Items

- [x] `_include_pulse` blocks: clean (no action needed)
- [x] Complexity removal: already done (no action needed)
- [x] NaiveStringMatch specs: match Pulse impl
- [x] KMP specs: match Pulse impl
- [x] RabinKarp specs: match Pulse impl
- [x] Dead code: noted but retained (Z3 stability)
