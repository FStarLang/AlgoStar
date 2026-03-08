# Chapter 32: String Matching — Verified Implementations

## Overview

Verified implementations of string matching algorithms from CLRS Chapter 32:

1. **Naive String Match** (§32.1) — O(nm) linked complexity, Pulse implementation
2. **Knuth-Morris-Pratt** (§32.4) — O(n+m) amortized, Pulse implementation
3. **Rabin-Karp** (§32.2) — O(nm) worst / O(n+m) expected, pure F* + Pulse

**All three algorithms have zero admits in implementations, specifications, and complexity analyses.**

- **~2900 lines** across 13 verified modules
- Full functional correctness: `count == count_matches_spec`
- No false positives, no false negatives (Rabin-Karp pure)
- Amortized O(n+m) complexity for KMP with exact bound `cf - c0 ≤ 2n + 2m`

---

## 1. Naive String Match — CLRS §32.1

### Specification

From `NaiveStringMatch.Spec.fst`:

```fstar
let matches_at (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat) : prop =
  s + Seq.length pattern <= Seq.length text /\
  (forall (j: nat). j < Seq.length pattern ==>
    Seq.index text (s + j) == Seq.index pattern j)
```

`count_matches_up_to text pattern limit` counts the number of valid shifts in `[0, limit)` where the pattern matches.

### Correctness Theorem

The Pulse implementation from `NaiveStringMatch.fst`:

```pulse
fn naive_string_match
  (#a: eqtype) ...
  (text: array a) (pattern: array a) ...
  (n: SZ.t) (m: SZ.t)
  (ctr: GR.ref nat) (#c0: erased nat)
  ...
  returns result: SZ.t
  ensures exists* (cf: nat). ... ** pure (
    SZ.v result <= SZ.v n - SZ.v m + 1 /\
    SZ.v result == count_matches_up_to s_text s_pat (SZ.v n - SZ.v m + 1) /\
    string_match_complexity_bounded cf (reveal c0) (SZ.v n) (SZ.v m))
```

**Postcondition breakdown:**

| Conjunct | Meaning |
|----------|---------|
| `result == count_matches_up_to s_text s_pat (n-m+1)` | Exact match count equals pure specification |
| `string_match_complexity_bounded cf c0 n m` | Ghost counter satisfies `cf - c0 ≤ (n-m+1)·m` |

**Note**: There is no separate `Impl.fsti` — the function is defined directly in `NaiveStringMatch.fst`.

### Strongest Guarantee

The postcondition provides the exact match count (not just "found a match"), which is the strongest possible guarantee for a counting algorithm. The complexity bound is tight: `(n-m+1)·m` character comparisons.

### Complexity

From `NaiveStringMatch.Complexity.fsti`:

```fstar
let string_match_complexity_bounded (cf c0 n m: nat) : prop =
  cf >= c0 /\ cf - c0 <= (n - m + 1) * m
```

The ghost counter ticks once per character comparison in the inner loop. The outer loop runs `n-m+1` times, the inner loop at most `m` times each, giving the `(n-m+1)·m` bound.

**No admits. No assumes.**

### Limitations

None. Fully verified end-to-end.

---

## 2. Knuth-Morris-Pratt (KMP) — CLRS §32.4

### Specification

From `KMP.PureDefs.fst`:

```fstar
let is_prefix_suffix (#a: eqtype) (pattern: seq a) (q: nat{q < length pattern}) (k: nat) : prop =
  k <= q /\
  (forall (i: nat). i < k ==> index pattern i == index pattern (q - k + 1 + i))
```

```fstar
let pi_correct (#a: eqtype) (pattern: seq a) (pi: seq SZ.t) : prop =
  length pi == length pattern /\
  length pattern > 0 /\
  (forall (q: nat). q < length pattern ==>
    is_prefix_suffix pattern q (SZ.v (index pi q)))
```

`pi_correct` asserts that for every position `q` in the pattern, `pi[q]` gives a valid prefix-suffix length. The bridge module proves maximality: `pi[q]` is the LONGEST such prefix-suffix.

### Correctness Theorem — Prefix Function

From `KMP.fst`:

```pulse
fn compute_prefix_function
  (#a: eqtype) ...
  (pattern: array a) (pi: V.vec SZ.t) ... (m: SZ.t)
  (ctr: GR.ref nat) (#c0: erased nat)
  ...
  returns _: unit
  ensures exists* s_pi (cf: nat). ... ** pure (
    Seq.length s_pi == SZ.v m /\
    pi_correct s_pat s_pi /\
    Bridge.pi_max_sz s_pat s_pi /\
    prefix_function_complexity_bound cf (reveal c0) (SZ.v m))
```

The postcondition guarantees `pi_correct` (validity) AND `pi_max_sz` (maximality).

### Correctness Theorem — Matcher

From `KMP.fst`:

```pulse
fn kmp_matcher ... (n: SZ.t) (m: SZ.t)
  (ctr: GR.ref nat) (#c0: erased nat)
  ...
  returns count: SZ.t
  ensures exists* (cf: nat). ... ** pure (
    SZ.v count >= 0 /\
    SZ.v count <= SZ.v n + 1 /\
    SZ.v count == Spec.count_matches_spec (reveal s_text) (reveal s_pat) (SZ.v n) (SZ.v m) /\
    matcher_complexity_bound cf (reveal c0) (SZ.v n))
```

**Postcondition:** The returned count equals the pure specification `count_matches_spec`, and the ghost counter satisfies `cf - c0 ≤ 2·n`.

### Strongest Guarantee

The KMP implementation provides:
- **Exact match count** — not just "found/not found"
- **Maximality of π** — `pi[q]` is the longest proper prefix-suffix (via `Bridge.pi_max_sz`)
- **Completeness** — every match is counted (proven via `Spec.kmp_match_iff` and `kmp_count_step`)
- **Tight complexity** — exact bound `cf - c0 ≤ 2n + 2m`, not just asymptotic O(n+m)

### Complexity

From `KMP.PureDefs.fst`:

```fstar
let kmp_total_complexity_bound (c_final c_init n m: nat) : prop =
  c_final >= c_init /\
  c_final - c_init <= 2 * n + 2 * m
```

The bound `2n + 2m` follows from the amortized analysis:

- **Prefix function**: at most `2·(m-1)` comparisons. The potential function is `k` (current match length). Each tick either advances `q` or decreases `k`.
- **Matching**: at most `2·n` comparisons. The potential function is `q` (current match position). Each comparison either advances the text pointer or decreases the match length.

The proof restructures inner loops to only tick for actual failure-chain follows (not exit iterations), tightening invariants to exact amortized potential bounds:
- Prefix computation: `vc - c0 + k ≤ 2·(q - 1)`
- Matching: `vc - c0 + q ≤ 2·i`

**No admits. No assumes.**

### Limitations

None. Fully verified.

---

## 3. Rabin-Karp — CLRS §32.2

### Specification

From `RabinKarp.Spec.fst`:

```fstar
let rec hash (x:Seq.seq nat) (d:nat) (q:nat{q <> 0})
             (i:nat) (j:nat{i <= j /\ j <= Seq.length x})
  : Tot nat (decreases j - i)
  = if i = j then 0
    else (d * hash x d q i (j - 1) + Seq.index x (j - 1)) % q
```

CLRS polynomial hash via Horner's rule: `hash(x, d, q, i, j) = x[i]·d^(j-i-1) + ... + x[j-1]·d^0 (mod q)`.

The rolling hash step:

```fstar
let rolling_hash_step (ts:nat) (old_char:nat) (new_char:nat)
                      (d:nat) (q:pos) (h:nat) : nat =
  (d * ((ts + q - (old_char * h) % q) % q) + new_char) % q
```

### Correctness Theorem — Pure

From `RabinKarp.Spec.fst`, the complete correctness theorem:

```fstar
let rabin_karp_find_all_correct (text pattern:Seq.seq nat) (d:nat) (q:nat{q <> 0})
  : Lemma (let results = rabin_karp_find_all text pattern d q in
           (forall (pos:nat). List.Tot.mem pos results ==> matches_at text pattern pos) /\
           (Seq.length pattern > 0 ==>
             (forall (pos:nat). pos + Seq.length pattern <= Seq.length text /\
                                matches_at text pattern pos ==> List.Tot.mem pos results)))
```

This proves **no false positives** (every returned position is a valid match) and **no false negatives** (every valid match is returned).

### Correctness Theorem — Pulse

From `RabinKarp.fst`:

```pulse
fn rabin_karp ... (n: SZ.t) (m: SZ.t) (d: nat) (q: pos)
  ...
  returns result: int
  ensures ... **
    pure (result >= 0 /\ result <= SZ.v n - SZ.v m + 1 /\
          result == count_matches_up_to s_text s_pat (SZ.v n - SZ.v m + 1))
```

The Pulse implementation returns the exact match count, matching `count_matches_up_to`.

### Rolling Hash Correctness

From `RabinKarp.Spec.fst`:

```fstar
let rolling_hash_step_correct
    (text:Seq.seq nat) (d:nat) (q:pos)
    (s:nat) (m:nat{m > 0 /\ s + m < Seq.length text})
    (current_hash:nat{current_hash == hash text d q s (s + m)})
    (h:nat{h == pow_mod d (m - 1) q})
  : Lemma (rolling_hash_step current_hash (Seq.index text s) (Seq.index text (s + m)) d q h
           == hash text d q (s + 1) (s + m + 1))
```

Proves the imperative rolling hash step computes the correct hash for the next window.

### Strongest Guarantee

The pure specification proves bidirectional correctness (no false positives AND no false negatives) for any hash parameters `d` and `q`. The Pulse implementation returns the exact match count.

### Complexity

From `RabinKarp.Complexity.fsti`:

```fstar
let rk_best_case (n m: nat) : nat =
  m + (if n >= m then n - m + 1 else 0)

let rk_worst_case (n m: nat) : nat =
  m + (if n >= m then (n - m + 1) * m else 0)
```

- **Best case**: O(n+m) when no spurious hash collisions occur
- **Worst case**: O(nm) when all hash values collide (every position requires verification)

**No admits. No assumes.**

### Limitations

- **Pure implementation**: The Rabin-Karp specification and correctness proofs are in pure F*, not Pulse. The Pulse wrapper wraps the pure logic.
- **Expected-case analysis not formalized**: The O(n+m) expected time (depending on hash quality / prime choice) is stated but not formally proven. Only the worst-case O(nm) is proven as a formal bound.

---

## File Inventory

| File | Lines | Role | Admits/Assumes |
|------|------:|------|:--------------:|
| `CLRS.Ch32.NaiveStringMatch.Spec.fst` | 44 | Pure spec: `matches_at`, `count_matches_up_to` | 0 |
| `CLRS.Ch32.NaiveStringMatch.Lemmas.fsti` | — | Correctness lemma interface | 0 |
| `CLRS.Ch32.NaiveStringMatch.Lemmas.fst` | 48 | `matches_at_dec_correct`, `count_matches_up_to_bounded` | 0 |
| `CLRS.Ch32.NaiveStringMatch.Complexity.fsti` | — | Complexity interface | 0 |
| `CLRS.Ch32.NaiveStringMatch.Complexity.fst` | 24 | `string_match_complexity_bounded` — O((n−m+1)·m) | 0 |
| `CLRS.Ch32.NaiveStringMatch.fst` | 179 | Pulse implementation with ghost tick counter | 0 |
| `CLRS.Ch32.RabinKarp.Spec.fst` | 368 | Hash, rolling hash, `rabin_karp_find_all`, correctness proofs | 0 |
| `CLRS.Ch32.RabinKarp.Lemmas.fsti` | — | Correctness lemma interface | 0 |
| `CLRS.Ch32.RabinKarp.Lemmas.fst` | 110 | `no_false_positives`, `no_false_negatives`, `find_all_correct` | 0 |
| `CLRS.Ch32.RabinKarp.Complexity.fsti` | — | Complexity interface | 0 |
| `CLRS.Ch32.RabinKarp.Complexity.fst` | 103 | O(n+m) best case, O(nm) worst case | 0 |
| `CLRS.Ch32.RabinKarp.fst` | 326 | Pulse implementation with rolling hash | 0 |
| `CLRS.Ch32.KMP.PureDefs.fst` | 112 | `is_prefix_suffix`, `pi_correct`, complexity bounds | 0 |
| `CLRS.Ch32.KMP.Spec.fst` | 623 | Completeness: `kmp_step_maximal`, `kmp_match_iff`, `kmp_count_step` | 0 |
| `CLRS.Ch32.KMP.Bridge.fst` | 383 | Connects Pulse `pi_correct` to `Spec.pi_max` | 0 |
| `CLRS.Ch32.KMP.fst` | 486 | Pulse `compute_prefix_function` + `kmp_matcher` + O(n+m) | 0 |
| `CLRS.Ch32.KMP.Test.fst` | 77 | Test cases for prefix function and matcher | 0 |

## Summary

| Algorithm | CLRS | Correctness | Complexity | Admits |
|-----------|------|:-----------:|:----------:|:------:|
| Naive | §32.1 | count == spec | O((n−m+1)·m) linked | **0** ✅ |
| KMP | §32.4 | count == spec | O(n+m) = 2n+2m exact | **0** ✅ |
| Rabin-Karp (pure) | §32.2 | bidirectional (no FP/FN) | O(nm) worst, O(n+m) best | **0** ✅ |
| Rabin-Karp (Pulse) | §32.2 | count == spec | (linked to pure) | **0** ✅ |

## Building

```bash
cd ch32-string-matching
make verify

# Verify a specific file
make verify FSTAR_FILES="CLRS.Ch32.KMP.fst"
```

## References

- CLRS 3rd Edition, Chapter 32: String Matching (§32.1, §32.2, §32.4)
- Knuth, D. E., Morris, J. H., & Pratt, V. R. (1977). Fast pattern matching in strings. *SIAM Journal on Computing*, 6(2), 323-350.
- Pulse separation logic: https://github.com/FStarLang/pulse
