# Chapter 32: String Matching — Verified Implementations

This directory contains verified implementations of string matching algorithms from CLRS Chapter 32, in both Pulse (imperative, separation-logic verified) and pure F*.

## Rubric Structure

Each algorithm follows the rubric structure from `RUBRIC.md`:
- **Spec.fst** — Pure F* specification (definitions, decidable checks)
- **Lemmas.fst / .fsti** — Correctness proofs about the specification
- **Complexity.fst / .fsti** — Complexity analysis and bounds
- **Impl** (main `.fst`) — Pulse implementation, proven equivalent to spec

## Files

### Naive String Matching (§32.1)

| File | Rubric Role | Description |
|------|-------------|-------------|
| `CLRS.Ch32.NaiveStringMatch.Spec.fst` | **Spec** | Pure spec: `matches_at`, `matches_at_dec`, `count_matches_up_to` |
| `CLRS.Ch32.NaiveStringMatch.Lemmas.fst` | **Lemmas** | Correctness: `matches_at_dec_correct`, `count_matches_up_to_bounded` |
| `CLRS.Ch32.NaiveStringMatch.Lemmas.fsti` | **Lemmas interface** | Public signatures for correctness lemmas |
| `CLRS.Ch32.NaiveStringMatch.Complexity.fst` | **Complexity** | Bound: `string_match_complexity_bounded` — O((n−m+1)·m) |
| `CLRS.Ch32.NaiveStringMatch.Complexity.fsti` | **Complexity interface** | Public signatures for complexity |
| `CLRS.Ch32.NaiveStringMatch.fst` | **Impl** | Pulse implementation with ghost tick counter |

### Rabin-Karp (§32.2)

| File | Rubric Role | Description |
|------|-------------|-------------|
| `CLRS.Ch32.RabinKarp.Spec.fst` | **Spec** | CLRS polynomial hash (Horner's rule), rolling hash, `matches_at`, `verify_match`, `rabin_karp_find_all` |
| `CLRS.Ch32.RabinKarp.Lemmas.fst` | **Lemmas** | Bidirectional correctness: `no_false_positives`, `no_false_negatives`, `find_all_correct` |
| `CLRS.Ch32.RabinKarp.Lemmas.fsti` | **Lemmas interface** | Public signatures for correctness lemmas |
| `CLRS.Ch32.RabinKarp.Complexity.fst` | **Complexity** | O(n+m) best case, O(nm) worst case |
| `CLRS.Ch32.RabinKarp.Complexity.fsti` | **Complexity interface** | Public signatures for complexity |
| `CLRS.Ch32.RabinKarp.fst` | **Impl** | Pulse implementation with rolling hash from `RabinKarp.Spec` |

### KMP (§32.4)

| File | Rubric Role | Description |
|------|-------------|-------------|
| `CLRS.Ch32.KMP.PureDefs.fst` | **Spec** | `is_prefix_suffix`, `pi_correct`, `matches_at`, complexity bounds |
| `CLRS.Ch32.KMP.Spec.fst` | **Lemmas** (completeness) | Full completeness proof: `kmp_step_maximal`, `kmp_match_iff`, `kmp_count_step`, `count_before_eq_spec` |
| `CLRS.Ch32.KMP.Bridge.fst` | **Lemmas** (bridging) | Connects Pulse `pi_correct` to `Spec.pi_max` via `pi_optimal_extension` |
| `CLRS.Ch32.KMP.fst` | **Impl** | Pulse `compute_prefix_function` + `kmp_matcher` + `kmp_string_match` with O(n+m) complexity |
| `CLRS.Ch32.KMP.Test.fst` | Test | Pulse test cases for prefix function and matcher |

### Reference (not part of verified library)
- `reference/reference.fst` — Port of `FStar/examples/algorithms/StringMatching.fst`
- `reference/test_without_lemma.fst` — Smoke test for `RabinKarp.Spec.rabin_karp_find_all`

## Verification Status

| Algorithm | Correctness | Complexity | Admits? | .fsti? |
|-----------|:-----------:|:----------:|:-------:|:------:|
| Naive (Pulse) | count == spec | O((n-m+1)·m) | None | ✅ Lemmas, Complexity |
| Rabin-Karp (Spec) | bidirectional | N/A (pure) | None | — |
| Rabin-Karp (Lemmas) | bidirectional | N/A | None | ✅ |
| Rabin-Karp (Pulse) | count == spec | (pure analysis only) | None | — |
| Rabin-Karp (Complexity) | — | O(n+m) / O(nm) | None | ✅ |
| KMP (Pulse) | count == spec | O(n+m) | None | — |
| KMP (Spec, pure) | count == spec | N/A (pure) | None | — |

All algorithms have **complete functional correctness proofs** with **zero admits**.

## Building

```bash
# Verify all files
make verify

# Verify a specific file
make verify FSTAR_FILES="CLRS.Ch32.KMP.fst"
```

## Requirements

- F* with Pulse support
- PULSE_ROOT environment variable set (or adjacent to FStar directory)

## References

- Cormen, T. H., Leiserson, C. E., Rivest, R. L., & Stein, C. (2009). *Introduction to Algorithms* (3rd ed.). MIT Press. Chapter 32: String Matching.
- Knuth, D. E., Morris, J. H., & Pratt, V. R. (1977). Fast pattern matching in strings. *SIAM Journal on Computing*, 6(2), 323-350.
