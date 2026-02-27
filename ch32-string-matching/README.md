# Chapter 32: String Matching — Verified Implementations

This directory contains verified implementations of string matching algorithms from CLRS Chapter 32, in both Pulse (imperative, separation-logic verified) and pure F*.

## Files

### Naive String Matching (§32.1)
- **CLRS.Ch32.NaiveStringMatch.fst**: Pulse implementation of NAIVE-STRING-MATCHER. Proves full functional correctness (`count == count_matches_up_to`) and O((n-m+1)*m) complexity. Generic over `eqtype`. No admits.

### Rabin-Karp (§32.2)
- **CLRS.Ch32.RabinKarp.fst**: Pulse implementation using a simple character-sum hash (not the CLRS polynomial hash). Proves full functional correctness (`count == count_matches_up_to`). No admits.
- **CLRS.Ch32.RabinKarp.Spec.fst**: Pure F* specification using the faithful CLRS polynomial hash with Horner's rule. Proves both no-false-positives and no-false-negatives (`rabin_karp_find_all_correct`). No admits.
- **CLRS.Ch32.RabinKarp.Complexity.fst**: Pure F* complexity analysis: O(n+m) best case, O(nm) worst case.

### KMP (§32.4)
- **CLRS.Ch32.KMP.PureDefs.fst**: Shared pure definitions (`is_prefix_suffix`, `pi_correct`, complexity bounds).
- **CLRS.Ch32.KMP.fst**: Pulse implementation of COMPUTE-PREFIX-FUNCTION and KMP-MATCHER. Proves memory safety, prefix function maximality (`pi_max_sz` — pi is the LONGEST prefix-suffix), full functional correctness (`count == count_matches_spec`), and O(n+m) complexity via amortized analysis. No admits.
- **CLRS.Ch32.KMP.Bridge.fst**: Bridging lemmas connecting Pulse `pi_max_sz` (SZ.t sequences) to Spec's `pi_max` (int sequences). Incremental proof helpers for the maximality invariant. No admits.
- **CLRS.Ch32.KMP.Spec.fst**: Pure F* completeness proof that KMP finds all matches. Proves `kmp_step_maximal`, `kmp_match_iff`, `kmp_count_step`, and `count_before_eq_spec`. No admits.
- **CLRS.Ch32.KMP.Test.fst**: Pulse test cases for `compute_prefix_function` and `kmp_string_match`.

### Reference
- **reference/reference.fst**: Port of `FStar/examples/algorithms/StringMatching.fst`. Contains verified naive matcher and Rabin-Karp with CLRS polynomial hash. Returns `option nat` (first match only).
- **reference/test_without_lemma.fst**: 9-line smoke test for `RabinKarp.Spec.rabin_karp_find_all`.

## Verification Status

| Algorithm | Correctness | Complexity | Admits? |
|-----------|:-----------:|:----------:|:-------:|
| Naive (Pulse) | count == spec | O((n-m+1)*m) | None |
| Rabin-Karp (Pulse) | count == spec | (pure analysis only) | None |
| Rabin-Karp (Spec) | bidirectional | N/A (pure) | None |
| KMP (Pulse) | count == spec | O(n+m) | None |
| KMP (Spec, pure) | count == spec | N/A (pure) | None |

All three algorithms now have **complete functional correctness proofs** (`count == count_matches_spec`) with **zero admits**.

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
