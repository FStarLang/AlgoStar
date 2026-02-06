# KMP String Matching - Verified Implementation in Pulse

This directory contains verified implementations of string matching algorithms from CLRS Chapter 32.

## Files

- **CLRS.Ch32.NaiveStringMatch.fst**: Naive string matching (O((n-m+1)*m))
- **CLRS.Ch32.KMP.fst**: KMP prefix function computation (O(m))
- **CLRS.Ch32.KMP.Test.fst**: Test cases for KMP prefix function

## KMP Prefix Function

The KMP algorithm preprocesses the pattern to build a "prefix function" π that encodes information about how the pattern matches against shifts of itself. This allows the matcher to skip unnecessary comparisons.

### Algorithm

Given pattern P[0..m-1], compute π[q] for each position q:
- π[q] = length of longest proper prefix of P[0..q] that is also a suffix of P[0..q]

```
compute_prefix(P, m):
  π[0] = 0
  k = 0
  for q = 1 to m-1:
    while k > 0 && P[k] != P[q]:
      k = π[k-1]
    if P[k] == P[q]:
      k = k + 1
    π[q] = k
  return π
```

### Example

Pattern: "ababaca"
Prefix function: π = [0, 0, 1, 2, 3, 0, 1]

Explanation:
- π[0] = 0 (by definition)
- π[1] = 0 (no proper prefix of "ab" is a suffix)
- π[2] = 1 ("a" is both prefix and suffix of "aba")
- π[3] = 2 ("ab" is both prefix and suffix of "abab")
- π[4] = 3 ("aba" is both prefix and suffix of "ababa")
- π[5] = 0 (no proper prefix of "ababac" is a suffix)
- π[6] = 1 ("a" is both prefix and suffix of "ababaca")

### Verification

The Pulse implementation proves:
- **Memory safety**: No out-of-bounds accesses, no memory leaks
- **Termination**: Both loops terminate (bounded by m)
- **Well-formedness**: Output satisfies 0 ≤ π[i] ≤ i for all i
- **No admits/assumes**: All proofs are complete

### Key Implementation Challenges

1. **Inner while loop complexity**: The condition `k > 0 && P[k] != P[q]` requires reading from the pattern array, which in Pulse is a stateful operation. To avoid ghost context issues, we:
   - Use a bounded outer loop (at most m iterations)
   - Read pattern values unconditionally
   - Use conditional logic to decide whether to update k
   - Break early when k stops decreasing

2. **Explicit array operations**: Pulse requires using `A.op_Array_Access` and `A.op_Array_Assignment` instead of shorthand notation like `a.(idx)`.

3. **Resource tracking**: The implementation explicitly tracks ownership of the pattern array (read-only) and the output array (mutable) through separation logic.

## Building and Testing

```bash
# Verify KMP implementation
make verify FSTAR_FILES="CLRS.Ch32.KMP.fst"

# Verify test cases
make verify FSTAR_FILES="CLRS.Ch32.KMP.Test.fst"

# Verify all files
make verify
```

## Requirements

- F* with Pulse support
- PULSE_ROOT environment variable set (or adjacent to FStar directory)

## References

- Cormen, T. H., Leiserson, C. E., Rivest, R. L., & Stein, C. (2009). *Introduction to Algorithms* (3rd ed.). MIT Press. Chapter 32: String Matching.
- Knuth, D. E., Morris, J. H., & Pratt, V. R. (1977). Fast pattern matching in strings. *SIAM Journal on Computing*, 6(2), 323-350.
