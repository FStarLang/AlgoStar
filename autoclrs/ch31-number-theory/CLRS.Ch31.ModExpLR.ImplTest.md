# ModExpLR (L-to-R) Spec Validation Test

## Test: `3^5 mod 7 = 5`

### Input
- `b = 3`, `e = 5`, `m = 7`

### Expected Output
- `pow(3, 5) mod 7 = 243 mod 7 = 5`

### What is Proven

1. **Precondition satisfiability**: The only precondition is the ghost counter
   (`GR.pts_to ctr c0`), which is trivially satisfiable via `GR.alloc`.

2. **Postcondition precision (functional correctness)**: The postcondition states
   `result == mod_exp_spec b e m`. Combined with the normalization lemma
   `mod_exp_spec 3 5 7 == 5`, this uniquely determines `result == 5`.

3. **Postcondition precision (bounds)**: The postcondition states
   `result >= 0 /\ result < m`. For our input, this gives `0 ≤ 5 < 7`,
   which is verified.

4. **No admits, no assumes.**

### Spec Assessment

The ModExpLR specification is **precise and complete**:
- The postcondition uniquely determines the output for any valid input.
- The bounds postcondition (`0 ≤ result < m`) is correct and useful.
- The complexity bound (`cf - c0 ≤ num_bits(e)`) is a tight upper bound.
- No issues found with the specification.

### Concrete Execution Results

The verified Pulse implementation was extracted to C via KaRaMeL and executed natively.

- **Extraction**: `CLRS.Ch31.ModExpLR.Impl.mod_exp_lr_impl` extracts to C using
  `krml_checked_int_t` (int32 with overflow checking) for the mathematical
  `int`/`nat`/`pos` parameters. Ghost parameters and pure assertions are
  fully erased. The left-to-right binary exponentiation loop (scanning bits
  from MSB to LSB via `num_bits` and `pow2`) compiles to an idiomatic C
  while-loop.
- **Execution**: `test_mod_exp_lr()` calls `mod_exp_lr_impl(3, 5, 7)` and
  completes successfully. The extracted C code runs without overflow or
  runtime errors.
- **Status**: ✅ PASSED — C extraction, compilation, and execution all succeed.
