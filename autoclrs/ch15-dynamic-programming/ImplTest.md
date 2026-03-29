# Ch15 Dynamic Programming — Concrete Execution Results

## Extraction Pipeline

The verified Pulse implementations are extracted to C via:
1. **F\* → .krml**: `fstar.exe --codegen krml` produces KaRaMeL intermediate representation
2. **KaRaMeL → .c**: `krml` with bundle flags produces clean C files
3. **gcc → executable**: Compiled with KaRaMeL runtime support

Key extraction details:
- Impl modules are extracted with full transitive dependencies (so Pulse `fn` bodies compile)
- ImplTest modules are extracted per-module (small, no competing extern declarations)
- `Pulse.Lib.BoundedIntegers` typeclass instances are provided by `main.c`
- Ghost references (`GR.ref nat`) are erased during extraction

## Test Results

```
=== Ch15 Dynamic Programming — Extracted C Tests ===

Rod Cutting (extracted from verified Pulse):
  PASS: rod_cutting completed
  Input: prices = [1, 5, 8, 9], n = 4
  Expected: optimal_revenue = 10

LCS (extracted from verified Pulse):
  PASS: lcs completed
  Input: x = [1, 2, 3], y = [2, 3, 4], m = 3, n = 3
  Expected: lcs_length = 2

Matrix Chain (extracted from verified Pulse):
  PASS: matrix_chain completed
  Input: dims = [10, 30, 5, 60], n = 3
  Expected: mc_result = 4500

=== All 3 extracted tests passed ===
```

## How to Run

```bash
make           # Verify all 28 F* modules
make test-c    # Extract to C, compile, and run
```
