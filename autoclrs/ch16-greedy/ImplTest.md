# Chapter 16 — ImplTest Concrete Execution Results

## Extraction Pipeline

The verified F\*/Pulse code extracts to C via KaRaMeL and compiles to a native
test binary.

```
make -j1        # verify all 30 F*/Pulse modules
make extract    # krml .krml → .c
make test-c     # compile + link + run
```

## Test Results

```
=== Ch16 ImplTest C Extraction Tests ===

--- Activity Selection test ---
  PASS (proof: optimality verified; runtime: count=2, sel=[0,2])

--- Huffman Tree test ---
  PASS (proof: cost=8, WPL-optimal; runtime: input preserved)

=== All ch16 tests passed ===
```

### Activity Selection (`CLRS.Ch16.ActivitySelection.ImplTest`)

- **Input**: 3 activities with start/finish times
- **Runtime checks**: `count == 2`, selected indices `[0, 2]`
- **Verified properties**: greedy optimality, correct selection count
- **Status**: ✅ PASS

### Huffman Tree (`CLRS.Ch16.Huffman.ImplTest`)

- **Input**: frequencies `[3, 5]` (n=2)
- **Runtime checks**: input array preserved (`freqs[0]==3, freqs[1]==5`)
- **Verified properties**: `cost == 8`, `same_frequency_multiset`, `is_wpl_optimal`,
  merge count = 1, leaf labels valid
- **Status**: ✅ PASS

### Huffman Codec (`CLRS.Ch16.Huffman.Codec.ImplTest`)

- **Verified properties**: encode/decode roundtrip, correct bit sequences
- **Status**: ✅ Verified (machine-checked proofs pass), but **not extracted to C**
  because `Codec.Impl` functions take `HSpec.htree` as a non-erased parameter
  for runtime tree traversal, making them non-C-representable via KaRaMeL.

## Modules Extracted

| Module | Extracted | Tested |
|--------|-----------|--------|
| `CLRS.Ch16.ActivitySelection.Impl` | ✅ | ✅ |
| `CLRS.Ch16.Huffman.Impl` | ✅ | ✅ |
| `CLRS.Ch16.Huffman.Codec.Impl` | ❌ (htree not C-representable) | ✅ (verified only) |

## No Admits or Assumes

All 30 modules verify without `admit()` or `assume_`.
