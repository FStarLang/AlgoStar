# Huffman Encode / Decode — Design & Implementation Plan

## Goal

Add symbol labels to the existing `htree` type, then build `huffman_encode` and
`huffman_decode` with a round-trip proof that `decode(encode(msg)) == msg` and
`encode(decode(bits)) == bits`, all connected to the existing Huffman development.

Finally, implement `Codec.Impl` in Pulse with proofs connecting to the pure Codec.

---

## Phase 1: Add `sym:nat` to `htree` Leaves

The existing type `Leaf : freq:pos -> htree` becomes `Leaf : sym:nat -> freq:pos -> htree`.
This makes the tree explicitly labeled with symbol indices (matching CLRS, where
leaves carry characters from an alphabet C).

### Blast radius (~430 occurrences across 10 files):

| File | Leaf occurrences | Difficulty |
|------|:----------------:|:----------:|
| `Huffman.Spec.fst` | ~249 | High — core type, all pattern matches |
| `Huffman.Complete.fst` | ~138 | High — constructs Leaf nodes, multiset reasoning |
| `Huffman.ForestLemmas.fst` | ~13 | Medium |
| `Huffman.PQForest.fst` | ~10 | Medium |
| `Huffman.Optimality.fst` | ~6 | Low |
| `Huffman.Complexity.fst` | ~6 | Low |
| `Huffman.Impl.fst` | ~5 | Low |
| `Huffman.ForestLemmas.fsti` | ~2 | Low |
| `Huffman.PQForest.fsti` | ~3 | Low |

### Mechanical changes:
- `| Leaf f ->` becomes `| Leaf _ f ->` (pattern match ignoring sym)
- `Leaf f` constructor becomes `Leaf c f` (need a sym value)
- Key: `huffman_complete` builds `Leaf` from frequency list — must assign sym indices
- `freq_of`, `leaf_freqs`, `weighted_path_length`, `cost` all match on `Leaf` — trivially updated

## Phase 2: Codec on Real `htree`

Build encode/decode directly on the modified `htree` type:
- `codeword : htree -> nat -> option (list bool)` — find path to leaf with given sym
- `encode : htree -> list nat -> option (list bool)` — concatenate codewords
- `decode : htree -> list bool -> option (list nat)` — walk tree, emit syms
- Round-trip proofs as in the current `Codec.fst` but using real `htree`

## Phase 3: Pulse `Codec.Impl`

Imperative encode/decode using the heap-allocated tree from `huffman_tree`.

---

## Implementation Order

1. Modify `htree` type in `Spec.fst` — add `sym:nat` field
2. Update `Spec.fst` — fix all pattern matches, constructors, and proofs
3. Update `Complete.fst` — fix Leaf construction (assign sym indices)
4. Update remaining files: Optimality, Complexity, ForestLemmas, PQForest, Impl
5. Verify all files
6. Rewrite `Codec.fst` on real `htree` (delete `ltree`)
7. Create `Codec.fsti`
8. Create `Codec.Impl.fst/.fsti` in Pulse
9. Verify everything, commit
