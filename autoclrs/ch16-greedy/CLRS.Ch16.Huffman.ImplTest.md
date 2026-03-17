# Huffman Tree Construction — Spec Validation Test

## Test Instance

Two symbols with frequencies [3, 5] (n=2).

## What Is Tested

The test calls `huffman_tree` from `CLRS.Ch16.Huffman.Impl.fsti` on a
2-element frequency array and proves postcondition precision.

1. **Precondition satisfiability**: The precondition is satisfiable
   for `n=2`, `SZ.fits (2*2+2)`, and all frequencies positive.

2. **Postcondition precision — cost**: The postcondition `cost ft == greedy_cost(input)`
   uniquely determines `cost ft == 8`.
   - `seq_to_pos_list [3; 5] 0` has the same multiset as `[3; 5]` (proven
     element-by-element via `seq_to_pos_list_freqseq2`)
   - `greedy_cost [3; 5] == 8` via `greedy_cost_sorted_unfold` and
     `greedy_cost_singleton`
   - `greedy_cost_multiset_invariant` bridges the two forms

3. **Postcondition precision — optimality**: `is_wpl_optimal ft [3; 5]`
   means the tree minimizes weighted path length over all binary trees
   with the same leaf frequency multiset. Combined with `cost == 8`, this
   gives `wpl == 8` (via `wpl_equals_cost`).

4. **Complexity**: The ghost counter satisfies `huffman_merge_bound cf 0 2`,
   proving exactly `n-1 = 1` merge iteration. Verified: `cf == 1`.

## Proof Techniques

- `greedy_cost_sorted_unfold` to unfold greedy cost for a 2-element list
- `greedy_cost_singleton` for base case
- `greedy_cost_multiset_invariant` to bridge `seq_to_pos_list` and `[3; 5]`
- `seq_to_pos_list_length` and element-by-element count equality

## Result

**PASS** — All assertions verified. Zero admits, zero assumes.

The postcondition of `huffman_tree` is precise enough to:
- Determine the exact cost of the tree (via `greedy_cost` equality)
- Determine the exact number of merge iterations (via complexity bound)
- Guarantee WPL optimality (strongest possible statement)

## Specification Quality Assessment

The `Impl.fsti` specification for Huffman tree construction is **excellent**:
- The `is_wpl_optimal` postcondition is the strongest possible optimality
  guarantee
- `same_frequency_multiset` ensures the tree uses exactly the right frequencies
- `cost == greedy_cost` ties the imperative output to the pure algorithm
- `huffman_merge_bound` provides exact complexity tracking

The only limitation is that the tree structure is not uniquely determined
(multiple trees can have the same WPL), but this is by design — the spec
correctly captures the relational nature of the output.

No specification improvements needed.

## Attribution

Test pattern inspired by
[Test.Quicksort.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch07-quicksort/Test.Quicksort.fst)
from the intent-formalization repository.
