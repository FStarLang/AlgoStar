# Ch16 Greedy — Specification Gap Review

## Overview

This document catalogs specification gaps between the C code in ch16/c and
the full verified F\* specifications in the Impl.fsti files, and documents
the results of the improvement effort.

**Build status**: All files verified successfully (`make clean && make` passes).

---

## 1. ActivitySelection.c vs CLRS.Ch16.ActivitySelection.Impl.fsti

### Properties in Impl.fsti (`activity_selection_post`):
1. ✅ `count <= n` — C: `return <= n`
2. ✅ `n == 0 ==> count == 0` — C: `n == 0 ==> return == 0`
3. ✅ `n > 0 ==> count >= 1` — C: `n > 0 ==> return >= 1`
4. ✅ `out[0] == 0` — C: `n > 0 ==> out[0] == 0`
5. ✅ `all_valid_indices` — C: `forall j < count. out[j] < n`
6. ✅ `strictly_increasing` — C: `forall j. j+1 < count ==> out[j] < out[j+1]`
7. ✅ `pairwise_compatible` — C: `forall j. j+1 < count ==> finish[out[j]] <= start[out[j+1]]`
8. ✅ `earliest_compatible (between)` — C loop ensures + function ensures
9. ⚠️ `earliest_compatible (after last)` — C loop ensures only, NOT in function postcondition
10. ❌ `max_compatible_count` (optimality) — missing from C, needs bridge lemma

### Complexity:
- ✅ No complexity instrumentation in C code (already clean)

### `_include_pulse` block:
- ✅ No `_include_pulse` block — ActivitySelection.c is clean

### Admits:
- ✅ **0 admits** in ActivitySelection.c

### Bridge Lemma:
- ⚠️ 1 `assume` in `CLRS.Ch16.ActivitySelection.C.BridgeLemmas.fst` (line 44)
- Reason: The "after last" part of `earliest_compatible` IS verified in the C
  loop ensures (line 111-112 of ActivitySelection.c), but c2pulse cannot export
  loop `_ensures` facts to the function postcondition. After `let mut var_count = count`,
  the loop's `count` becomes `!var_count` in Pulse, and facts about `count` from
  `_ensures` don't transfer to the function return context.
- **Status: c2pulse limitation — cannot fix without framework changes**

---

## 2. HuffmanCost.c vs CLRS.Ch16.Huffman.Impl.fsti

### Properties in Impl.fsti (`huffman_tree` postcondition):
1. ❌ `cost == greedy_cost` — C only proves `return > 0`
2. ❌ `same_frequency_multiset` — not applicable (no tree built)
3. ❌ `is_wpl_optimal` — not applicable (no tree built)
4. ❌ `huffman_merge_bound` (complexity) — not applicable
5. ❌ `tree_leaf_labels_valid` — not applicable (no tree built)

### Note:
HuffmanCost.c implements only the merge-cost computation (root frequency),
not the full tree construction. The Impl.fsti doesn't have a separate spec
for just the merge cost — this is auxiliary code.

### `_include_pulse` block:
- ✅ No `_include_pulse` block

### Admits:
- ✅ **1 admit** (reduced from 6 original)
- Remaining: Line 139 — overflow safety for `min1 + min2`

### Improvement details (6 → 1 admits):
1. **Removed admits 1-2** (parameter-to-ref bridge): Restructured sum loop to
   start from `i=0, total_sum=0` instead of `i=1, total_sum=freq[0]`. This
   avoids accessing `freq[0]` before the loop, eliminating the need to bridge
   quantified preconditions from `var_freq` (parameter) to `!var_freq` (ref).
2. **Removed admits 3-4** (positivity/propagation): Discovered that loop
   `_ensures` clauses cause pure facts to NOT propagate to subsequent code
   (Pulse limitation). Removed all `_ensures` and relied solely on `_invariant`
   facts. Added `n > 0` and `total_sum >= i` invariants.
3. **Removed admit 5** (if-else fact loss): Changed `if (n>1) mq_len=n-1 else mq_len=1`
   to `mq_len = n`. If-else blocks in Pulse drop pure facts at the join point.
4. **Cannot remove admit 6** (overflow safety): Proving `min1 + min2 <= total_sum`
   requires sum conservation: the sum of all queue elements equals `total_sum`
   at every iteration. This requires a recursive ghost function over the array's
   snapshot sequence (`Seq.seq (option Int32.t)`), which c2pulse's C-level
   specification language cannot reference. The array snapshot is existentially
   quantified in the generated Pulse code and has no C-level name.

### c2pulse limitations discovered:
1. **Loop `_ensures` fact propagation**: Facts in `_ensures` do NOT propagate
   to code after the loop. Workaround: use only `_invariant`.
2. **If-else join drops pure facts**: Pure facts established before an if-else
   block are lost after the join. Workaround: restructure code to avoid if-else.
3. **Ghost sum over array snapshots**: Cannot define recursive ghost functions
   over array snapshot sequences from C-level specifications.

---

## 3. HuffmanTree.c vs CLRS.Ch16.Huffman.Impl.fsti

### Properties in Impl.fsti (`huffman_tree` postcondition):
1. ❌ `cost == greedy_cost` — not proven in C
2. ❌ `same_frequency_multiset` — not proven in C
3. ❌ `is_wpl_optimal` — not proven in C
4. ❌ `huffman_merge_bound` — not proven in C
5. ❌ `tree_leaf_labels_valid` — not proven in C
6. ⚠️ `is_htree` ghost predicate — defined but used with admits

### `_include_pulse` block content:
- `is_htree` recursive predicate — ✅ specification/ghost only
- `elim_is_htree_leaf` — ✅ ghost function
- `intro_is_htree_leaf` — ✅ ghost function
- `elim_is_htree_internal` — ✅ ghost function
- `intro_is_htree_internal` — ✅ ghost function

All content in `_include_pulse` is specifications/ghost — ✅ compliant

### Admits:
- ⚠️ **18 admits** (unchanged — all are genuine c2pulse/Pulse limitations)
- `free_htree`: 3 admits (ghost fold/unfold for recursive tree walk)
- `root_freq`: 2 admits (ghost fold/unfold for reading node)
- `huffman_tree`: 13 admits (tree construction proofs)

### Analysis of why admits cannot be removed:

**root_freq and free_htree (5 admits)**: The `is_htree` predicate places the
Leaf/Internal discriminator (null left/right pointers) INSIDE the existentially
quantified struct. To unfold `is_htree p ft`, one must case-split on `ft` —
but `ft` is an abstract/erased ghost variable at the call site. A generic
`elim_is_htree_any` ghost function was attempted with a `match ft` body (similar
to DLLPtr's `elim_is_dll_nonnull`), but Pulse's SL solver cannot normalize
`match ft with ...` expressions in postconditions when `ft` is known only in
a specific match branch. Error: "Cannot prove: match ft with ...". The DLLPtr
pattern works because its discriminator (`is_null head`) is visible OUTSIDE the
predicate as a runtime value, allowing C-level `if` to dispatch to case-specific
ghost functions. For `is_htree`, the discriminator is hidden inside.

**huffman_tree (13 admits)**:
- 1 admit: parameter-to-ref bridge (quantified preconditions about `var_freq` don't
  transfer to `!var_freq` after `let mut`)
- 4 admits: struct field write after `alloc_ref` (individual field writes via
  `p->sym = 0; p->freq = ...` need explicit `aux_raw_unfold_uninit`/`aux_raw_fold`
  around them, which c2pulse doesn't insert)
- 3 admits: array ownership tracking (writing allocated pointers into arrays
  requires ownership transfer that c2pulse can't express)
- 2 admits: allocator arrays ownership (after `calloc`, array ownership predicates
  need proper initialization)
- 1 admit: Int32 overflow for `min1_freq + min2_freq` (same sum conservation issue
  as HuffmanCost.c)
- 1 admit: final postcondition (array ownership handback for `freq`)
- 1 admit: early return path (leaf case postcondition)

### Bridge Lemma:
- ✅ 0 admits in `CLRS.Ch16.Huffman.C.BridgeLemmas.fst`

---

## Summary

| File | Original Admits | Final Admits | Notes |
|------|----------------|--------------|-------|
| ActivitySelection.c | 0 | **0** | Clean |
| ActivitySelection Bridge | 1 assume | **1 assume** | c2pulse limitation |
| HuffmanCost.c | 6 | **1** | 5 removed via restructuring |
| HuffmanTree.c | 18 | **18** | All genuine Pulse limitations |
| Huffman Bridge | 0 | **0** | Clean |

### Key c2pulse/Pulse limitations identified:

1. **Parameter-to-ref bridge**: After `let mut var = param`, quantified facts
   about `param` don't transfer to `!var`. Workaround: restructure code to
   establish facts via loop invariants instead.

2. **Loop `_ensures` fact propagation**: Facts in `_ensures` don't propagate
   past the loop. Workaround: use `_invariant` only.

3. **If-else pure fact loss**: Pure facts are dropped at if-else join points.
   Workaround: avoid if-else by restructuring code.

4. **Recursive predicate case-split**: When a recursive predicate's discriminator
   is inside an existential (e.g., `is_htree`'s null-pointer check is inside
   `exists* nd.`), there is no way to case-split at the C level. Pulse's SL
   solver cannot normalize `match` expressions in postconditions.

5. **Ghost sum over array snapshots**: Cannot define recursive ghost functions
   over array snapshot sequences (existentially quantified in generated Pulse
   code) from C-level specifications.

6. **Struct field writes after alloc**: Individual field writes (`p->field = val`)
   after `alloc_ref` require explicit `aux_raw_unfold_uninit`/`aux_raw_fold` that
   c2pulse doesn't auto-insert. Aggregate initialization (`*p = (struct){...}`)
   may work but is not always applicable.

---

## Representation Bridge Notes

The C code uses:
- `int` → `Int32.t` (c2pulse representation)
- `size_t` → `SizeT.t`
- Array reads use `array_read` (c2pulse generated)
- Struct fields use `struct_hnode__freq` etc.

The Impl.fsti uses:
- `int` (F\* unbounded integer)
- `SZ.t` (= `SizeT.t`)
- `Seq.index` for array access
- Direct struct fields

Bridge lemmas need to convert between these representations,
primarily via `Int32.v` and `SizeT.v` coercions.
