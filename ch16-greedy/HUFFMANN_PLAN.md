# Huffman Module Action Plan

## Current State (2025-02-27)

### File sizes
| File | Lines | `.checked` |
|------|------:|:----------:|
| `CLRS.Ch16.Huffman.fst` | 3,019 (working copy; 2,596 committed) | ❌ Never verified |
| `CLRS.Ch16.Huffman.Spec.fst` | 2,124 | ✅ |
| `CLRS.Ch16.Huffman.Complete.fst` | 1,807 | ✅ |
| `CLRS.Ch16.Huffman.Optimality.fst` | 353 | ✅ |
| `CLRS.Ch16.Huffman.Complexity.fst` | 225 | ✅ |
| `TestHuffman.fst` | 48 | ✅ |

### Git history summary

The last committed state (`544a84c`) has a single `admit()` inside the
merge loop of `huffman_tree` (line ~2538 of committed version):
```
    // TODO: maintain pq_tree_freq_match, forest_has_pq_entry, cost invariant
    admit ();
```
The committed version maintained some invariants inline (pq_freqs_positive,
pq_idx_unique, pq_forest, node_ptr_correspondence, leaf_freq multiset) but
left three properties unproven: `pq_tree_freq_match`, `forest_has_pq_entry`,
and the cost invariant.

### Uncommitted working copy (+510 lines, -87 lines)

A long-running agent attempted to eliminate the `admit()` by:
1. Adding ~170 lines of new helper lemmas for the cost invariant (e.g.
   `cost_invariant_merge_step`, `cost_invariant_from_merge_bundle`,
   `forest_root_freqs_remove_two_le`, `freq2_le_at_rem_pos`,
   `freq2_le_remaining_root_freqs`)
2. Adding ~110 lines of new helpers for `forest_has_pq_entry` maintenance
   (`forest_has_pq_entry_remove_two`, `forest_distinct_indices_remove_at/two`,
   `pq_indices_in_forest_shrink`, `remaining_no_idx`,
   `forest_has_pq_entry_prepend`)
3. Adding `merge_bundle_intro` and `merge_bundle_step` (~90 lines) that
   encapsulates ALL invariant maintenance in a single F* lemma
4. Simplifying the Pulse merge loop body from ~60 inline proof lines to
   ~15 lines (just calling `merge_bundle_step`)
5. Adding `node_ptr_correspondence_upd_nat`, `forest_total_cost_merge_step_any`,
   `forest_root_freqs_length` (moved from later in file), etc.
6. Adding `SZ.fits n` to `merge_bundle` and `init_to_merge_bundle` requires

The working copy has **zero admits/assumes** — but it was **never verified**.
The agent crashed before verification completed. The file is now 3,019 lines
and likely takes 10+ minutes to verify (if it verifies at all).

### Current postcondition of `huffman_tree`
```fstar
ensures A.pts_to freqs freq_seq **
        (exists* ft. is_htree result ft **
                pure (HSpec.cost ft >= 0 /\
                      HSpec.same_frequency_multiset ft (seq_to_pos_list freq_seq 0)))
```
This proves:
- ✅ `cost ft >= 0`
- ✅ `same_frequency_multiset ft initial_freqs`
- ❌ `HSpec.cost ft == HOpt.greedy_cost initial_freqs` (NOT in postcondition)
- ❌ `HSpec.is_wpl_optimal ft initial_freqs` (NOT in postcondition)

### What the merge_bundle cost invariant gives us at loop exit

The `merge_bundle` predicate (opaque) carries:
```
forest_total_cost active + HOpt.greedy_cost (forest_root_freqs active) ==
  HOpt.greedy_cost (seq_to_pos_list freq_seq 0)
```
When the loop exits with `L.length active_final == 1`:
- `forest_root_freqs [e] == [freq_of (entry_tree e)]`
- `greedy_cost [f] == 0` (proven: `greedy_cost_singleton`)
- `forest_total_cost [e] == HSpec.cost (entry_tree e)` (proven: `forest_total_cost_singleton`)

Therefore: **`HSpec.cost (final_tree) == HOpt.greedy_cost initial_freqs`**

Combined with `same_frequency_multiset`, we can invoke:
```
HOpt.greedy_cost_implies_optimal : ft:htree -> freqs:list pos{Cons? freqs} ->
  Lemma (requires same_frequency_multiset ft freqs /\ cost ft == greedy_cost freqs)
        (ensures is_wpl_optimal ft freqs)
```

---

## Goal

Strengthen the postcondition of `huffman_tree` to:
```fstar
ensures A.pts_to freqs freq_seq **
        (exists* ft. is_htree result ft **
                pure (HSpec.cost ft == HOpt.greedy_cost (seq_to_pos_list freq_seq 0) /\
                      HSpec.same_frequency_multiset ft (seq_to_pos_list freq_seq 0) /\
                      HSpec.is_wpl_optimal ft (seq_to_pos_list freq_seq 0)))
```

---

## Action Plan

### Phase 0: Assess the working copy (Est: 30 min)

**0.1** Try verifying the working copy as-is with `fstar.exe`.
Use `--admit_except CLRS.Ch16.Huffman.huffman_tree` first to check
that all the new pure lemmas verify, then try the full file.

If the working copy verifies → skip directly to Phase 2.

If it doesn't → proceed to Phase 1.

### Phase 1: Get to a verifying state

**Strategy A: Incremental fix of working copy**

**1.1** If only a few errors, fix them directly. The most likely issues are:
- `SZ.fits n` not available where needed (added to merge_bundle but possibly
  not propagated everywhere)
- `merge_bundle_step` requires clause not matching what's available in the
  Pulse loop body (e.g., `j1 < j2` ordering constraint)
- Missing `reveal_opaque` for newly opaqued definitions
- SMT resource limits too low for the combined proof

**1.2** If many errors or the file is too large to get useful feedback,
fall back to Strategy B.

**Strategy B: Revert working copy, re-introduce changes incrementally**

**1.3** `git stash` the working copy changes.
**1.4** Start from the committed version (with `admit()`).
**1.5** Add the pure helper lemmas first (they don't affect the Pulse code).
      Verify after each batch.
**1.6** Add `merge_bundle_step` and `merge_bundle_intro`.
**1.7** Replace the inline proof + `admit()` in the Pulse loop with
      `merge_bundle_step` call.
**1.8** Verify the full file.

### Phase 2: Strengthen the postcondition

Once the file verifies with zero admits:

**2.1** After the merge loop exits (around line 2971 in working copy),
add proof steps to derive cost equality:
```pulse
// Derive cost equality from merge_bundle's cost invariant
merge_bundle_elim freq_seq nd_final_pre pq_final active_final (SZ.v n);
forest_total_cost_singleton active_final;
forest_root_freqs_singleton active_final;
greedy_cost_singleton (HSpec.freq_of (entry_tree (L.index active_final 0)));
// Now: HSpec.cost (entry_tree (L.index active_final 0))
//      == HOpt.greedy_cost (seq_to_pos_list freq_seq 0)
```

**2.2** Use `greedy_cost_implies_optimal` to derive `is_wpl_optimal`:
```pulse
// Need Cons? (seq_to_pos_list freq_seq 0) — follows from n > 0
seq_to_pos_list_length freq_seq 0;  // if this helper exists
HOpt.greedy_cost_implies_optimal
  (entry_tree (L.index active_final 0))
  (seq_to_pos_list freq_seq 0);
```

**2.3** Update the `ensures` clause to include the stronger properties.

**2.4** Verify the full file.

### Phase 3: Split the file for build efficiency

The file is 3,000+ lines. Verification is slow and wasteful — a change to
any lemma requires re-checking the entire file. Split into modules with
`.fsti` interfaces to enable parallel checking and separation of concerns.

**Proposed module split:**

| New module | Contents | Approx lines |
|------------|----------|-------------:|
| `CLRS.Ch16.Huffman.PQInvariants.fst` | PQ entry helpers: `valid_pq_entries`, `pq_freqs_positive`, `pq_idx_unique`, `pq_indices_in_forest`, all `_extends`/`_shrink` lemmas | ~500 |
| `CLRS.Ch16.Huffman.Forest.fst` | `forest_entry`, `forest_own`, `forest_distinct_indices`, `list_remove_at/two`, `find_entry_by_idx`, `all_leaf_freqs`, `forest_root_freqs`, multiset lemmas | ~800 |
| `CLRS.Ch16.Huffman.TreeOwnership.fst` | `is_htree`, `alloc_hnode`, `alloc_htree`, `free_htree`, `hnode`/`hnode_ptr` defs, `forest_own_take_at/two/put_head` (Pulse ghost fns) | ~400 |
| `CLRS.Ch16.Huffman.CostInvariant.fst` | `forest_total_cost`, `cost_invariant_merge_step`, `cost_invariant_from_merge_bundle`, greedy-cost singleton, merge-step cost, `freq2_le_*` | ~300 |
| `CLRS.Ch16.Huffman.MergeBundle.fst` | `init_bundle`, `merge_bundle`, `init_to_merge_bundle`, `merge_bundle_elim/intro/step`, `pq_tree_freq_match*` | ~400 |
| `CLRS.Ch16.Huffman.fst` | Top-level `huffman_cost`, `huffman_tree` (the Pulse implementations) | ~600 |

**Interface strategy:**
- Each `.fst` gets a `.fsti` exposing only what downstream modules need.
- `MergeBundle.fsti` exports `merge_bundle` (opaque), `merge_bundle_elim`,
  `merge_bundle_intro`, `merge_bundle_step` — the loop body just calls these.
- `Forest.fsti` exports `forest_entry`, `entry_idx/ptr/tree`, list operations.
- `TreeOwnership.fsti` exports `is_htree`, `forest_own`, the ghost Pulse fns.
- The main `Huffman.fst` only needs to call lemmas from the interfaces.

**Benefits:**
- Parallel `.checked` production: `make -j` checks all modules simultaneously.
- Isolation: changing a cost lemma doesn't re-check PQ invariants.
- Faster feedback: each module is ~300-800 lines → seconds, not minutes.

**Execution:**
- **3.1** Create `.fsti` files for each new module (top-down: decide what to export).
- **3.2** Move definitions/lemmas into new `.fst` files.
- **3.3** Update `open`/`module` directives in each file.
- **3.4** Verify each module independently.
- **3.5** Verify the full build with `make`.

### Phase 4: Verify with Makefile

**4.1** Run `make -C ch16-greedy` (or the top-level `make` targeting ch16).
**4.2** Confirm `CLRS.Ch16.Huffman.fst.checked` is produced.
**4.3** Commit with a clear message describing the strengthened postcondition.

---

## Risk Assessment

| Risk | Mitigation |
|------|------------|
| Working copy doesn't verify | Strategy B: revert and re-introduce incrementally |
| `merge_bundle_step` has a subtle precondition mismatch | The lemma takes explicit `j1 j2` but the Pulse code computes them via `find_entry_by_idx`; ensure the ordering `j1 < j2` holds (it does because `pq_idx_unique` ensures `idx1 <> idx2`, and the code orders them) |
| `seq_to_pos_list freq_seq 0` might not satisfy `Cons?` | It does: `n > 0` and all elements `> 0`, so `seq_to_pos_list` returns a non-empty `list pos` |
| File split introduces import cycles | The dependency graph is strictly layered: Forest → PQInvariants → TreeOwnership → CostInvariant → MergeBundle → Huffman.fst |
| SMT instability after split | Opaque bundles and `--split_queries always` already isolate SMT contexts; splitting further should only help |

## Key Insight

The cost invariant is **already maintained** in the working copy's
`merge_bundle` predicate. The only missing piece for the strengthened
postcondition is ~5 lines of proof at the end of `huffman_tree` to
extract the cost equality from the final `merge_bundle` state and invoke
`greedy_cost_implies_optimal`. The hard work (maintaining the cost
invariant through each merge step) is done — we just need to verify
it and thread the result through to the postcondition.
