# Array-Based BST Spec Validation — ImplTest.md

## Source

New test created for the CLRS Chapter 12 array-based BST.
Methodology from [arXiv:2406.09757](https://arxiv.org/abs/2406.09757).

## Test Description

**File:** `CLRS.Ch12.BSTArray.ImplTest.fst`

The test exercises the array-based BST API on a concrete 7-element instance
(cap=7, 3-level implicit binary tree) with ghost bounds lo=0, hi=100.

### § 1. Bridge Lemma

The test includes a bridge lemma `sir_bridge` that proves:

```
AP.subtree_in_range keys valid cap i lo hi
==> Impl.subtree_in_range keys valid cap i lo hi
```

This is necessary because `tree_insert`'s postcondition uses
`AP.well_formed_bst` (from the Predicates module), while `tree_search`'s
precondition uses `Impl.subtree_in_range` (duplicated in the Impl.fsti for
Pulse compatibility). The two `subtree_in_range` definitions are
syntactically identical but in different modules. The bridge lemma
(via `wfb_to_sir`) converts between them.

**This is a spec gap**: the Impl.fsti API should either:
- Use a single `subtree_in_range` definition (from Predicates), or
- Export a bridge lemma, or
- Use `well_formed_bst` consistently in both search and insert preconditions

### § 2. Pure Spec Validation

| Property | Status |
|----------|--------|
| `well_formed_bst` for empty tree (all valid=false) | ✅ |
| `subtree_in_range` for empty tree | ✅ |
| `~(key_in_subtree)` for empty tree | ✅ |

### § 3. Pulse API Test

| Step | Operation | Expected Result | Proven? |
|------|-----------|-----------------|---------|
| 1 | Create key/valid arrays (7 elements) | Arrays allocated | ✅ |
| 2 | `tree_search t 5 ctr` (empty tree) | `None? r_empty` | ✅ |
| 3 | `tree_insert t 5 ctr` | Insert called | ✅ |
| 4 | `wfb_to_sir` bridge | Establish `subtree_in_range` | ✅ |
| 5 | `tree_search t 5 ctr` (after insert) | `Some? r_found`? | ❌ (see below) |
| 6 | `tree_search t 99 ctr` (absent key) | `None? r_miss`? | ❌ (see below) |
| 7 | Free arrays and ghost counter | Cleanup | ✅ |

### What Is Proven

1. **Search precondition satisfiability on empty tree**: `tree_search` can
   be called on an empty BST array. The `subtree_in_range` predicate holds
   trivially when `valid[0] == false`.

2. **Search postcondition precision on empty tree**: Searching an empty tree
   returns `None`, and the postcondition `~(key_in_subtree ...)` confirms
   the key is truly absent. Verified for key 5.

3. **Insert precondition satisfiability**: `tree_insert` can be called on
   an empty BST array with bounds lo=0, hi=100 and key=5.

4. **Insert preserves well_formed_bst**: The postcondition
   `AP.well_formed_bst keys' valid' cap 0 lo hi` is guaranteed.

5. **Search-after-insert precondition satisfiability**: Using the bridge
   lemma `wfb_to_sir`, the `subtree_in_range` precondition of `tree_search`
   can be established from the `well_formed_bst` postcondition of
   `tree_insert`. This proves the operations are composable.

### Spec Issues Found

#### Issue 1: Insert postcondition too weak — cannot prove success

The `tree_insert` postcondition does not guarantee `success == true` even
when the tree has empty slots. The postcondition only says:
- IF success: `∃ idx. keys'[idx] == key ∧ valid'[idx] == true`
- IF NOT success: arrays unchanged

Both outcomes are consistent with the postcondition for an empty tree.

**Impact**: Cannot prove that inserting into a non-full tree always succeeds.

**Fix**: Add a precondition/postcondition connecting success to available capacity:
```
(success == true <==> ~(subtree_all_valid valid_seq cap 0))
```
or at minimum guarantee:
```
(~(key_in_subtree keys_seq valid_seq cap 0 key) /\ has_empty_slot ==> success)
```

#### Issue 2: Insert postcondition too weak — no reachability guarantee

After insert, the postcondition says `∃ idx. keys'[idx] == key ∧ valid'[idx] == true`.
This is weaker than `key_in_subtree keys' valid' cap 0 key` (reachability from
root via BST path). Without a reachability guarantee, subsequent `tree_search`
cannot be proven to find the inserted key.

**Impact**: Cannot chain insert → search and prove the search succeeds.

**Fix**: Strengthen the insert postcondition to:
```
(success ==> key_in_subtree keys_seq' valid_seq' cap 0 key)
```
This would allow proving `Some? (tree_search t key)` after a successful insert.

#### Issue 3: Duplicated `subtree_in_range` definition

The `subtree_in_range` predicate is defined in both `Impl.fsti` and
`Predicates.fst` with identical bodies but as separate recursive functions.
This creates a bridging burden for clients who need to chain operations
(insert gives `AP.well_formed_bst`, search needs `Impl.subtree_in_range`).

**Impact**: Clients must prove a bridge lemma (`sir_bridge`) to compose
search and insert operations.

**Fix**: Either use a single definition (import from Predicates) or export
a bridge lemma from the Impl module.

### Comparison with Pointer-Based BST

The pointer-based BST (`CLRS.Ch12.BST.Impl.fsti`) has none of these issues:

| Property | Pointer BST | Array BST |
|----------|-------------|-----------|
| Insert postcondition | `bst_subtree y (bst_insert 'ft k) parent` — exact tree shape | `∃ idx. keys'[idx]==key` — existential |
| Search composability | Direct: ghost tree determines search result | Broken: insert → search requires unproven reachability |
| Insert success guarantee | Always succeeds (tree grows dynamically) | Not guaranteed (fixed capacity, postcondition too weak) |
| Predicate consistency | Single `bst_subtree` predicate | Duplicated `subtree_in_range` |

### Verification

- **Admits**: 0
- **Assumes**: 0
- **Solver options**: `--z3rlimit 80 --fuel 8 --ifuel 4`
