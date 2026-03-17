# Array-Based BST Spec Validation — ImplTest.md

## Source

New test created for the CLRS Chapter 12 array-based BST.
Methodology from [arXiv:2406.09757](https://arxiv.org/abs/2406.09757).

## Test Description

**File:** `CLRS.Ch12.BSTArray.ImplTest.fst`

The test exercises the array-based BST API on a concrete 7-element instance
(cap=7, 3-level implicit binary tree) with ghost bounds lo=0, hi=100.

### § 1. Pure Spec Validation

| Property | Status |
|----------|--------|
| `well_formed_bst` for empty tree (all valid=false) | ✅ |
| `subtree_in_range` for empty tree | ✅ |
| `~(key_in_subtree)` for empty tree | ✅ |

### § 2. Pulse API Test

| Step | Operation | Expected Result | Proven? |
|------|-----------|-----------------|---------|
| 1 | Create key/valid arrays (7 elements) | Arrays allocated | ✅ |
| 2 | `tree_search t 5 ctr` (empty tree) | `None? r_empty` | ✅ |
| 3 | `tree_insert t 5 ctr` | Insert called | ✅ |
| 4 | `wfb_to_sir` bridge | Establish `subtree_in_range` | ✅ |
| 5 | `tree_search t 5 ctr` (after insert) | `success ==> Some? r_found` | ✅ |
| 6 | `tree_search t 5 ctr` (insert failed) | `not success ==> None? r_found` | ✅ |
| 7 | `tree_search t 99 ctr` (insert failed) | `not success ==> None? r_miss` | ✅ |
| 8 | Free arrays and ghost counter | Cleanup | ✅ |

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

5. **Insert→Search composability (success case)**: When insert succeeds,
   the strengthened postcondition `key_in_subtree keys' valid' cap 0 key`
   contradicts search's `None` postcondition `~(key_in_subtree ...)`,
   proving `Some? r_found`. This demonstrates that the insert and search
   specifications are compositionally precise.

6. **Insert→Search composability (failure case)**: When insert fails,
   arrays are unchanged (all valid=false). Search for any key returns
   `None` because `Some?` would require `valid[idx]==true`, contradicting
   the unchanged all-false valid array.

7. **Bridge composability**: The exported `wfb_to_sir` bridge from
   `Impl.fsti` converts `AP.well_formed_bst` (insert postcondition) to
   `subtree_in_range` (search precondition), enabling insert→search
   composition without client-side bridge lemmas.

### Spec Issues Resolved

#### ~~Issue 2: Insert postcondition too weak — no reachability guarantee~~ (RESOLVED)

**Previously**: After insert, the postcondition said
`∃ idx. keys'[idx] == key ∧ valid'[idx] == true`. This was weaker than
`key_in_subtree keys' valid' cap 0 key` (reachability from root via BST
path). Without reachability, search after insert couldn't be proven to find
the inserted key.

**Fix applied**: The insert postcondition now includes
`success ==> key_in_subtree keys_seq' valid_seq' (SZ.v t.cap) 0 key`.
This is proven by `lemma_insert_key_reachable`, which shows that writing a
key at a position reached by BST search makes it reachable from the root.

**Impact**: Can now prove `success ==> Some? (tree_search t key)` after a
successful insert. The test demonstrates this.

#### ~~Issue 3: Duplicated `subtree_in_range` definition~~ (RESOLVED)

**Previously**: `subtree_in_range` was defined in both `Impl.fsti` and
`Predicates.fst`. Clients needed to write a bridge lemma (`sir_bridge`) to
compose insert (postcondition uses `AP.well_formed_bst`) with search
(precondition uses local `subtree_in_range`).

**Fix applied**: `Impl.fsti` now exports `wfb_to_sir`, a bridge function
that converts `AP.well_formed_bst` to local `subtree_in_range`. Clients
can use this directly without defining their own bridge.

**Impact**: The test no longer needs client-side bridge lemmas. The
`wfb_to_sir` call cleanly chains insert → search.

### Remaining Spec Issues

#### Issue 1: Insert postcondition doesn't guarantee success

The `tree_insert` postcondition does not guarantee `success == true` even
when the tree has empty slots. The postcondition only says:
- IF success: key is placed and reachable (`key_in_subtree`)
- IF NOT success: arrays unchanged

Both outcomes are consistent with the postcondition for an empty tree.

**Impact**: Cannot prove that inserting into a non-full tree always succeeds.
The test handles both cases conditionally.

**Potential fix**: Add a precondition/postcondition connecting success to
available capacity, e.g.:
```
(~key_in_subtree keys valid cap 0 key /\ has_empty_slot ==> success)
```

#### Issue 4: No frame property for insert

When insert succeeds, the postcondition says `∃ idx. keys'[idx] == key ∧
valid'[idx] == true` but does not constrain OTHER positions. A frame
property like `keys' == Seq.upd keys idx key ∧ valid' == Seq.upd valid idx
true` would enable proving absent keys remain absent after insert (e.g.,
`success ==> None? (tree_search t 99)`).

**Impact**: Cannot prove `None?` for absent keys in the success case.

### Comparison with Pointer-Based BST

| Property | Pointer BST | Array BST |
|----------|-------------|-----------|
| Insert postcondition | `bst_subtree y (bst_insert 'ft k) parent` — exact tree shape | `key_in_subtree` + `∃ idx. keys'[idx]==key` — reachable but existential |
| Search composability | Direct: ghost tree determines search result | ✅ Fixed: `key_in_subtree` enables insert→search chaining |
| Insert success guarantee | Always succeeds (tree grows dynamically) | Not guaranteed (fixed capacity, postcondition too weak) |
| Predicate consistency | Single `bst_subtree` predicate | ✅ Fixed: `wfb_to_sir` bridge exported from Impl |

### Verification

- **Admits**: 0
- **Assumes**: 0
- **Solver options**: `--z3rlimit 80 --fuel 8 --ifuel 4`
