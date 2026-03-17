# Pointer-Based BST Spec Validation — ImplTest.md

## Source

New test created for the CLRS Chapter 12 pointer-based BST.
Methodology from [arXiv:2406.09757](https://arxiv.org/abs/2406.09757).
Test pattern adapted from
[Test.DLL.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.DLL.fst)
and existing `ImplTest.fst` files in the AutoCLRS repository.

## Test Description

**File:** `CLRS.Ch12.BST.ImplTest.fst`

The test exercises both pure specification functions and the Pulse API on a
concrete 3-element BST instance: insert keys {2, 1, 3} into an empty tree.

### § 1. Pure Spec Validation

Verifies, via `assert_norm`, that all pure specification functions compute
the expected results for concrete inputs:

| Property | Assertion | Status |
|----------|-----------|--------|
| Tree shape after insert 2 | `t1 == Node Leaf 2 Leaf` | ✅ |
| Tree shape after insert 1 | `t2 == Node (Node Leaf 1 Leaf) 2 Leaf` | ✅ |
| Tree shape after insert 3 | `t3 == Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)` | ✅ |
| Validity at each step | `bst_valid t0..t3 == true` | ✅ |
| Search finds key 1 | `bst_search t3 1 == true` | ✅ |
| Search finds key 2 | `bst_search t3 2 == true` | ✅ |
| Search finds key 3 | `bst_search t3 3 == true` | ✅ |
| Search misses key 0 | `bst_search t3 0 == false` | ✅ |
| Search misses key 4 | `bst_search t3 4 == false` | ✅ |
| Minimum is 1 | `bst_minimum t3 == Some 1` | ✅ |
| Maximum is 3 | `bst_maximum t3 == Some 3` | ✅ |
| Delete key 2 shape | `t4 == Node (Node Leaf 1 Leaf) 3 Leaf` | ✅ |
| Validity after delete | `bst_valid t4 == true` | ✅ |
| Search after delete | `bst_search t4 2 == false`, 1 and 3 still true | ✅ |
| Delete all → Leaf | `bst_delete (bst_delete t4 1) 3 == Leaf` | ✅ |
| Duplicate insert is no-op | `bst_insert t3 2 == t3` | ✅ |

### § 2. Pulse API Test

Exercises all six operations from `CLRS.Ch12.BST.Impl.fsti`:

| Step | Operation | Expected Result | Proven? |
|------|-----------|-----------------|---------|
| 1 | `fold (bst_subtree empty Leaf parent)` | Empty tree | ✅ |
| 2 | `tree_insert empty 2 parent ticks` | Insert key 2 | ✅ |
| 3 | `tree_insert r1 1 parent ticks` | Insert key 1 | ✅ |
| 4 | `tree_insert r2 3 parent ticks` | Insert key 3 | ✅ |
| 5 | `tree_search r3 1 ticks` | `true` | ✅ |
| 6 | `tree_search r3 2 ticks` | `true` | ✅ |
| 7 | `tree_search r3 3 ticks` | `true` | ✅ |
| 8 | `tree_search r3 0 ticks` | `false` | ✅ |
| 9 | `tree_search r3 4 ticks` | `false` | ✅ |
| 10 | `tree_minimum (Some bp) bp ticks` | `1` | ✅ |
| 11 | `tree_maximum (Some bp) bp ticks` | `3` | ✅ |
| 12 | `tree_delete (Some bp) 2 parent ticks` | Delete key 2 | ✅ |
| 13 | `tree_search r4 2 ticks` (after delete) | `false` | ✅ |
| 14 | `tree_search r4 1 ticks` | `true` | ✅ |
| 15 | `tree_search r4 3 ticks` | `true` | ✅ |
| 16 | `tree_minimum (Some bp4) bp4 ticks` | `1` | ✅ |
| 17 | `tree_maximum (Some bp4) bp4 ticks` | `3` | ✅ |
| 18 | `free_bst (Some bp4)` | Deallocate tree | ✅ |

### What Is Proven

1. **Precondition satisfiability**: All six operations (`tree_insert`,
   `tree_search`, `tree_minimum`, `tree_maximum`, `tree_delete`, `free_bst`)
   are successfully called with valid preconditions.

2. **Insert postcondition precision**: The ghost tree after insert is
   `bst_insert 'ft k`, which for concrete inputs computes to the exact
   tree shape. Combined with `bst_valid 'ft ==> bst_valid (bst_insert 'ft k)`,
   this is the strongest possible postcondition.

3. **Search postcondition precision**: `result == bst_search 'ft k` uniquely
   determines the search result for any concrete ghost tree. Verified for
   3 present keys and 2 absent keys.

4. **Minimum/Maximum postcondition precision**: `bst_minimum 'ft == Some result`
   and `bst_maximum 'ft == Some result` uniquely determine the return value.
   Verified for both the 3-element and 2-element trees.

5. **Delete postcondition precision**: The ghost tree after delete is
   `bst_delete 'ft k`, which computes to the expected shape. Verified by
   subsequent search, minimum, and maximum calls.

6. **Round-trip correctness**: Insert 3 keys, delete 1, verify remaining
   keys, free entire tree. Full lifecycle exercised.

### Auxiliary Lemmas

Helper lemmas wrap `assert_norm` to pre-compute pure spec results, bridging
the gap between F*'s normalization and Pulse's SMT-based assertion checking.
This is a standard pattern used in the ch13 RBTree ImplTest.

### Spec Issues Found

**None.** The pointer-based BST specification is precise and complete:
- All postconditions uniquely determine outputs for concrete inputs
- The ghost tree tracks exact tree shapes through insert and delete
- Validity preservation is included in the postconditions
- All operations compose cleanly (insert → search → delete → search)

### Verification

- **Admits**: 0
- **Assumes**: 0
- **Solver options**: `--z3rlimit 80 --fuel 8 --ifuel 4`
