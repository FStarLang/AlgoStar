# Ch12 BST C Code — Specification Review

## Overview

The C code in `ch12/c/` implements an array-based BST verified with c2pulse.
The Impl.fsti files (`CLRS.Ch12.BSTArray.Impl.fsti`, `CLRS.Ch12.BSTArray.Delete.fsti`)
provide much stronger specifications. This document catalogs the gaps.

The c2pulse representation uses `Int32.t` arrays (`Seq.seq (option Int32.t)`)
while the Impl.fsti uses `Prims.int` and `bool` (`Seq.seq int`, `Seq.seq bool`).
Bridge lemmas must convert between these representations.

---

## Gap Analysis by Function

### 1. BstSearch.c — `bst_search`

**C spec (current):**
- Pre: `keys._length == cap`, `valid._length == cap`, `cap > 0 && cap < 32768`, `i <= cap`
- Post: `return <= cap`, found ⟹ `keys[return] == key && valid[return] != 0`, arrays unchanged

**Impl.fsti (`tree_search`):**
- Pre: `subtree_in_range keys valid cap 0 lo hi` (BST ordering)
- Post:
  - Found ⟹ `keys[idx] == key && valid[idx] == true`
  - **Not found ⟹ `~(key_in_subtree keys valid cap 0 key)`** ← MISSING
  - Ticks bounded by `tree_height(cap)`

**Gaps:**
- [ ] Missing BST ordering precondition (`subtree_in_range` or `well_formed_bst`)
- [ ] Missing completeness postcondition (not found ⟹ key absent from subtree)
- [ ] Missing connection to pure `bst_search` spec

### 2. BstInsert.c — `bst_insert`

**C spec (current):**
- Pre: basic array/bounds
- Post: `return <= cap`, found ⟹ `keys[return] == key && valid[return] != 0`,
  frame: only position `return` changed

**Impl.fsti (`tree_insert`):**
- Pre: `well_formed_bst keys valid cap 0 lo hi`, `lo < key < hi`
- Post:
  - **`well_formed_bst` preserved** ← MISSING
  - **`key_in_subtree keys' valid' cap 0 key`** ← MISSING
  - Exact characterization: `Seq.upd` at empty slot

**Gaps:**
- [ ] Missing `well_formed_bst` precondition
- [ ] Missing `well_formed_bst` preservation postcondition
- [ ] Missing `key_in_subtree` postcondition
- [ ] Missing `lo < key < hi` precondition

### 3. BstMinMax.c — `bst_minimum` / `bst_maximum`

**C spec (current):**
- Pre: basic bounds + **ad-hoc local ordering** (∀j, keys[2j+1] < keys[j])
- Post: `return <= keys[i]` (minimum), `return >= keys[i]` (maximum), arrays unchanged

**Delete.fsti (`tree_minimum` / `tree_maximum`):**
- Pre: basic validity (no explicit ordering precondition — uses `well_formed_bst` from caller)
- Post:
  - Result index is valid
  - **`is_left_spine start result`** (minimum) ← MISSING
  - No valid left child at result position

**Gaps:**
- [ ] Replace ad-hoc local ordering precondition with `well_formed_bst` (or remove — rely on caller)
- [ ] Add `is_left_spine` postcondition for minimum (connects to delete)
- [ ] Current C minimum returns key value, Delete.fsti returns index — different API
  → BstSuccessor.c already has `bst_minimum_idx` returning index; use that pattern
- [ ] Return bounded by root key is weaker than Impl.fsti structural guarantees

### 4. BstSuccessor.c — `bst_successor` / `bst_minimum_idx`

**C spec (current):**
- Pre: basic bounds
- Post: `return <= cap`, found ⟹ `valid[return] != 0`, arrays unchanged

**Delete.fsti (`tree_successor`):**
- Pre: basic validity
- Post: result is valid node (if Some)

**Gaps:**
- [x] Specs are roughly at parity for validity guarantees
- [ ] Missing key ordering guarantee (successor key > current key when BST valid)

### 5. BstPredecessor.c — `bst_predecessor` / `bst_maximum_idx`

**C spec (current):** Same pattern as successor.

**Delete.fsti (`tree_predecessor`):**
- Post: result is valid node (if Some)

**Gaps:**
- [x] Specs are roughly at parity for validity guarantees
- [ ] Missing key ordering guarantee (predecessor key < current key when BST valid)

### 6. BstDelete.c — `bst_delete`

**C spec (current):**
- Pre: basic bounds, `valid[del_idx] != 0`
- Post: failure (return 0) ⟹ arrays unchanged

**Delete.fsti (`tree_delete`):**
- Pre: `well_formed_bst`, node valid
- Post:
  - **`well_formed_bst` preserved** ← MISSING
  - Failure ⟹ arrays unchanged
  - Array lengths preserved

**Gaps:**
- [ ] Missing `well_formed_bst` precondition
- [ ] Missing `well_formed_bst` preservation postcondition
- [ ] No guarantee about what changes on success (key removed?)

### 7. BstDeleteKey.c — `bst_delete_key`

**C spec (current):**
- Pre: basic bounds
- Post: (none beyond what search + delete provide)

**Delete.fsti (`tree_delete_key`):**
- Pre: `well_formed_bst`
- Post: **`well_formed_bst` preserved** ← MISSING, failure ⟹ unchanged

**Gaps:**
- [ ] Missing `well_formed_bst` precondition
- [ ] Missing `well_formed_bst` preservation postcondition

### 8. BstInorderWalk.c — `bst_inorder_walk`

**C spec (current):**
- Pre: basic bounds, `*write_pos <= out_len`
- Post: write_pos stays in bounds, BST arrays unchanged

**Impl.fsti (`inorder_walk`):**
- Post: write_pos stays in bounds, BST arrays unchanged

**Gaps:**
- [x] Specs are roughly at parity (both are relatively weak)
- [ ] Neither proves sorted output — low priority

---

## Implementation Plan

### Phase 1: Bridge Infrastructure
Extend `CLRS.Ch12.BST.C.BridgeLemmas` with:
- `seq_key`: extract `int` from `Seq.seq (option Int32.t)` (like ch11's `seq_val`)
- `seq_vld`: extract `bool` from `Seq.seq (option Int32.t)` (nonzero → true)
- `to_int_seq` / `to_bool_seq`: full sequence conversion
- `c_well_formed_bst`: bridge predicate on option Int32.t sequences
- `c_key_in_subtree`: bridge predicate on option Int32.t sequences
- `c_subtree_in_range`: bridge predicate on option Int32.t sequences
- Equivalence lemmas connecting these to the Predicates module

### Phase 2: Strengthen Search + Insert (highest impact)
- BstSearch.c: add `c_well_formed_bst` pre, completeness post
- BstInsert.c: add `c_well_formed_bst` pre + preservation post

### Phase 3: Strengthen Delete
- BstDelete.c: add `c_well_formed_bst` pre + preservation post
- BstDeleteKey.c: add `c_well_formed_bst` pre + preservation post

### Phase 4: Strengthen MinMax
- BstMinMax.c: replace ad-hoc ordering with `c_well_formed_bst`

### Phase 5: Low-priority improvements
- Successor/Predecessor key ordering
- Inorder walk sorted output
