# Array-Based Binary Search Tree (CLRS §12.1–12.3)

## Top-Level Signatures

Here are the top-level signatures proven about the array-backed BST in
`CLRS.Ch12.BSTArray.Impl.fsti`:

### `tree_search`

```fstar
fn tree_search
  (#p: perm)
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (#lo: Ghost.erased int)
  (#hi: Ghost.erased int)
  (key: int)
  (ticks: GR.ref nat)
  requires
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    GR.pts_to ticks 'n **
    pure (
      Seq.length keys_seq == A.length t.keys /\
      Seq.length valid_seq == A.length t.valid /\
      A.length t.keys == A.length t.valid /\
      SZ.v t.cap <= A.length t.keys /\
      SZ.v t.cap < 32768 /\
      subtree_in_range keys_seq valid_seq (SZ.v t.cap) 0 lo hi
    )
  returns result: option SZ.t
  ensures exists* vticks.
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    GR.pts_to ticks vticks **
    pure (
      vticks >= 'n /\
      (SZ.v t.cap > 0 ==> vticks - 'n <= tree_height (SZ.v t.cap)) /\
      (Some? result ==> (
        SZ.v (Some?.v result) < Seq.length keys_seq /\
        SZ.v (Some?.v result) < Seq.length valid_seq /\
        Seq.index valid_seq (SZ.v (Some?.v result)) == true /\
        Seq.index keys_seq (SZ.v (Some?.v result)) == key)) /\
      (None? result ==> ~(key_in_subtree keys_seq valid_seq (SZ.v t.cap) 0 key))
    )
```

### `tree_insert`

```fstar
fn tree_insert
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (key: int)
  (#lo: Ghost.erased int)
  (#hi: Ghost.erased int)
  (ticks: GR.ref nat)
  requires
    A.pts_to t.keys keys_seq **
    A.pts_to t.valid valid_seq **
    GR.pts_to ticks 'n **
    pure (
      Seq.length keys_seq == A.length t.keys /\
      Seq.length valid_seq == A.length t.valid /\
      A.length t.keys == A.length t.valid /\
      SZ.v t.cap <= A.length t.keys /\
      SZ.v t.cap < 32768 /\
      AP.well_formed_bst keys_seq valid_seq (SZ.v t.cap) 0 (Ghost.reveal lo) (Ghost.reveal hi) /\
      Ghost.reveal lo < key /\ key < Ghost.reveal hi
    )
  returns success: bool
  ensures exists* keys_seq' valid_seq' vticks.
    A.pts_to t.keys keys_seq' **
    A.pts_to t.valid valid_seq' **
    GR.pts_to ticks vticks **
    pure (
      vticks >= 'n /\
      (SZ.v t.cap > 0 ==> vticks - 'n <= tree_height (SZ.v t.cap)) /\
      Seq.length keys_seq' == Seq.length keys_seq /\
      Seq.length valid_seq' == Seq.length valid_seq /\
      (not success ==> Seq.equal keys_seq' keys_seq /\
                       Seq.equal valid_seq' valid_seq) /\
      (success ==> (exists (idx: nat). idx < SZ.v t.cap /\
                    idx < Seq.length keys_seq' /\
                    idx < Seq.length valid_seq' /\
                    Seq.index keys_seq' idx == key /\
                    Seq.index valid_seq' idx == true)) /\
      AP.well_formed_bst keys_seq' valid_seq' (SZ.v t.cap) 0 (Ghost.reveal lo) (Ghost.reveal hi)
    )
```

### `inorder_walk`

```fstar
fn inorder_walk
  (#p: perm)
  (t: bst)
  (#keys_seq: Ghost.erased (Seq.seq int))
  (#valid_seq: Ghost.erased (Seq.seq bool))
  (output: A.array int)
  (#out_seq: Ghost.erased (Seq.seq int))
  (write_pos: R.ref SZ.t)
  (#wp0: Ghost.erased SZ.t)
  (out_len: SZ.t)
  requires
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    A.pts_to output out_seq **
    R.pts_to write_pos wp0 **
    pure (...)
  ensures
    A.pts_to t.keys #p keys_seq **
    A.pts_to t.valid #p valid_seq **
    (exists* out_seq' wp'.
      A.pts_to output out_seq' **
      R.pts_to write_pos wp' **
      pure (
        Seq.length out_seq' == A.length output /\
        SZ.v wp' <= SZ.v out_len
      ))
```

### Parameters

* `t` is a record `{ keys: A.array int; valid: A.array bool; cap: SZ.t }`. Node
  at index `i` has left child at `2*i+1` and right child at `2*i+2`. The
  `valid` array tracks which positions contain nodes.

* `keys_seq`, `valid_seq` are ghost snapshots of the array contents.

* `lo`, `hi` are ghost bounds for the BST ordering invariant.

* `ticks` is a **ghost counter** for complexity measurement.

### BST Type

```fstar
noeq
type bst = {
  keys: A.array int;
  valid: A.array bool;
  cap: SZ.t;
}
```

### Preconditions

* `SZ.v t.cap < 32768`: Capacity is bounded to ensure child indices fit in
  `SZ.t` (since `2*i+2 < 2*cap < 65536 = pow2 16`).

* `subtree_in_range keys_seq valid_seq (SZ.v t.cap) 0 lo hi` (search) or
  `well_formed_bst ...` (insert): BST ordering invariant holds.

### Postconditions

**Search**:
* On found (`Some idx`): `keys[idx] == key` and `valid[idx] == true`.
* On not found (`None`): `~(key_in_subtree keys valid cap 0 key)` — key truly
  absent from the tree.
* Complexity: `vticks - 'n ≤ tree_height(cap)`.

**Insert**:
* On success: There exists an index where `keys'[idx] == key` and
  `valid'[idx] == true`.
* On failure: Arrays unchanged (tree is full).
* `well_formed_bst` preserved in both cases.
* Complexity: `vticks - 'n ≤ tree_height(cap)`.

**Inorder walk**: Write position is bounded; tree arrays unchanged (read-only
via fractional permission `#p`).

## Auxiliary Definitions

### `subtree_in_range` (from `CLRS.Ch12.BSTArray.Predicates`)

```fstar
let rec subtree_in_range
  (keys: Seq.seq int) (valid: Seq.seq bool) (cap: nat) (i: nat) (lo hi: int)
  : Tot prop (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= Seq.length keys || i >= Seq.length valid then True
    else if not (Seq.index valid i) then True
    else
      let k = Seq.index keys i in
      let left = op_Multiply 2 i + 1 in
      let right = op_Multiply 2 i + 2 in
      lo < k /\ k < hi /\
      subtree_in_range keys valid cap left lo k /\
      subtree_in_range keys valid cap right k hi
```

Recursive BST ordering: each valid node's key is within `(lo, hi)`, and children
narrow the bounds.

### `well_formed_bst` (from `CLRS.Ch12.BSTArray.Predicates`)

```fstar
let rec well_formed_bst
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat) (lo hi: int)
  : Tot prop (decreases (if i < cap then cap - i else 0))
  = if i >= cap || i >= length keys || i >= length valid then True
    else if not (index valid i) then subtree_all_invalid valid cap i
    else
      let k = index keys i in
      let left = 2 * i + 1 in
      let right = 2 * i + 2 in
      lo < k /\ k < hi /\
      well_formed_bst keys valid cap left lo k /\
      well_formed_bst keys valid cap right k hi
```

Stronger than `subtree_in_range`: additionally requires that no valid nodes
appear below an invalid node (`subtree_all_invalid`). This structural invariant
is needed by insert to prove that writing a key at an empty slot does not
corrupt existing subtrees.

### `key_in_subtree` (from `CLRS.Ch12.BSTArray.Predicates`)

```fstar
let rec key_in_subtree
  (keys: seq int) (valid: seq bool) (cap: nat) (i: nat) (key: int)
  : Tot prop (decreases (if i < cap then cap - i else 0))
  = i < cap /\ i < length keys /\ i < length valid /\
    index valid i /\
    (index keys i == key \/
     key_in_subtree keys valid cap (2 * i + 1) key \/
     key_in_subtree keys valid cap (2 * i + 2) key)
```

### `tree_height` (from `CLRS.Ch12.BSTArray.Complexity`)

```fstar
let tree_height (cap:nat{cap > 0}) : nat =
  log2_floor cap
```

Height of the implicit binary tree is `⌊log₂(cap)⌋`, since node at index `i`
has depth `⌊log₂(i+1)⌋`.

## What Is Proven

### Functional Correctness

* **Search soundness** (`pure_search_sound`): If search returns `Some idx`, then
  `keys[idx] == key` and `valid[idx] == true`.

* **Search completeness** (`pure_search_complete`): If search returns `None`
  under `subtree_in_range`, then `~(key_in_subtree ... key)`.

* **Insert soundness** (`pure_insert_sound`): If insert returns `Some idx`,
  then `idx` is an empty slot (`valid[idx] == false`).

* **Insert preserves existing keys** (`pure_insert_complete`): Existing
  `key_in_subtree` memberships are preserved after insertion.

* **Insert preserves `well_formed_bst`** (`lemma_insert_wfb`): Writing a key at
  a position reachable by BST search preserves the structural invariant.

### Refinement (in `CLRS.Ch12.BSTArray.Refinement` and `CLRS.Ch12.BSTArray.Lemmas`)

* **Abstraction function** `array_to_bst`: Maps the array representation to the
  inductive `bst` type from `CLRS.Ch12.BST.Spec`.

* `well_formed_bst ⟹ bst_valid(array_to_bst(...))` — Array invariant implies
  inductive BST validity.

* `key_in_subtree ⟺ bst_search(array_to_bst(...))` — Array membership
  corresponds to inductive search.

* Inorder traversal on arrays matches `bst_inorder` on the abstraction.

### Complexity (in `CLRS.Ch12.BSTArray.Complexity`)

* `node_depth i ≤ tree_height cap` for all `i < cap`.
* `tree_height cap = log2_floor cap`.
* `log2_floor` is bounded and monotone.
* Search/insert path length is `O(h) = O(log cap)`.

**Zero admits, zero assumes** in the Pulse implementation and spec modules.

## Specification Gaps and Limitations

1. **~~Delete is incomplete.~~** *(Partially addressed.)* `tree_delete` now
   handles the **two-children case** using the CLRS successor key-swap
   approach: find the successor (minimum of right subtree via `tree_minimum`),
   copy its key to the deleted position, and mark the successor as invalid.
   This is proven to preserve `well_formed_bst` when the successor is a leaf
   (no valid children). The postcondition is strengthened from conditional to
   unconditional: `well_formed_bst` is ALWAYS preserved on the result arrays,
   whether the deletion succeeds or not. When the successor has a right child,
   or when the node has only a left child, the function returns `false` (tree
   unchanged) rather than orphaning subtrees. Supporting lemmas:
   `lemma_successor_swap_delete_wfb`, `lemma_delete_min_narrow_wfb`,
   `is_left_spine`, and several bound-widening/framing lemmas.

2. **Capacity must be < 32768.** The `cap < 32768` precondition ensures child
   indices (`2*i+2`) fit in `pow2 16`. This is an implementation artifact of
   using `SZ.t` arithmetic, not a fundamental limitation.

3. **Fixed capacity, no resizing.** Insert returns `false` when the implicit
   tree is full (all `cap` positions occupied). No dynamic resizing is provided.

4. **Inorder walk has weak postcondition.** The postcondition only asserts the
   write position is bounded; it does not state that the output array contains
   the inorder traversal. The functional correctness of the walk is not linked
   to the pure `bst_inorder` specification.

5. **No complexity for delete.** The `tree_delete` operation does not take a
   ghost tick counter and has no complexity bound.

6. **Ghost bounds `lo`/`hi` must be provided.** The BST ordering is parameterized
   by ghost bounds, meaning callers must track and supply these. In practice,
   `lo = min_int` and `hi = max_int` at the root, but the implementation uses
   unbounded `int` with no default bounds.

7. **Height is O(log cap), not O(log n).** The complexity bound uses `cap` (total
   array capacity), not the number of valid nodes `n`. For a sparse tree with
   few valid nodes in a large array, the bound is loose.

8. **Left-child-only deletion not handled.** When the node has only a left child
   (no right child), `tree_delete` returns `false` without modifying the tree.
   A predecessor-based key-swap (symmetric to the successor approach) would
   handle this case but requires analogous lemmas.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Search | O(log cap) = log2_floor(cap) | ✅ Ghost ticks | Upper bound |
| Insert | O(log cap) = log2_floor(cap) | ✅ Ghost ticks | Upper bound |
| Delete | — | ❌ No counter | — |
| Inorder | — | ❌ No counter | — |

## Proof Structure

The proof is organized in layers:

1. **Predicates** (`CLRS.Ch12.BSTArray.Predicates`): Defines `subtree_in_range`,
   `well_formed_bst`, `key_in_subtree`, `subtree_all_invalid`, and the
   descendant relation `is_desc_of`. Contains frame lemmas for array updates
   (both positional and descendant-based).

2. **Pure spec** (`CLRS.Ch12.BSTArray.Spec`): Defines `pure_search` and
   `pure_insert` as recursive functions on the array representation. Proves
   soundness and completeness for both.

3. **Refinement** (`CLRS.Ch12.BSTArray.Refinement`): Defines `array_to_bst` and
   proves the array representation faithfully refines the inductive BST.

4. **Complexity** (`CLRS.Ch12.BSTArray.Complexity`): Defines `log2_floor`,
   `tree_height`, `node_depth` and proves depth bounds.

5. **Pulse implementation** (`CLRS.Ch12.BSTArray.Impl.fst`): Iterative Pulse
   implementations using while loops. Insert uses `bst_search_reaches` to
   track the BST path and `lemma_insert_wfb` to maintain the invariant.

6. **Delete** (`CLRS.Ch12.BSTArray.Delete.fst`): Separate module with minimum,
   maximum, successor, predecessor (all fully verified), and a partially
   complete delete.

## Profiling and Proof Stability

### Solver Settings

| File | Max rlimit | Fuel | # push-options | Notes |
|------|-----------|------|----------------|-------|
| `BSTArray.Predicates.fst` | **80** | 2/1 | 18 | Stabilized (was 300/3/2) |
| `BSTArray.Refinement.fst` | 40 | 2/1 | 1 | Stable |
| `BSTArray.Impl.fst` | default | default | 0 | Stable |
| `BSTArray.Delete.fst` | default | default | 0 | Stable |
| `BSTArray.Spec.fst` | default | default | 0 | Stable |
| `BSTArray.Complexity.fst` | default | default | 0 | Stable |
| `BSTArray.Lemmas.fst` | default | default | 0 | Thin re-export |

### Cache File Sizes (proxy for proof complexity)

| File | .checked size | Notes |
|------|--------------|-------|
| `BSTArray.Predicates.fst` | **826 KB** | ⚠️ Largest in ch12; 933 LOC, 18 push-options |
| `BSTArray.Impl.fst` | 555 KB | Moderate (680 LOC) |
| `BSTArray.Delete.fst` | 263 KB | Moderate (786 LOC) |
| `BSTArray.Refinement.fst` | 200 KB | Clean |
| `BSTArray.Spec.fst` | 196 KB | Clean |
| `BSTArray.Impl.fsti` | 174 KB | Interface |

### Assessment

**Overall stability: GOOD.** After stabilization, the maximum rlimit is 80
(previously 300), and all proofs use fuel 2 / ifuel 1 (previously fuel 3 /
ifuel 2 for the hotspot). The `lemma_successor_swap_delete_wfb` proof was
reduced from `--z3rlimit 300 --fuel 3 --ifuel 2` to
`--z3rlimit 80 --fuel 2 --ifuel 1` — a 3.75× rlimit reduction and fuel
reduction from 3 to 2. All other modules use default or low settings.
All 20 modules verify with zero errors on a clean build.

## Files

| File | LOC | Role |
|------|-----|------|
| `CLRS.Ch12.BSTArray.Impl.fsti` | 211 | Public interface (types, predicates, signatures) |
| `CLRS.Ch12.BSTArray.Impl.fst` | 679 | Pulse implementation (search, insert, inorder) |
| `CLRS.Ch12.BSTArray.Spec.fst` | 344 | Pure search/insert functions + soundness/completeness proofs |
| `CLRS.Ch12.BSTArray.Predicates.fst` | 933 | Shared predicates, frame lemmas, descendant relation |
| `CLRS.Ch12.BSTArray.Refinement.fst` | 249 | Abstraction function + refinement proofs |
| `CLRS.Ch12.BSTArray.Complexity.fsti` | 76 | Complexity definitions + lemma signatures |
| `CLRS.Ch12.BSTArray.Complexity.fst` | 97 | Complexity proofs |
| `CLRS.Ch12.BSTArray.Lemmas.fsti` | 47 | Unified lemma interface |
| `CLRS.Ch12.BSTArray.Lemmas.fst` | 83 | Lemma proofs (delegates to Refinement) |
| `CLRS.Ch12.BSTArray.Delete.fst` | 786 | Delete + min/max/successor/predecessor |

## Checklist (Priority Order)

Items to address for a fully proven, high-quality implementation:

- [x] **P0: Zero admits/assumes.** All modules fully verified.
- [x] **P0: Rubric compliance.** All required files present (Spec, Lemmas,
  Lemmas.fsti, Complexity, Complexity.fsti, Impl, Impl.fsti).
- [x] **P0: Search/insert functional correctness.** Soundness, completeness,
  and `well_formed_bst` preservation all proven.
- [x] **P0: Refinement bridge.** `array_to_bst` connects array representation
  to pure inductive BST. Validity, search, and inorder all refined.
- [x] **P0: Complexity linked for search/insert.** Ghost tick counters with
  O(log cap) bounds.
- [x] **P0: Spec validation test.** `CLRS.Ch12.BSTArray.ImplTest.fst` tests
  search (empty tree), insert, and search-after-insert chaining. Finds three
  spec gaps (see below). Zero admits, zero assumes.
- [ ] **P0: Strengthen insert postcondition.** *(Spec gap found by ImplTest.)*
  Insert postcondition should include `key_in_subtree` reachability guarantee
  and `success == true` when tree has capacity. Currently, neither is provable
  from the postcondition. See `CLRS.Ch12.BSTArray.ImplTest.md` for details.
- [ ] **P0: Unify subtree_in_range definitions.** *(Spec gap found by ImplTest.)*
  `subtree_in_range` is duplicated in `Impl.fsti` and `Predicates.fst`. Clients
  need a bridge lemma to compose insert → search. Should use a single definition
  or export a bridge.
- [ ] **P1: Complete delete for all cases.** Left-child-only deletion and
  successor-with-right-child cases currently return `false`. Needs
  predecessor-swap infrastructure (symmetric to successor approach) and
  recursive successor deletion.
- [x] **P1: Stabilize Predicates.fst high-rlimit proof.** *(Addressed.)* The
  `lemma_successor_swap_delete_wfb` proof reduced from rlimit 300 / fuel 3 /
  ifuel 2 to rlimit 80 / fuel 2 / ifuel 1. All other rlimit 80 blocks
  reduced to 20. Max rlimit across all of ch12 is now 100 (in BST.Delete.Spec
  and BST.Insert.Spec, inherent to FiniteSet library).
- [ ] **P1: Strengthen inorder walk postcondition.** Currently only bounds
  write position; should link output to `bst_inorder` via refinement.
- [ ] **P2: Add ghost ticks to delete.** `tree_delete` in `Delete.fst` has
  no complexity counter. Should track ticks bounded by `tree_height(cap)`.
- [ ] **P2: Add ghost ticks to min/max/successor/predecessor.** These
  operations in `Delete.fst` have no complexity counters.
- [ ] **P3: Remove 32768 capacity limitation.** Use larger integer type or
  parameterize by bit width.
- [ ] **P3: Complexity in terms of n, not cap.** Current bounds use
  `log2_floor(cap)` which is loose for sparse trees.
