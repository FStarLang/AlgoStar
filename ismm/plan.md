# Plan: Verified Pulse Implementation of "Reference Counting Deeply Immutable Data Structures with Cycles"

## Paper Reference
**"Reference Counting Deeply Immutable Data Structures with Cycles: An Intellectual Abstract"**
Parkinson, Clebsch, Wrigstad — ISMM '24, DOI: 10.1145/3652024.3665507

## Problem Statement
Implement and formally verify (in Pulse/F*) the paper's algorithm for managing memory of deeply immutable, possibly cyclic data structures using reference counting at the level of strongly connected components (SCCs). The algorithm combines union-find with a path-based SCC algorithm (Purdom's), enabling cycle-safe, prompt, deterministic memory reclamation without a backup garbage collector.

## Algorithm Summary

### Node Status (4 states, stored in a single `status` field per node):
- `UNMARKED` — not yet visited by freeze
- `RANK(n)` — on the pending stack during freeze; part of tentative SCC with rank `n`
- `REP(ptr)` — part of a completed SCC; representative reachable via `ptr` (union-find parent)
- `RC(n)` — SCC representative with external reference count `n`

### Three Core Operations:
1. **`freeze(root)`** — DFS over reachable graph; computes SCCs via Purdom's path-based algorithm fused with union-find; assigns each SCC an initial external reference count.
2. **`dispose(root)`** — Deallocates all nodes in an SCC whose RC hit 0; cascades decrements to child SCCs, potentially triggering their disposal too.
3. **`acquire(r)` / `release(r)`** — Increment/decrement the SCC-level reference count (via `find`); release triggers `dispose` when RC reaches 0.

### Complexity: O(|E| · α(|N|)) for freeze and dispose (almost linear).

## Approach
Build this bottom-up in Pulse, following the project's existing Spec → Impl → Lemmas pattern (see `autoclrs/` for examples). Place all code in `ismm/`.

## Reusable Code from autoclrs/

| Component | Source | How to Reuse |
|-----------|--------|--------------|
| **Union-Find spec** | `autoclrs/ch21-disjoint-sets/CLRS.Ch21.UnionFind.Spec.fst` | Adapt `uf_forest`, `pure_find`, `pure_union`, `rank_invariant`. The paper extends UF with two extra states (UNMARKED, RC), so we define a new 4-state status type and adapt the UF operations. |
| **Union-Find impl** | `autoclrs/ch21-disjoint-sets/CLRS.Ch21.UnionFind.Impl.fst` | Adapt the Pulse imperative `find`/`union` with path compression for our extended status type. |
| **Union-Find lemmas** | `autoclrs/ch21-disjoint-sets/CLRS.Ch21.UnionFind.Lemmas.fst` | Reuse `count_above` termination measure, rank monotonicity proofs. |
| **DFS (stack-based)** | `autoclrs/ch22-elementary-graph/CLRS.Ch22.DFS.Impl.fst` | Adapt the iterative DFS pattern (work-stack with pre/post-order). The paper's `freeze_inner` is DFS with both pre-order (push to pending, detect back edges) and post-order (complete SCC) actions. |
| **DFS spec** | `autoclrs/ch22-elementary-graph/CLRS.Ch22.DFS.Spec.fst` | Reuse `color` type pattern, `valid_state` invariants. |
| **Graph representation** | `autoclrs/ch22-elementary-graph/CLRS.Ch22.Graph.Common.fst` | Reuse `has_edge`, `reachable_in`, ghost counter pattern (`incr_nat`/`tick`), adjacency matrix utilities. |
| **Pulse patterns** | `pulse/lib/` | Use `Pulse.Lib.Array`, `Pulse.Lib.Reference`, `Pulse.Lib.Vec`, `Pulse.Lib.GhostReference` for heap-allocated arrays and refs. |

## Todos

### Phase 1: Pure Specification Layer (ismm/)

#### 1. `ISMM.Status.fst` — Status type & basic predicates
- Define the 4-state status: `type status = UNMARKED | RANK of nat | REP of nat | RC of nat`
- Define `is_representative`, `is_frozen`, `is_pending` predicates
- Define `node_record` type: `{ status: status; fields: list nat }` (fields = outgoing edges)

#### 2. `ISMM.Graph.fst` — Graph model & SCC specification
- Define graph as `{ n: nat; nodes: seq node_record }` or adapt `has_edge` from ch22
- Define `scc_equiv` relation (bidirectional reachability)
- Define `quotient_dag` (the DAG of SCC equivalence classes)
- State key theorems: SCC quotient is a DAG; SCC is an equivalence relation
- Adapt `reachable_in` from `CLRS.Ch22.Graph.Common`

#### 3. `ISMM.UnionFind.Spec.fst` — Extended union-find specification
- Adapt `CLRS.Ch21.UnionFind.Spec` for 4-state status
- `pure_find`: works on nodes in RANK/REP states (find representative)
- `pure_union`: union by rank, only on RANK nodes
- Prove: `rank_invariant` holds after union; `pure_find` terminates (reuse `count_above` measure)
- Key new invariant: "A node whose representative is RC can only reach other RC representatives"

#### 4. `ISMM.Freeze.Spec.fst` — Pure functional freeze specification
- Define `freeze_inner_spec` as a pure recursive function over the graph
- Specify the pending stack model
- State correctness: after freeze, all reachable nodes from root are partitioned into SCCs with correct external RC
- State the key invariant from Section 4 of the paper

#### 5. `ISMM.Dispose.Spec.fst` — Pure functional dispose specification
- Define `dispose_spec` using dfs/scc/free_list stacks
- State correctness: all nodes in SCC with RC=0 are freed; child SCC RCs decremented; cascading disposal

#### 6. `ISMM.RefCount.Spec.fst` — Acquire/Release specification
- `acquire_spec(r)`: `find(r)` then increment RC
- `release_spec(r)`: `find(r)` then decrement RC; if RC=0 call dispose
- State correctness: RC tracks external reference count faithfully

### Phase 2: Imperative Pulse Implementation

#### 7. `ISMM.Node.fst` — Heap node representation
- Define Pulse node type with mutable `status` field and pointer array for edges
- Define `pts_to` predicate for a node (separation logic ownership)
- Define `graph_pts_to` for an array of nodes (full graph ownership)

#### 8. `ISMM.UnionFind.Impl.fst` — Imperative find/union in Pulse
- Adapt `CLRS.Ch21.UnionFind.Impl` for 4-state status
- `find(x)`: path compression on REP chain, return representative
- `union(x, y)`: merge two RANK nodes by rank
- Prove refinement against `ISMM.UnionFind.Spec`

#### 9. `ISMM.Freeze.Impl.fst` — Imperative freeze in Pulse
- Implement iterative DFS with explicit work-stack (adapt DFS pattern from ch22)
- Pending stack for SCC detection
- Pre-order: push UNMARKED nodes, detect back edges → union SCCs
- Post-order: when top-of-pending = current node, finalize SCC with `RC(1)`
- Prove refinement against `ISMM.Freeze.Spec`

#### 10. `ISMM.Dispose.Impl.fst` — Imperative dispose in Pulse
- Three stacks: `dfs`, `scc`, `free_list`
- Process SCC by following REP pointers to find all members
- Decrement child SCC reference counts; cascade if RC=0
- Deallocate from free_list
- Prove refinement against `ISMM.Dispose.Spec`

#### 11. `ISMM.RefCount.Impl.fst` — Acquire/Release in Pulse
- `incref(r)`: atomic match on RC(n) → RC(n+1)
- `decref(r)`: atomic match on RC(1) → true | RC(n) → RC(n-1), false
- `acquire(r)`: `incref(find(r))`
- `release(r)`: if `decref(find(r))` then `dispose(r)`

### Phase 3: Correctness Proofs

#### 12. `ISMM.Freeze.Lemmas.fst` — Freeze correctness
- Key invariant: "RC-marked representatives can only reach other RC-marked representatives"
- Every reachable node from root gets assigned to exactly one SCC
- Reference counts correctly count external incoming edges
- Termination: each edge followed at most once; each node pushed at most once

#### 13. `ISMM.Dispose.Lemmas.fst` — Dispose correctness
- All nodes in a zero-RC SCC are deallocated
- Child SCC decrements are correct
- No use-after-free (separation logic)
- Termination: each edge followed at most once in disposal

#### 14. `ISMM.Complexity.fst` — Complexity analysis
- Freeze: O(|E| · α(|N|)) — reuse ghost tick counting from `CLRS.Common.Complexity`
- Dispose: O(|E| · α(|N|))
- Acquire/Release: O(α(|N|)) amortized

### Phase 4: Integration & Testing

#### 15. `ISMM.Test.fst` — Test cases
- Unit tests: acyclic graph (linked list), single-node SCC
- Cyclic graph: doubly-linked list, diamond with cycle
- Paper's running example (Fig. 3): nodes A-E with specific edge pattern
- Dispose cascade test: release root → dispose chain

## Key Proof Challenges

1. **Freeze termination**: The while-loop on line 46 (union until matching pending entry) removes ≤ |N| elements total across all calls. Need a global decreasing measure (pending stack size).

2. **SCC correctness**: After freeze, the union-find equivalence classes exactly correspond to the SCC equivalence relation. Requires proving that every back-edge triggers a union that merges the correct components.

3. **Reference count precision**: External RC of each SCC = number of edges crossing SCC boundaries. Inductive argument over the DFS traversal order.

4. **Dispose safety**: Separation logic must ensure no double-free and that all nodes in an SCC are accessible from its representative via REP pointers.

5. **Status field reuse**: The status field serves four purposes across the algorithm's lifecycle (UNMARKED → RANK → REP/RC). Need a state-machine invariant governing valid transitions.

## Suggested Implementation Order

```
ISMM.Status          (standalone, no deps)
ISMM.Graph           (depends on Status)
ISMM.UnionFind.Spec  (depends on Status; adapt from ch21)
ISMM.UnionFind.Impl  (depends on UF.Spec; adapt from ch21)
ISMM.Freeze.Spec     (depends on Graph, UF.Spec)
ISMM.Node            (depends on Status; Pulse types)
ISMM.Freeze.Impl     (depends on Freeze.Spec, Node, UF.Impl; adapt DFS from ch22)
ISMM.Freeze.Lemmas   (depends on Freeze.Spec, Freeze.Impl)
ISMM.Dispose.Spec    (depends on Graph, UF.Spec)
ISMM.RefCount.Spec   (depends on Dispose.Spec)
ISMM.Dispose.Impl    (depends on Dispose.Spec, Node, UF.Impl)
ISMM.RefCount.Impl   (depends on RefCount.Spec, Dispose.Impl)
ISMM.Dispose.Lemmas  (depends on Dispose.Spec, Dispose.Impl)
ISMM.Complexity      (depends on all Impl modules)
ISMM.Test            (depends on all Impl modules)
```

## Notes
- The paper uses a recursive `freeze_inner` for clarity; the implementation should use an explicit work-stack (as noted in Section 3.4 of the paper) since object graphs can be large.
- `incref`/`decref` are marked `atomic` in the paper for concurrency. In a single-threaded Pulse verification, we can omit atomicity, or model it with `Pulse.Lib.Mutex` / `Pulse.Lib.SpinLock` for a concurrent extension.
- The paper's `find` includes path compression. The existing ch21 implementation has both path compression and union-by-rank — directly adaptable.
- Graph representation: the paper uses pointer-based nodes with fields. For Pulse, we can use an array-of-structs model (similar to ch22's flat adjacency matrix) or a pointer-graph model (closer to `Pulse.Lib.LinkedList`). The array-of-structs approach is simpler to verify; pointer-based is more realistic. Start with array-of-structs.

## Implementation Status

### Completed (18 files, ~3381 lines, 26 assume_ + 1 assume)

| File | Lines | Status |
|------|-------|--------|
| ISMM.Status.fst | ~40 | ✅ Pure |
| ISMM.Graph.fst | ~80 | ✅ Pure |
| ISMM.UnionFind.Spec.fst | ~160 | ✅ Pure (1 assume for rank_bounded root) |
| ISMM.UnionFind.Union.fst | ~150 | ✅ Pure |
| ISMM.UnionFind.Compress.fst | ~120 | ✅ Pure |
| ISMM.UnionFind.Impl.fsti | ~170 | ✅ Interface |
| ISMM.UnionFind.Impl.fst | ~660 | ✅ Imperative |
| ISMM.Freeze.Spec.fst | ~60 | ✅ Pure |
| ISMM.Dispose.Spec.fst | ~50 | ✅ Pure |
| ISMM.RefCount.Spec.fst | ~40 | ✅ Pure |
| ISMM.UF.Lemmas.fst | ~220 | ✅ Pure (tag/rank-update preservation) |
| ISMM.Arith.Lemmas.fst | ~115 | ✅ Pure (arithmetic + Seq.upd helpers) |
| ISMM.Freeze.Impl.fsti | ~85 | ✅ Interface |
| ISMM.Freeze.Impl.fst | ~700 | ✅ Imperative (6 assume_) |
| ISMM.Dispose.Impl.fsti | ~75 | ✅ Interface |
| ISMM.Dispose.Impl.fst | ~535 | ✅ Imperative (5 assume_) |
| ISMM.RefCount.Impl.fsti | ~100 | ✅ Interface |
| ISMM.RefCount.Impl.fst | ~155 | ✅ Imperative (2 assume_) |
| ISMM.Test.fst | ~120 | ✅ Test |

### Proven Lemmas
#### ISMM.UF.Lemmas.fst
- `tag_update_preserves_uf_inv`: Tag-only updates with valid_tag preserve uf_inv
- `rank_increase_on_root_preserves_uf_inv`: Rank increases on roots preserve uf_inv
- `tag_rank_increase_on_root_preserves_uf_inv`: Combined tag+rank increase on root
- `noop_write_preserves_to_uf`: Writing the same value back is a no-op
- Bridge lemmas: `to_int_seq_upd`, `to_uf_upd_tag`, `to_uf_upd_rank`, `to_uf_upd_tag_rank`

#### ISMM.Arith.Lemmas.fst
- `product_strict_bound`: c < a ∧ d < b ⟹ c*b + d < a*b
- `fits_product_smaller`: SZ.fits preservation for smaller products
- `adj_index_fits`: Adjacency matrix index bounds from x < n ∧ fi < n ∧ fits(n*n)
- `ghost_ctr_fits`, `inner_ctr_fits`, `rc_inc_fits`, `rc_dec_fits`
- `seq_upd_content_bound`: Stack content < bound preserved after push
- `seq_upd_content_le_bound`: Stack content ≤ bound preserved after push
- `seq_upd_existing_le_bound`: Existing entry update preserves ≤ bound

### Key Architectural Decisions
1. **Separate Refcount Array**: RC values in dedicated `refcount` array, NOT in `rank`.
   Rank only stores UF ranks (never modified by RC ops). Trivially preserves uf_inv.
2. **Stack Content Invariants**: Universal quantifiers `forall i. i < top ==> stk[i] < n`
   track that all stack elements are valid node indices. Propagated through all helper
   functions and loop invariants. Uses explicit `seq_upd_content_bound` lemma calls for Z3.
3. **DFS Edge Content**: Separate invariant `forall i. i < top ==> edge[i] <= n` for
   the freeze DFS edge stack (values 0..n, where n means "all edges explored").

### Remaining assume_ obligations (13 total + 1 assume)

| Category | Count | Files | Description |
|----------|-------|-------|-------------|
| Stack overflow | 4 | Freeze(2), Dispose(2) | Stack tops < n before push (needs visited-once argument) |
| Ghost counter | 4 | Freeze(2), Dispose(2) | Strict bound gc < bound for increment (needs termination proof) |
| RC fits | 3 | Freeze(2), RefCount(1) | fits(rc+1) before increment (needs RC bound or API contract) |
| RC arithmetic | 2 | Dispose(1), RefCount(1) | rc > 0 before decrement (needs protocol invariant) |
| Spec rank bound | 1 | Spec | rank[root] < n (needs CLRS Lemma 21.4: 2^rank ≤ component_size) |

### Why remaining assumes are hard
- **Stack overflow (4)**: Requires ghost visited set proving each node pushed at most once.
  Pattern: `count_ones visited n == stack_top` (from autoclrs DFS). Requires maintaining
  visited array through all push operations.
- **Ghost counters (4)**: The strict bound `gc < bound` requires proving the loop body only
  executes when work remains. Equivalent to DFS termination: at most n*(n+1) events.
  The while loop's decreases clause verifies this AFTER the body, but we need it BEFORE
  the increment.
- **RC fits (3)**: At freeze-time, RC ≤ total cross-edges ≤ n². But tracking per-SCC
  cross-edge counts through the DFS is complex. For the acquire API, RC is unbounded
  (depends on caller behavior).
- **RC > 0 (2)**: Protocol invariant: every decrement is preceded by a matching increment.
  Formalizing requires linear/affine resource tracking.
- **Spec rank bound (1)**: CLRS Lemma 21.4 requires ghost component-size tracking through
  union operations, proving 2^rank ≤ size ≤ n. Available in autoclrs as
  `size_rank_invariant` but requires adapting to ISMM's 4-state UF.
