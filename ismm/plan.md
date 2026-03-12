# Plan: Verified Pulse Implementation of "Reference Counting Deeply Immutable Data Structures with Cycles"

## Progress Checklist

### Phase 1: Pure Specifications (all verified ✓)
- [x] `ismm/Makefile` — Build system (uses F*/Pulse from submodules)
- [x] `ISMM.Status.fst` — Status type & predicates
- [x] `ISMM.Graph.fst` — Graph model, reachability, SCC equivalence
- [x] `ISMM.UnionFind.Spec.fst` — Pure UF spec with 3-array model (1 assume in rank_bounded root case)
- [x] `ISMM.UnionFind.Union.fst` — Union + correctness/stability proofs
- [x] `ISMM.UnionFind.Compress.fst` — Path compression lemmas
- [x] `ISMM.Freeze.Spec.fst` — Freeze postcondition predicates
- [x] `ISMM.Dispose.Spec.fst` — Dispose postcondition predicates
- [x] `ISMM.RefCount.Spec.fst` — Acquire/Release postcondition predicates

### Phase 2: Imperative Implementations (all verified ✓)
- [x] `ISMM.UnionFind.Impl.fsti` + `.fst` — Imperative UF with path compression (~660 lines)
- [x] `ISMM.Freeze.Impl.fsti` + `.fst` — Freeze DFS + SCC detection (~640 lines, 14 assume_)
- [x] `ISMM.Dispose.Impl.fsti` + `.fst` — Dispose with cascading (~480 lines, 14 assume_)
- [x] `ISMM.RefCount.Impl.fsti` + `.fst` — Acquire/Release (~140 lines, 4 assume_)
- [x] `ISMM.Test.fst` — Basic UF test (make_set, union, find)

### Phase 3: Remaining Work
- [ ] `ISMM.Freeze.Lemmas.fst` — Prove freeze assume_ obligations (tag/rank updates preserve uf_inv)
- [ ] `ISMM.Dispose.Lemmas.fst` — Prove dispose assume_ obligations
- [ ] Prove `rank_bounded` root case (needs Lemma 21.4: 2^rank ≤ component_size)

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

### Complexity: O(|E| · α(|N|)) for freeze and dispose (almost linear). (Not verified; included for context only.)

## Top-Level API Sketch

### Pure Specification Types (`ISMM.Status.fst`)

```fstar
module ISMM.Status

/// Node status — the paper's 4-state field (Fig. 2, Section 3)
/// Encoded in two parallel arrays: status_tag (int) + status_data (SZ.t)
///
///   Tag 0 = UNMARKED    data ignored
///   Tag 1 = RANK(n)     data = n (UF rank / max tree depth)
///   Tag 2 = REP(ptr)    data = ptr (UF parent index)
///   Tag 3 = RC(n)       data = n (external reference count)

let tag_unmarked : int = 0
let tag_rank     : int = 1
let tag_rep      : int = 2
let tag_rc       : int = 3

let is_unmarked  (stag: Seq.seq int) (i: nat) : prop =
  i < Seq.length stag /\ Seq.index stag i == tag_unmarked

let is_rank      (stag: Seq.seq int) (i: nat) : prop =
  i < Seq.length stag /\ Seq.index stag i == tag_rank

let is_rep       (stag: Seq.seq int) (i: nat) : prop =
  i < Seq.length stag /\ Seq.index stag i == tag_rep

let is_rc        (stag: Seq.seq int) (i: nat) : prop =
  i < Seq.length stag /\ Seq.index stag i == tag_rc

let is_frozen    (stag: Seq.seq int) (i: nat) : prop =
  is_rep stag i \/ is_rc stag i

/// The paper's key invariant (Section 4):
/// A node whose representative is marked RC can only reach
/// other nodes whose representative is marked RC.
let rc_closed (stag: Seq.seq int) (sdata: Seq.seq SZ.t) (adj: Seq.seq int) (n: nat) : prop = ...
```

### Pure Specification: Extended Union-Find (`ISMM.UnionFind.Spec.fst`)

```fstar
module ISMM.UnionFind.Spec

open ISMM.Status

/// Pure forest model — extends CLRS.Ch21.UnionFind.Spec with 4-state status
type uf_state = {
  n: nat;
  tag:  Seq.seq int;    // status tag per node
  data: Seq.seq nat;    // status data per node (rank, parent idx, or RC)
}

/// UF invariant: REP nodes form a forest; RANK nodes obey rank_invariant
val uf_inv (s: uf_state) : prop

/// Pure find: follow REP chain to representative (terminates via count_above)
val pure_find (s: uf_state{uf_inv s}) (x: nat{x < s.n})
  : Tot nat (decreases (count_above s.data (Seq.index s.data x) 0 s.n))

/// Pure union: merge two RANK-state representatives by rank
val pure_union (s: uf_state{uf_inv s}) (x y: nat{x < s.n /\ y < s.n})
  : Tot uf_state
```

### Graph Model & SCC Predicates (`ISMM.Graph.fst`)

```fstar
module ISMM.Graph

open FStar.Mul

/// Graph representation: flat adjacency matrix (Seq.seq int) of size n*n,
/// where adj[u*n+v] <> 0 indicates edge u → v. (Same as CLRS.Ch22.Graph.Common.)
let has_edge (adj: Seq.seq int) (n: nat) (u v: nat) : prop =
  u < n /\ v < n /\ u * n + v < Seq.length adj /\ Seq.index adj (u * n + v) <> 0

let rec reachable_in (adj: Seq.seq int) (n: nat) (src dst: nat) (steps: nat)
  : Tot prop (decreases steps)
  = if steps = 0 then dst == src
    else exists (u: nat). u < n /\ reachable_in adj n src u (steps - 1) /\ has_edge adj n u dst

/// Two nodes are SCC-equivalent iff mutually reachable
let scc_equiv (adj: Seq.seq int) (n: nat) (u v: nat) : prop =
  (exists k. reachable_in adj n u v k) /\ (exists k. reachable_in adj n v u k)

/// After freeze: all reachable nodes are in REP or RC state
let all_reachable_frozen (stag: Seq.seq int) (adj: Seq.seq int) (n: nat) (root: nat) : prop =
  forall (v: nat) (k: nat). reachable_in adj n root v k ==> is_frozen stag v

/// After freeze: UF equivalence classes = SCC equivalence classes
let sccs_correct (stag sdata: Seq.seq int) (adj: Seq.seq int) (n: nat) (root: nat) : prop =
  forall (u v: nat). u < n /\ v < n /\
    (exists k. reachable_in adj n root u k) /\ (exists k. reachable_in adj n root v k) ==>
    (pure_find_of stag sdata n u == pure_find_of stag sdata n v <==> scc_equiv adj n u v)
```

### Imperative Interface: Find & Union (`ISMM.UnionFind.Impl.fsti`)

```fstar
module ISMM.UnionFind.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A  = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = ISMM.UnionFind.Spec
open ISMM.Status

/// Bridge: imperative arrays → pure spec
let to_uf (stag: Seq.seq int) (sdata: Seq.seq SZ.t) (n: nat) : Spec.uf_state = ...

/// FIND with path compression (paper Fig. 1 + §3.1)
/// Follows REP chain to representative; compresses path.
fn find_set
  (status_tag:  A.array int)
  (status_data: A.array SZ.t)
  (x: SZ.t) (n: SZ.t)
  (#stag:  erased (Seq.seq int))
  (#sdata: erased (Seq.seq SZ.t))
  requires
    A.pts_to status_tag stag **
    A.pts_to status_data sdata **
    pure (
      SZ.v x < SZ.v n /\
      SZ.v n <= Seq.length stag /\
      SZ.v n <= Seq.length sdata /\
      Spec.uf_inv (to_uf stag sdata (SZ.v n)) /\
      ~(is_unmarked stag (SZ.v x))       // x must be visited (RANK, REP, or RC)
    )
  returns root: SZ.t
  ensures exists* stag' sdata'.
    A.pts_to status_tag stag' **
    A.pts_to status_data sdata' **
    pure (
      SZ.v root < SZ.v n /\
      Spec.uf_inv (to_uf stag' sdata' (SZ.v n)) /\
      SZ.v root == Spec.pure_find (to_uf stag sdata (SZ.v n)) (SZ.v x) /\
      // Equivalence classes preserved
      (forall (z: nat). z < SZ.v n /\ ~(is_unmarked stag z) ==>
        Spec.pure_find (to_uf stag' sdata' (SZ.v n)) z ==
        Spec.pure_find (to_uf stag sdata (SZ.v n)) z)
    )

/// UNION by rank (paper Fig. 1 + §3.1, lines 46–48)
/// Merges two RANK-state SCCs on the pending stack.
fn union_set
  (status_tag:  A.array int)
  (status_data: A.array SZ.t)
  (x: SZ.t) (y: SZ.t) (n: SZ.t)
  (#stag:  erased (Seq.seq int))
  (#sdata: erased (Seq.seq SZ.t))
  requires
    A.pts_to status_tag stag **
    A.pts_to status_data sdata **
    pure (
      SZ.v x < SZ.v n /\ SZ.v y < SZ.v n /\
      SZ.v n <= Seq.length stag /\
      SZ.v n <= Seq.length sdata /\
      Spec.uf_inv (to_uf stag sdata (SZ.v n))
    )
  returns merged: bool
  ensures exists* stag' sdata'.
    A.pts_to status_tag stag' **
    A.pts_to status_data sdata' **
    pure (
      Seq.length stag' == Seq.length stag /\
      Seq.length sdata' == Seq.length sdata /\
      Spec.uf_inv (to_uf stag' sdata' (SZ.v n)) /\
      // After union, x and y share a representative
      Spec.pure_find (to_uf stag' sdata' (SZ.v n)) (SZ.v x) ==
        Spec.pure_find (to_uf stag' sdata' (SZ.v n)) (SZ.v y) /\
      // Disjoint elements unchanged
      (forall (z: nat). z < SZ.v n ==>
        Spec.pure_find (to_uf stag sdata (SZ.v n)) z <>
          Spec.pure_find (to_uf stag sdata (SZ.v n)) (SZ.v x) ==>
        Spec.pure_find (to_uf stag sdata (SZ.v n)) z <>
          Spec.pure_find (to_uf stag sdata (SZ.v n)) (SZ.v y) ==>
        Spec.pure_find (to_uf stag' sdata' (SZ.v n)) z ==
          Spec.pure_find (to_uf stag sdata (SZ.v n)) z)
    )
```

### Imperative Interface: Freeze (`ISMM.Freeze.Impl.fsti`)

```fstar
module ISMM.Freeze.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A  = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
open ISMM.Status
open ISMM.Graph

/// freeze(root): compute SCCs and initial reference counts.
/// Paper §3.1 (Fig. 2): iterative DFS with pending stack.
///
/// Pre:  all nodes UNMARKED; root < n; adj is n×n adjacency matrix.
/// Post: every reachable node is REP or RC; UF classes = SCCs;
///       each SCC rep has correct external RC.
fn freeze
  (adj:         A.array int)
  (status_tag:  A.array int)
  (status_data: A.array SZ.t)
  (pending:     A.array SZ.t)   // working stack for SCC detection
  (n: SZ.t)
  (root: SZ.t)
  (#sadj:   erased (Seq.seq int))
  (#stag:   erased (Seq.seq int))
  (#sdata:  erased (Seq.seq SZ.t))
  (#spend:  erased (Seq.seq SZ.t))
  requires
    A.pts_to adj sadj **
    A.pts_to status_tag stag **
    A.pts_to status_data sdata **
    A.pts_to pending spend **
    pure (
      SZ.v n > 0 /\
      SZ.v root < SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sadj <= A.length adj /\
      Seq.length stag == SZ.v n /\
      Seq.length stag <= A.length status_tag /\
      Seq.length sdata == SZ.v n /\
      Seq.length sdata <= A.length status_data /\
      Seq.length spend == SZ.v n /\
      Seq.length spend <= A.length pending /\
      SZ.fits (SZ.v n * SZ.v n) /\
      // All nodes start UNMARKED
      (forall (i: nat). i < SZ.v n ==> is_unmarked stag i)
    )
  ensures exists* stag' sdata' spend'.
    A.pts_to adj sadj **
    A.pts_to status_tag stag' **
    A.pts_to status_data sdata' **
    A.pts_to pending spend' **
    pure (
      Seq.length stag' == SZ.v n /\
      Seq.length sdata' == SZ.v n /\
      // All reachable nodes frozen (REP or RC)
      all_reachable_frozen stag' sadj (SZ.v n) (SZ.v root) /\
      // UF equivalence classes = SCCs
      sccs_correct stag' sdata' sadj (SZ.v n) (SZ.v root) /\
      // Non-reachable nodes unchanged
      (forall (i: nat). i < SZ.v n /\
        (forall (k: nat). ~(reachable_in sadj (SZ.v n) (SZ.v root) i k)) ==>
        is_unmarked stag' i)
    )
```

### Imperative Interface: Dispose (`ISMM.Dispose.Impl.fsti`)

```fstar
module ISMM.Dispose.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul

module A  = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
open ISMM.Status
open ISMM.Graph

/// dispose(r): deallocate SCC at r; cascade to child SCCs with RC=0.
/// Paper §3.2 (Fig. 4): three-stack traversal (dfs, scc, free_list).
///
/// Pre:  r is an SCC representative with RC(0).
/// Post: all nodes in r's SCC marked as deallocated;
///       child SCC reference counts decremented;
///       child SCCs reaching RC(0) also disposed.
fn dispose
  (adj:         A.array int)
  (status_tag:  A.array int)
  (status_data: A.array SZ.t)
  (dfs_stack:   A.array SZ.t)
  (scc_stack:   A.array SZ.t)
  (free_list:   A.array SZ.t)
  (n: SZ.t)
  (r: SZ.t)
  (#sadj:   erased (Seq.seq int))
  (#stag:   erased (Seq.seq int))
  (#sdata:  erased (Seq.seq SZ.t))
  (#sdfs:   erased (Seq.seq SZ.t))
  (#sscc:   erased (Seq.seq SZ.t))
  (#sfree:  erased (Seq.seq SZ.t))
  requires
    A.pts_to adj sadj **
    A.pts_to status_tag stag **
    A.pts_to status_data sdata **
    A.pts_to dfs_stack sdfs **
    A.pts_to scc_stack sscc **
    A.pts_to free_list sfree **
    pure (
      SZ.v n > 0 /\
      SZ.v r < SZ.v n /\
      is_rc stag (SZ.v r) /\
      SZ.v (Seq.index sdata (SZ.v r)) == 0 /\   // RC = 0
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length stag == SZ.v n /\
      Seq.length sdata == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  ensures exists* stag' sdata' sdfs' sscc' sfree'.
    A.pts_to adj sadj **
    A.pts_to status_tag stag' **
    A.pts_to status_data sdata' **
    A.pts_to dfs_stack sdfs' **
    A.pts_to scc_stack sscc' **
    A.pts_to free_list sfree' **
    pure (
      Seq.length stag' == SZ.v n /\
      Seq.length sdata' == SZ.v n
      // All nodes in r's SCC deallocated (tag set to a "freed" marker)
      // Child SCC reference counts correctly decremented
      // No double-free
    )
```

### Imperative Interface: Acquire & Release (`ISMM.RefCount.Impl.fsti`)

```fstar
module ISMM.RefCount.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A  = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
open ISMM.Status

/// acquire(r): increment SCC reference count. (Paper §3.3, Fig. 4 line 78)
fn acquire
  (status_tag:  A.array int)
  (status_data: A.array SZ.t)
  (r: SZ.t) (n: SZ.t)
  (#stag:  erased (Seq.seq int))
  (#sdata: erased (Seq.seq SZ.t))
  requires
    A.pts_to status_tag stag **
    A.pts_to status_data sdata **
    pure (
      SZ.v r < SZ.v n /\
      SZ.v n <= Seq.length stag /\
      SZ.v n <= Seq.length sdata /\
      is_frozen stag (SZ.v r)
    )
  ensures exists* stag' sdata'.
    A.pts_to status_tag stag' **
    A.pts_to status_data sdata' **
    pure (
      Seq.length stag' == Seq.length stag /\
      Seq.length sdata' == Seq.length sdata /\
      // find(r)'s RC incremented by 1; everything else unchanged
      (let rep = Spec.pure_find (to_uf stag sdata (SZ.v n)) (SZ.v r) in
       SZ.v (Seq.index sdata' rep) == SZ.v (Seq.index sdata rep) + 1 /\
       Seq.index stag' rep == tag_rc /\
       (forall (i: nat). i < SZ.v n /\ i <> rep ==>
         Seq.index stag' i == Seq.index stag i /\
         SZ.v (Seq.index sdata' i) == SZ.v (Seq.index sdata i)))
    )

/// release(r): decrement SCC ref count; dispose on zero. (Paper §3.3, Fig. 4 lines 80–82)
fn release
  (adj:         A.array int)
  (status_tag:  A.array int)
  (status_data: A.array SZ.t)
  (dfs_stack:   A.array SZ.t)
  (scc_stack:   A.array SZ.t)
  (free_list:   A.array SZ.t)
  (n: SZ.t) (r: SZ.t)
  (#sadj:   erased (Seq.seq int))
  (#stag:   erased (Seq.seq int))
  (#sdata:  erased (Seq.seq SZ.t))
  (#sdfs:   erased (Seq.seq SZ.t))
  (#sscc:   erased (Seq.seq SZ.t))
  (#sfree:  erased (Seq.seq SZ.t))
  requires
    A.pts_to adj sadj **
    A.pts_to status_tag stag **
    A.pts_to status_data sdata **
    A.pts_to dfs_stack sdfs **
    A.pts_to scc_stack sscc **
    A.pts_to free_list sfree **
    pure (
      SZ.v n > 0 /\
      SZ.v r < SZ.v n /\
      is_frozen stag (SZ.v r) /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length stag == SZ.v n /\
      Seq.length sdata == SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n) /\
      // RC >= 1 (we hold a reference)
      (let rep = Spec.pure_find (to_uf stag sdata (SZ.v n)) (SZ.v r) in
       is_rc stag rep /\ SZ.v (Seq.index sdata rep) >= 1)
    )
  ensures exists* stag' sdata' sdfs' sscc' sfree'.
    A.pts_to adj sadj **
    A.pts_to status_tag stag' **
    A.pts_to status_data sdata' **
    A.pts_to dfs_stack sdfs' **
    A.pts_to scc_stack sscc' **
    A.pts_to free_list sfree' **
    pure (
      Seq.length stag' == SZ.v n /\
      Seq.length sdata' == SZ.v n
      // If RC was 1: SCC disposed (cascading)
      // If RC was > 1: RC decremented by 1, nothing else changed
    )
```

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
ISMM.Test            (depends on all Impl modules)
```

## Notes
- The paper uses a recursive `freeze_inner` for clarity; the implementation should use an explicit work-stack (as noted in Section 3.4 of the paper) since object graphs can be large.
- `incref`/`decref` are marked `atomic` in the paper for concurrency. In a single-threaded Pulse verification, we can omit atomicity, or model it with `Pulse.Lib.Mutex` / `Pulse.Lib.SpinLock` for a concurrent extension.
- The paper's `find` includes path compression. The existing ch21 implementation has both path compression and union-by-rank — directly adaptable.
- Graph representation: the paper uses pointer-based nodes with fields. For Pulse, we can use an array-of-structs model (similar to ch22's flat adjacency matrix) or a pointer-graph model (closer to `Pulse.Lib.LinkedList`). The array-of-structs approach is simpler to verify; pointer-based is more realistic. Start with array-of-structs.
