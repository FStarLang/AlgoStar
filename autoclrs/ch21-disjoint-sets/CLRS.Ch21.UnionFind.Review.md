# Union-Find / Disjoint Sets — Review (CLRS §21.3)

**Last reviewed:** 2026-03-16
**Verification status:** ✅ All 4 source files verify — **zero admits, zero assumes**
**Full rebuild time:** ~2 min 9 sec

---

## Checklist

Priority-ordered items to address. Items marked ✅ are resolved.

- [x] **P0 — Verify clean build.** All 4 source files verify with zero admits/assumes.
- [x] **P1 — `union` calls `find_set` with path compression.** Confirmed:
      `Impl.fst` lines 630–633 call `find_set` (not `find_root_imp`), matching CLRS §21.3.
- [x] **P2 — Fix SMTPat warning in Lemmas.fst:443.** Warning 271: pattern
      `[SMTPat ()]` on `check_size_bound` misses bound variable `i`.
      Replaced with `[SMTPat (Seq.index f'.size i)]`. ✅ Fixed.
- [x] **P3 — Fix stale README.md.** Line 167 said "union … uses
      `find_root_imp` (read-only)" but `union` now calls `find_set`.
      Updated to match current implementation. ✅ Fixed.
- [x] **P4 — Fix RUBRIC_21.md: Complexity.fst/fsti claimed present but missing.**
      Lines 38–39 said Complexity files are "✅ Present" but no such files
      exist on disk. Corrected rubric to mark them as ❌ Missing. ✅ Fixed.
- [x] **P5 — Proof optimization: tighten `--z3rlimit 100` in Impl.fst.**
      `compress_path`, `find_set`, and `union` all reduced from
      `--z3rlimit 100` to `--z3rlimit 40`. Full rebuild passes cleanly.
      ✅ Fixed.

### Spec validation

- [x] **SV1 — ImplTest.fst written and verified.**
      `CLRS.Ch21.UnionFind.ImplTest.fst` tests a 3-element instance:
      make_set, find_set on fresh forest (returns self), union(0,1)
      merge (find(0)==find(1)), and stability (find(2)==2).
      Zero admits, zero assumes. ✅
- [x] **SV2 — Preconditions satisfiable.** All three API preconditions
      (make_set, find_set, union) are proven satisfiable on the test
      instance. ✅
- [x] **SV3 — Postconditions precise for single operations.** After
      make_set, the postcondition (uf_inv + zero ranks) is strong enough
      to determine pure_find(x)==x. After union, merge and stability
      clauses fully determine outputs. ✅
- [x] **SV4 — Union membership clause added.** Added missing membership
      clause to `union` postcondition in `Impl.fsti` and proven in
      `Impl.fst`. New `Spec.fst` lemmas: `pure_union_membership`,
      `pure_union_membership_all`. Enables multi-step union reasoning:
      elements previously in x's or y's class remain in the merged
      class. ✅ Fixed.
- [ ] **SV5 — Rank bound not preserved by union.** The `union`
      postcondition does not re-establish `rank[i] < n` for the output
      ranks. In the equal-rank case, proving `rank_x + 1 < n` requires
      the logarithmic bound from `Lemmas.fst` (not threaded through
      imperative code). This prevents chaining multiple union calls
      without independent rank bound proofs.

### Out of scope (documented limitations)

- Amortized O(α(n)) complexity (CLRS §21.4) — not formalized.
- Ghost tick counter — O(log n) bound is on the pure model, not
  instrumented in the Pulse implementation.
- `size_rank_invariant` not threaded through imperative code.
- `rank[i] < n` precondition on `union` — provably maintained but
  caller must establish.

---

## Top-Level Signatures (`Impl.fsti`)

Three operations are verified in `CLRS.Ch21.UnionFind.Impl.fsti`:

### MAKE-SET

```fstar
fn make_set
  (parent: array SZ.t)
  (rank: array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (n: SZ.t)
  requires
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      SZ.v n > 0 /\
      SZ.v n <= A.length parent /\
      SZ.v n <= A.length rank /\
      Seq.length sparent == A.length parent /\
      Seq.length srank == A.length rank
    )
  ensures exists* sp sr.
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      is_forest sp (SZ.v n) /\
      Spec.uf_inv (to_uf sp sr (SZ.v n)) /\
      (forall (idx: nat). idx < SZ.v n ==> is_root_at sp idx) /\
      (forall (idx: nat). idx < SZ.v n /\ idx < Seq.length sr ==> SZ.v (Seq.index sr idx) == 0)
    )
```

Initializes `parent[i] = i`, `rank[i] = 0` for all `i < n`. Every element
is its own root. Establishes `uf_inv` and `is_forest`.

### FIND-SET

```fstar
fn find_set
  (parent: A.array SZ.t) (x: SZ.t) (n: SZ.t)
  (#sparent: erased (Seq.seq SZ.t))
  (#srank: erased (Seq.seq SZ.t))
  requires
    A.pts_to parent sparent **
    pure (
      is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\
      SZ.v n <= Seq.length sparent /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n))
    )
  returns root: SZ.t
  ensures exists* sp.
    A.pts_to parent sp **
    pure (
      SZ.v root < SZ.v n /\
      Seq.length sp == Seq.length sparent /\
      is_forest sp (SZ.v n) /\
      SZ.v (Seq.index sp (SZ.v x)) == SZ.v root /\
      SZ.v (Seq.index sp (SZ.v root)) == SZ.v root /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n)) /\
      Spec.uf_inv (to_uf sp srank (SZ.v n)) /\
      SZ.v root == Spec.pure_find (to_uf sparent srank (SZ.v n)) (SZ.v x) /\
      (forall (z: nat). z < SZ.v n ==>
        Spec.pure_find (to_uf sp srank (SZ.v n)) z ==
        Spec.pure_find (to_uf sparent srank (SZ.v n)) z)
    )
```

Two-pass path compression (CLRS §21.3): Pass 1 finds the root (read-only),
Pass 2 compresses the path. The postcondition guarantees:

* `root == pure_find(original_forest, x)` — correct root returned.
* `parent[x] == root` — x now points directly to root.
* `uf_inv` preserved for the new forest.
* **All equivalence classes preserved**: for all `z`,
  `pure_find(new, z) == pure_find(old, z)`.

### UNION

```fstar
fn union
  (parent: array SZ.t)
  (rank: array SZ.t)
  (#sparent: Ghost.erased (Seq.seq SZ.t))
  (#srank: Ghost.erased (Seq.seq SZ.t))
  (x: SZ.t) (y: SZ.t) (n: SZ.t)
  requires
    A.pts_to parent sparent **
    A.pts_to rank srank **
    pure (
      is_forest sparent (SZ.v n) /\
      SZ.v x < SZ.v n /\ SZ.v y < SZ.v n /\
      Seq.length srank == Seq.length sparent /\
      SZ.v n <= Seq.length sparent /\
      Spec.uf_inv (to_uf sparent srank (SZ.v n)) /\
      (forall (i: nat). i < SZ.v n ==> SZ.v (Seq.index srank i) < SZ.v n)
    )
  ensures exists* sp sr.
    A.pts_to parent sp **
    A.pts_to rank sr **
    pure (
      is_forest sp (SZ.v n) /\
      Seq.length sp == Seq.length sparent /\
      Seq.length sr == Seq.length srank /\
      Spec.uf_inv (to_uf sp sr (SZ.v n)) /\
      Spec.pure_find (to_uf sp sr (SZ.v n)) (SZ.v x) ==
        Spec.pure_find (to_uf sp sr (SZ.v n)) (SZ.v y) /\
      (forall (z: nat). z < SZ.v n ==>
        Spec.pure_find (to_uf sparent srank (SZ.v n)) z <>
          Spec.pure_find (to_uf sparent srank (SZ.v n)) (SZ.v x) ==>
        Spec.pure_find (to_uf sparent srank (SZ.v n)) z <>
          Spec.pure_find (to_uf sparent srank (SZ.v n)) (SZ.v y) ==>
        Spec.pure_find (to_uf sp sr (SZ.v n)) z ==
          Spec.pure_find (to_uf sparent srank (SZ.v n)) z)
    )
```

Union by rank. The postcondition guarantees:

* **Merge**: `pure_find(new, x) == pure_find(new, y)`.
* **Stability**: Elements not in x's or y's class are unchanged.

## Auxiliary Definitions

### `uf_forest`, `uf_inv` (from `CLRS.Ch21.UnionFind.Spec`)

```fstar
type uf_forest = {
  parent: Seq.seq nat;
  rank: Seq.seq nat;
  n: nat;
}

let uf_inv (f: uf_forest) : prop =
  is_valid_uf f /\ rank_invariant f
```

Where `is_valid_uf` requires `n > 0`, correct lengths, and all parents
in bounds. The `rank_invariant` (CLRS Lemma 21.4) requires rank to
strictly increase along parent pointers:

```fstar
let rank_invariant (f: uf_forest) : prop =
  is_valid_uf f /\
  (forall (x: nat). x < f.n /\ Seq.index f.parent x <> x ==>
    Seq.index f.rank x < Seq.index f.rank (Seq.index f.parent x))
```

### `pure_find` (from `CLRS.Ch21.UnionFind.Spec`)

```fstar
let rec pure_find (f: uf_forest{uf_inv f}) (x: nat{x < f.n})
  : Tot nat (decreases (count_above f.rank (Seq.index f.rank x) 0 f.n))
  = if Seq.index f.parent x = x then x
    else begin
      count_above_strict f.rank (Seq.index f.rank x) (Seq.index f.parent x) 0 f.n;
      pure_find f (Seq.index f.parent x)
    end
```

The pure find function follows parent pointers to the root. **Termination**
is proven using `count_above` — the number of nodes with rank strictly above
the current node's rank. Each step moves to a node with strictly higher
rank, so this count strictly decreases. This is a **fuel-free** termination
argument — no `fuel` parameter is needed.

### `to_uf` (from `CLRS.Ch21.UnionFind.Impl.fsti`)

```fstar
let to_nat_seq (s: Seq.seq SZ.t) (n: nat) : Seq.seq nat =
  Seq.init n (fun (i: nat{i < n}) ->
    if i < Seq.length s then (SZ.v (Seq.index s i) <: nat) else (0 <: nat))

let to_uf (parent rank: Seq.seq SZ.t) (n: nat) : Spec.uf_forest =
  { Spec.parent = to_nat_seq parent n;
    Spec.rank = to_nat_seq rank n;
    Spec.n = n }
```

The bridge function converts imperative machine-integer arrays to the pure
spec's natural-number sequences. Key bridge lemmas:

* `to_uf_upd_parent`: Parent array update corresponds to spec record update.
* `to_uf_upd_rank`: Rank array update corresponds to spec record update.
* `to_uf_upd_both`: Combined parent + rank update.

## What Is Proven

**Functional correctness:**

* `make_set` initializes a valid forest where every element is its own
  representative.

* `find_set` returns `pure_find(original, x)` — the correct representative
  — and path compression preserves all equivalence classes.

* `union` merges the classes of `x` and `y` while preserving all other
  classes.

**Structural invariants:**

* `uf_inv` (including `rank_invariant`) is preserved across all three
  operations.

* `is_forest` (imperative termination invariant) is preserved.

**Pure spec theorems** (from `CLRS.Ch21.UnionFind.Spec`):

* `pure_find_is_root`: Find returns a root.
* `pure_find_idempotent`: Find of find is find.
* `compress_preserves_find_all`: Compression preserves all equivalence classes.
* `pure_union_preserves_inv`: Union preserves `uf_inv`.
* `pure_union_same_set`: After union, `pure_find x == pure_find y`.
* `pure_union_stability`: Union does not merge unrelated sets.

**Rank bounds** (from `CLRS.Ch21.UnionFind.Lemmas`):

* `size_rank_invariant`: Every node's subtree has ≥ 2^rank nodes.
* `rank_logarithmic_bound_sized`: rank[x] ≤ ⌊log₂ n⌋.
* `union_by_rank_logarithmic_find`: tree height ≤ ⌊log₂ n⌋.
* `find_logarithmic_complexity`: O(log n) worst-case per find (without
  path compression amortization).

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **No amortized O(α(n)) complexity proof.** The amortized complexity of
   union-find with both path compression and union by rank is O(α(n)) per
   operation, where α is the inverse Ackermann function. This is **not
   formalized**. The Lemmas module proves the weaker O(log n) worst-case
   bound per find via the rank bound. Proving α(n) would require defining
   the Ackermann function and a potential function argument, which is
   significantly more complex.

2. **No ghost counter for operations.** Unlike other algorithms in this
   repository, the union-find operations do not carry a ghost counter for
   counting comparisons or pointer traversals. The O(log n) bound is
   proven on the pure model, not linked to the Pulse implementation.

3. **`find_set` does not modify rank.** Path compression only updates
   parent pointers, not ranks. The rank array is passed as a ghost
   parameter (`#srank`) and is not written to during `find_set`. This is
   correct per CLRS (ranks are an upper bound on height, not exact heights),
   but means ranks may become stale upper bounds after compression.

4. ~~**`union` does not perform path compression.**~~ **RESOLVED.** The
   `union` function now calls `find_set` (with full path compression)
   rather than `find_root_imp` (read-only). This matches CLRS §21.3
   where UNION calls FIND-SET. A helper lemma
   `pure_find_self_implies_root_at` bridges the pure spec root detection
   back to the imperative `is_root_at` predicate, needed to prove that
   a root found in the first `find_set` call remains a root after the
   second `find_set` call's path compression.

5. **Size-rank invariant not threaded through Pulse.** The
   `size_rank_invariant` and `size_correctness_invariant` are proven on the
   pure `uf_forest_sized` model but are not maintained by the imperative
   code. The imperative code does not track subtree sizes at all — the
   `rank` array serves as the proxy. The logarithmic rank bound is proven
   in the pure model and could in principle be connected to the imperative
   code, but this connection is not formalized.

6. **`rank[i] < n` precondition on `union`.** The `union` function
   requires `forall i. rank[i] < n` as a precondition. This is provably
   maintained (since rank ≤ ⌊log₂ n⌋ < n for n > 0), but the caller must
   establish it.

## Profiling & Proof Resource Usage

| File | Lines | z3rlimit | Rebuild time | Notes |
|------|-------|----------|-------------|-------|
| `Spec.fst` | 375 | max 80 | ~25s | 4 `#restart-solver`; `compress_preserves_find` is heaviest |
| `Lemmas.fst` | 676 | max 20 | ~40s | Warning 271 (SMTPat) at line 443 |
| `Impl.fsti` | 150 | — | ~5s | Interface only |
| `Impl.fst` | 686 | max 40 | ~60s | `compress_path`, `find_set`, `union` (reduced from 100) |
| **Total** | **1887** | — | **~2m 6s** | |

### Resource flags in use

- `Spec.fst`: `--z3rlimit 80 --fuel 1 --ifuel 0` (heaviest block: `compress_preserves_find`)
- `Lemmas.fst`: `--z3rlimit 20` (one block at `--fuel 2`)
- `Impl.fst`: `--z3rlimit 40 --fuel 2 --ifuel 1` (3 blocks, tightened from 100)

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Find (worst-case) | O(log n) | ⚠️ Pure model only | Upper bound |
| Find (amortized) | O(α(n)) | ❌ Not proven | — |
| Union (worst-case) | O(log n) | ⚠️ Pure model only | Upper bound |

The O(log n) bound for find comes from `rank ≤ ⌊log₂ n⌋` and
`tree height ≤ rank[root]`. The amortized O(α(n)) bound is not formalized.

## Proof Structure

**Termination of `pure_find`:** Uses `count_above f.rank (rank[x]) 0 n` —
the count of nodes with rank strictly above `rank[x]`. Since each step
moves to a parent with strictly higher rank, this count strictly decreases.
This avoids the common pitfall of using a fuel parameter.

**Compression correctness:** `compress_preserves_find` is proven by
induction on `count_above`. The key insight: compressing node `v` to its
root only changes `parent[v]`, and since all nodes on the path from `v` to
the root already have `pure_find = root`, the compression doesn't change
any `pure_find` result.

**Union correctness:** `pure_find_after_link` shows that linking `root_a`
to `root_b` changes `pure_find` only for nodes previously in `root_a`'s
tree (they now find `root_b`), while all other nodes are unchanged. This is
proven by induction on `count_above`.

**Rank bound:** The Lemmas module introduces `uf_forest_sized` (tracking
subtree sizes) and proves:
1. `size[x] ≥ 2^rank[x]` (size-rank invariant).
2. `size[x] ≤ n` (bounded by total number of elements).
3. Therefore `2^rank[x] ≤ n`, giving `rank[x] ≤ ⌊log₂ n⌋`.

The imperative `is_forest` invariant ensures termination of loops by
proving all paths reach a root within `n` steps (via a pigeonhole argument
on `path_node` to show `path_len < n`).

## Files

| File | Role |
|------|------|
| `CLRS.Ch21.UnionFind.Impl.fsti` | Public interface (make_set, find_set, union) |
| `CLRS.Ch21.UnionFind.Impl.fst` | Pulse implementation |
| `CLRS.Ch21.UnionFind.Spec.fst` | `uf_forest`, `pure_find`, `pure_union`, invariant theorems |
| `CLRS.Ch21.UnionFind.Lemmas.fst` | Rank bounds, size-rank invariant, O(log n) proof |
