# Floyd-Warshall All-Pairs Shortest Paths (CLRS §25.2)

## Top-Level Signature

Here is the top-level signature proven about Floyd-Warshall in
`CLRS.Ch25.FloydWarshall.Impl.fsti`:

```fstar
fn floyd_warshall
  (dist: array int)
  (#contents: Ghost.erased (Seq.seq int))
  (n: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to dist contents **
    GR.pts_to ctr c0 **
    pure (
      Seq.length contents == SZ.v n * SZ.v n /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  returns _:unit
  ensures exists* contents' (cf: nat).
    A.pts_to dist contents' **
    GR.pts_to ctr cf **
    pure (
      Seq.length contents' == SZ.v n * SZ.v n /\
      contents' == fw_outer contents (SZ.v n) 0 /\
      fw_complexity_bounded cf (reveal c0) (SZ.v n)
    )
```

### Parameters

* `dist` is a mutable flat `n×n` distance matrix of `int`. The ghost variable
  `contents` captures the initial contents (adjacency weights).

* `n` is the number of vertices, of type `SZ.t`.

* `ctr` is a **ghost counter** — a ghost reference to a natural number used to
  count relaxation operations. The initial value is `c0`.

### Preconditions

* `Seq.length contents == SZ.v n * SZ.v n`: Distance matrix is properly sized.
* `SZ.fits (SZ.v n * SZ.v n)`: No `SZ.t` overflow.

Note: The `SZ.v n > 0` precondition has been removed — Floyd-Warshall now
handles the empty graph (n = 0) trivially.

### Postcondition

The `ensures` clause states that there exist a final sequence `contents'` and
a final counter value `cf` such that:

* `Seq.length contents' == SZ.v n * SZ.v n` — Output has the same size.

* `contents' == fw_outer contents (SZ.v n) 0` — The output **equals** the pure
  functional FW computation applied to the input. This is a **functional
  refinement**: the imperative code computes exactly the same result as the
  mathematical specification.

* `fw_complexity_bounded cf (reveal c0) (SZ.v n)` — The number of relaxation
  operations is exactly n³.

## Auxiliary Definitions

### `fw_outer`, `fw_inner_i`, `fw_inner_j` (from `CLRS.Ch25.FloydWarshall.Spec`)

```fstar
let rec fw_inner_j (d: seq int) (n k i j: nat) (d_ik: int) 
  : Tot (seq int) (decreases (n - j)) =
  if j >= n || i >= n || k >= n || length d <> n * n then d
  else
    let d_ij = index d (i * n + j) in
    let d_kj = index d (k * n + j) in
    let via_k = d_ik + d_kj in
    let new_val = if via_k < d_ij then via_k else d_ij in
    fw_inner_j (upd d (i * n + j) new_val) n k i (j + 1) d_ik

let rec fw_inner_i (d: seq int) (n k i: nat) 
  : Tot (seq int) (decreases (n - i)) =
  if i >= n || k >= n || length d <> n * n then d
  else
    let d_ik = index d (i * n + k) in
    fw_inner_i (fw_inner_j d n k i 0 d_ik) n k (i + 1)

let rec fw_outer (d: seq int) (n k: nat) 
  : Tot (seq int) (decreases (n - k)) =
  if k >= n || length d <> n * n then d
  else fw_outer (fw_inner_i d n k 0) n (k + 1)
```

The pure specification mirrors the imperative triple-nested loop exactly: outer
loop over intermediate vertices `k`, middle loop over rows `i`, inner loop over
columns `j`. Each step computes `d[i][j] = min(d[i][j], d[i][k] + d[k][j])`.
The `d_ik` value is cached (read once per row), matching the CLRS optimization.

### `fw_entry` (from `CLRS.Ch25.FloydWarshall.Spec`)

```fstar
let rec fw_entry (adj: seq int) (n: nat) (i j k: nat)
  : Tot int (decreases k)
  = if i >= n || j >= n || length adj <> n * n then inf
    else if k = 0 then index adj (i * n + j)
    else
      let without = fw_entry adj n i j (k - 1) in
      let d_ik = fw_entry adj n i (k - 1) (k - 1) in
      let d_kj = fw_entry adj n (k - 1) j (k - 1) in
      let via_k = d_ik + d_kj in
      if via_k < without then via_k else without
```

This is the **CLRS Equation 25.5** recurrence: `d^(k)[i][j] = min(d^(k-1)[i][j],
d^(k-1)[i][k-1] + d^(k-1)[k-1][j])`. It defines shortest-path distances
using only vertices `{0, ..., k-1}` as intermediates.

### `fw_complexity_bounded` (from `CLRS.Ch25.FloydWarshall.Spec`)

```fstar
let fw_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n * n * n
```

This says the total number of relaxation operations is **exactly** n³. Note the
use of `==` (equality), not `<=` (upper bound). This is **Θ(n³)**, not merely
O(n³) — the triple loop always executes all `n × n × n` iterations regardless
of input.

### `weights_bounded` and `non_negative_diagonal` (from `CLRS.Ch25.FloydWarshall.Spec`)

```fstar
let weights_bounded (d: seq int) (n: nat) : prop =
  length d == n * n /\
  (forall (i: nat). i < n * n ==>
    (index d i >= 0 /\ (index d i < inf ==> index d i <= inf / n)))

let non_negative_diagonal (d: seq int) (n: nat) : prop =
  length d == n * n /\
  (forall (v: nat). v < n ==> index d (v * n + v) >= 0)
```

Safety predicates ensuring no arithmetic overflow during path-sum computation,
and no negative self-loops (required for the no-negative-cycles assumption).

## Correctness Chain

### `floyd_warshall_computes_shortest_paths` (from `CLRS.Ch25.FloydWarshall.Lemmas`)

```fstar
val floyd_warshall_computes_shortest_paths
  (adj: seq int) (n: nat) (qi qj: nat)
  : Lemma
    (requires
      length adj == n * n /\ n > 0 /\ qi < n /\ qj < n /\
      (forall (k: nat) (v: nat). k <= n /\ v < n ==> fw_entry adj n v v k >= 0))
    (ensures
      index (fw_outer adj n 0) (qi * n + qj) == fw_entry adj n qi qj n)
```

**Key link:** The imperative-mirroring spec `fw_outer` computes exactly the
recurrence `fw_entry` at level `n`. Combined with the Pulse postcondition
`contents' == fw_outer contents n 0`, this gives: the output matrix entry
`(qi, qj)` equals `fw_entry adj n qi qj n`.

### Graph-Theoretic Soundness (`CLRS.Ch25.FloydWarshall.Paths`)

```fstar
let fw_entry_leq_any_walk
  (adj: Seq.seq int) (n: nat) (i j: nat) (w: list nat)
  : Lemma
    (requires ...)
    (ensures fw_entry adj n i j n <= walk_weight adj n w)

let fw_entry_eq_some_walk
  (adj: Seq.seq int) (n: nat) (i j: nat)
  : Lemma
    (requires ...)
    (ensures exists (w: list nat). ... /\ walk_weight adj n w == fw_entry adj n i j n)
```

* `fw_entry_leq_any_walk`: `fw_entry` is ≤ the weight of any valid walk
  (soundness — no walk is cheaper).
* `fw_entry_eq_some_walk`: There exists a walk achieving `fw_entry`'s value
  (completeness — the value is attainable).

Together, these prove `fw_entry adj n i j n` is the **true shortest walk
weight** from `i` to `j`. The `Paths` module formalizes walks, walk splitting,
walk restriction to intermediate vertex sets, and cycle stripping.

## What Is Proven

The postcondition `contents' == fw_outer contents n 0` is the **strongest
possible functional correctness specification** for Floyd-Warshall: the
imperative code is proven to compute exactly the same sequence as the pure
mathematical definition. No approximation, no rounding, no off-by-one.

The complexity bound `cf - c0 == n³` is **exact** (Θ(n³)), not an upper bound.
The ghost counter is incremented inside the innermost loop of the Pulse code.

The correctness chain is:
1. `contents' == fw_outer contents n 0` (Pulse postcondition)
2. `fw_outer` computes `fw_entry` at level `n` (Lemmas)
3. `fw_entry` equals shortest walk weight (Paths)

**Zero admits, zero assumes.** All proof obligations in `Impl.fst`, `Spec.fst`,
`Lemmas.fst`, and `Paths.fst` are discharged by F\* and Z3.

## Specification Gaps and Limitations

1. ~~**No negative-cycle detection.**~~ **RESOLVED.** A `check_no_negative_cycle`
   Pulse function is provided in `NegCycleDetect.fst`. It scans the diagonal of
   the output matrix and proves: if the check passes (returns `true`), the
   output satisfies `non_negative_diagonal`. Additionally,
   `lemma_weights_bounded_nonneg_entry` in `Spec.fst` proves that when
   `weights_bounded` holds, all `fw_entry` values (including diagonal entries at
   every level) are non-negative — so no negative cycles can exist. The combined
   theorem `floyd_warshall_full_correctness` in `Lemmas.fst` derives the full
   correctness chain from `weights_bounded` alone, without requiring the
   intermediate `fw_entry` diagonal invariant as a separate precondition.

2. **No predecessor matrix.** CLRS §25.2 also describes computing a
   predecessor matrix Π for path reconstruction. This implementation only
   computes distances, not actual paths.

3. **Infinity sentinel.** `inf = 1000000` is a finite sentinel. The safety
   predicate `weights_bounded` ensures no overflow, but the specification
   conflates "unreachable" with "weight = 1000000". A more robust formalization
   would use `option int` or a dedicated infinity type.

4. ~~**Precondition: `SZ.v n > 0`.**~~ **RESOLVED.** The `SZ.v n > 0`
   precondition has been removed from `floyd_warshall`. The empty graph (n = 0)
   is now handled: the loops never execute, the output equals the input
   (`fw_outer d 0 0 == d`), and the complexity is 0³ = 0. A test
   `test_empty_graph` in `Test.fst` exercises this path.

5. ~~**`weights_bounded` is not in the Pulse precondition.**~~ **RESOLVED.**
   A `floyd_warshall_safe` wrapper in `NegCycleDetect.fst` provides a function
   with `weights_bounded` and `non_negative_diagonal` in its precondition,
   closing the gap between what the correctness proofs require and what the
   Pulse function enforces. The original `floyd_warshall` retains its minimal
   precondition for maximum flexibility.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Relaxations | Θ(n³) = n·n·n | ✅ Ghost counter | **Exact** (==, not ≤) |

The complexity is **fully linked** to the imperative implementation: the ghost
counter `ctr` is incremented inside the innermost relaxation loop of the Pulse
code, and the postcondition directly constrains `cf - c0 == n * n * n`. This is
the tightest possible bound — it is exact, not an approximation.

## Proof Structure

The proof has four layers:

1. **Spec layer** (`Spec.fst`): Defines `fw_inner_j`, `fw_inner_i`, `fw_outer`
   (imperative-mirroring), `fw_entry` (recurrence), safety predicates, length
   preservation lemmas, and `lemma_weights_bounded_nonneg_entry` (proves all
   `fw_entry` values are non-negative when `weights_bounded` holds). Zero admits.

2. **Lemma layer** (`Lemmas.fst`): Proves `fw_outer` computes `fw_entry` via
   induction. Key results: `fw_inner_j_correct`, `fw_inner_i_correct`,
   `fw_inner_i_preserves_row_k`, `fw_outer_computes_entry`, and
   `floyd_warshall_full_correctness` (combined theorem deriving correctness
   from `weights_bounded` alone). Zero admits.

3. **Path layer** (`Paths.fst`): Graph-theoretic formalization of walks,
   intermediate vertex restriction, walk splitting, cycle stripping. Proves
   `fw_entry` is the shortest walk weight. Structured in 9 sections. Zero
   admits.

4. **Detection layer** (`NegCycleDetect.fst`): Pulse implementation of
   `check_no_negative_cycle` (runtime diagonal check) and `floyd_warshall_safe`
   (wrapper with `weights_bounded` + `non_negative_diagonal` preconditions).
   Zero admits.

## Files

| File | Role |
|------|------|
| `CLRS.Ch25.FloydWarshall.Impl.fsti` | Public interface (this signature) |
| `CLRS.Ch25.FloydWarshall.Impl.fst` | Pulse implementation |
| `CLRS.Ch25.FloydWarshall.Spec.fst` | Pure spec: `fw_outer`, `fw_entry`, safety predicates, non-negativity lemma |
| `CLRS.Ch25.FloydWarshall.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch25.FloydWarshall.Lemmas.fst` | Correctness proofs: `fw_outer` computes `fw_entry`, full correctness theorem |
| `CLRS.Ch25.FloydWarshall.Paths.fst` | Graph-theoretic shortest path proofs |
| `CLRS.Ch25.FloydWarshall.NegCycleDetect.fst` | Negative-cycle detection + safe wrapper |
| `CLRS.Ch25.FloydWarshall.SpecTest.fst` | Test cases for the specification |
| `CLRS.Ch25.FloydWarshall.Test.fst` | Test cases for the implementation |
