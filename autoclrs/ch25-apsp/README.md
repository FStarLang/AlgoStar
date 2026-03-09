# Chapter 25 — All-Pairs Shortest Paths: Floyd-Warshall

Fully verified Pulse implementation of the Floyd-Warshall algorithm
from CLRS §25.2.  The formalization proves functional correctness
(output == pure DP recurrence), exact Θ(n³) complexity, and the
connection between the imperative-mirroring spec and the classical
`fw_entry` recurrence (CLRS Equation 25.5).

**Verification status:** All modules verify with **zero admits and
zero assumes**.

---

## Summary Table

| Property | Status | Notes |
|---|---|---|
| Functional correctness (`contents' == fw_outer`) | ✅ Fully proven | Impl.fst postcondition |
| `fw_outer` computes `fw_entry` at level n | ✅ Fully proven | `floyd_warshall_computes_shortest_paths` |
| `fw_entry` = classic DP recurrence (Eq. 25.5) | ✅ Fully proven | Direct encoding in Spec.fst |
| `fw_entry` = min walk weight (graph-theoretic) | ✅ Fully proven | `Paths.fst` — achievability + soundness |
| Complexity: exactly n³ relaxation ops | ✅ Proven | `fw_complexity_bounded cf c0 n ≡ cf − c0 == n³` |
| Length preservation across all loops | ✅ Proven | SMT-pattern auto-triggered |
| Concrete test (3×3 graph, all 9 entries) | ✅ Proven | `SpecTest.fst` |
| Pulse runtime test | ✅ | `Test.fst` |
| Negative-cycle detection | ❌ | Assumed via `non_negative_diagonal` precondition |
| Admits | **0** | |
| Assumes | **0** | |

---

## File Inventory

| File | Language | LOC | Role |
|---|---|---|---|
| `CLRS.Ch25.FloydWarshall.Spec.fst` | F* | ~123 | Pure specification: `fw_entry` recurrence, `fw_inner_j/i`, `fw_outer`, safety predicates, length lemmas, complexity bound definition |
| `CLRS.Ch25.FloydWarshall.Lemmas.fsti` | F* | ~107 | Interface for correctness lemma signatures |
| `CLRS.Ch25.FloydWarshall.Lemmas.fst` | F* | ~367 | Correctness proofs: `fw_inner_j_correct`, `fw_inner_i_correct`, `fw_outer_computes_entry`, top-level `floyd_warshall_computes_shortest_paths` |
| `CLRS.Ch25.FloydWarshall.Paths.fst` | F* | ~large | Walk formalism: walk definitions, splitting, concatenation, monotonicity, achievability, soundness, final theorem connecting `fw_entry` to shortest paths |
| `CLRS.Ch25.FloydWarshall.Impl.fsti` | Pulse | ~47 | Interface: `floyd_warshall` signature with correctness + complexity postcondition |
| `CLRS.Ch25.FloydWarshall.Impl.fst` | Pulse | ~156 | Implementation: three nested loops with ghost tick counter |
| `CLRS.Ch25.FloydWarshall.SpecTest.fst` | F* | ~short | Concrete 3×3 test: verifies all 9 output entries |
| `CLRS.Ch25.FloydWarshall.Test.fst` | Pulse | ~short | Pulse compilation/runtime test |

---

## Specification (`Spec.fst`)

### Infinity Sentinel

```fstar
let inf : int = 1000000
```

### FW Recurrence (`fw_entry`)

The classic DP recurrence from CLRS Equation 25.5:

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

Here `k` counts how many vertices have been considered as intermediates:
`k=0` means no intermediates (direct edges), `k=n` means all vertices.

### Imperative-Mirroring Pure Spec

Rather than defining the algorithm declaratively, the spec directly
encodes the loop structure as recursive sequence transformations:

```fstar
let rec fw_inner_j (d: seq int) (n k i j: nat) (d_ik: int)
  : Tot (seq int) (decreases (n - j)) = ...

let rec fw_inner_i (d: seq int) (n k i: nat)
  : Tot (seq int) (decreases (n - i)) = ...

let rec fw_outer (d: seq int) (n k: nat)
  : Tot (seq int) (decreases (n - k)) = ...
```

`fw_inner_j` processes columns, `fw_inner_i` iterates rows,
`fw_outer` iterates intermediate vertices.  The parameter `d_ik` in
`fw_inner_j` is cached (read once before the j-loop), matching the
imperative code.

### Safety Predicates

```fstar
let weights_bounded (d: seq int) (n: nat) : prop = ...
let non_negative_diagonal (d: seq int) (n: nat) : prop = ...
```

`weights_bounded` ensures path sums cannot reach the infinity
sentinel.  `non_negative_diagonal` (no negative self-loops) is
required for the no-negative-cycles assumption.

### Complexity Bound

```fstar
let fw_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n * n * n
```

This is an **exact** bound — not O(n³) but precisely n³ relaxation
operations.

---

## Correctness Theorem — Implementation (`Impl.fsti`)

The EXACT signature from `CLRS.Ch25.FloydWarshall.Impl.fsti`:

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
      SZ.v n > 0 /\
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

**Postcondition analysis:**

1. **`contents' == fw_outer contents (SZ.v n) 0`** — The output array
   exactly equals the pure FW computation applied to the original input.
   This is the functional correctness guarantee.

2. **`fw_complexity_bounded cf (reveal c0) (SZ.v n)`** — The ghost
   counter increased by exactly n³.  Since exactly one `tick` is called
   per relaxation (inner j-loop body), this proves Θ(n³) operations.

3. **`Seq.length contents' == SZ.v n * SZ.v n`** — Array size preserved.

### Why This Is the Strongest Functional Guarantee

- **Full equivalence to pure spec**, not just "some correct answer".
  The output is definitionally equal to `fw_outer contents n 0`.
- **Exact complexity**, not just big-O.  Every iteration performs
  exactly one relaxation, and all three loop bounds are tight.
- The Lemmas module further proves `fw_outer ≡ fw_entry`, connecting
  the imperative-mirroring spec to the declarative DP recurrence.
- The Paths module proves `fw_entry` equals the minimum walk weight,
  completing the chain: imperative → mirroring spec → DP recurrence →
  shortest paths.

---

## Correctness Lemmas (`Lemmas.fst`)

### Main Theorem

```fstar
val floyd_warshall_computes_shortest_paths
  (adj: seq int) (n: nat) (qi qj: nat)
  : Lemma
    (requires length adj == n * n /\ n > 0 /\ qi < n /\ qj < n /\
      (forall (k: nat) (v: nat). k <= n /\ v < n ==> fw_entry adj n v v k >= 0))
    (ensures
      index (fw_outer adj n 0) (qi * n + qj) == fw_entry adj n qi qj n)
```

This connects the mirroring spec (`fw_outer`) to the declarative
recurrence (`fw_entry`).

### Supporting Lemmas

- **`lemma_fw_inner_j_correct`**: After `fw_inner_j`, entry `[i,j']` =
  `min(d[i,j'], d_ik + d[k,j'])` for `j' ≥ j`.
- **`lemma_fw_inner_j_other_pos`**: `fw_inner_j` only modifies row `i`.
- **`lemma_fw_inner_i_preserves_row_k`**: Row `k` is unchanged through
  the i-loop (critical for the cached `d_ik` correctness).
- **`lemma_fw_inner_i_correct`**: After processing row `i`, entry
  `[qi, qj]` = `min(d[qi,qj], d[qi,k] + d[k,qj])`.
- **`fw_outer_computes_entry`**: Inductive proof that `fw_outer`
  computes `fw_entry` at all levels.

---

## Walk Formalism (`Paths.fst`)

The Paths module connects `fw_entry` to graph-theoretic shortest paths:

1. **Walk definitions**: `is_walk`, `walk_weight`, `walk_valid`,
   `walk_restricted` (intermediate vertices in `{0..k-1}`).
2. **Soundness**: `fw_entry adj n i j k ≤ walk_weight(w)` for all
   valid restricted walks `w`.
3. **Achievability**: there exists a walk `w` with
   `walk_weight(w) == fw_entry adj n i j k`.
4. **Final theorem**: `fw_entry adj n i j n` equals the minimum walk
   weight over all valid walks — i.e., the true shortest-path distance
   δ(i,j).

This module is **fully proven with zero admits**.

---

## Complexity

The complexity bound is **exact** (Θ(n³)), not merely asymptotic:

```fstar
let fw_complexity_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n * n * n
```

The proof uses a *linear cost decomposition* across the three loops:

- **Outer loop**: after `vk` iterations, exactly `vk * n * n` ticks.
- **Middle loop**: adds `vi * n` ticks per row.
- **Inner loop**: adds 1 tick per column.
- Arithmetic identity: `vk * n² + n² = (vk + 1) * n²` discharged by SMT.

The ghost tick counter (`GR.ref nat`) is completely erased at runtime.

| Aspect | Proven | Bound |
|---|---|---|
| Relaxation operations | ✅ Exact | n³ (not "O(n³)" — exactly n³) |
| Ghost tick mechanism | ✅ | `GR.ref nat`, erased at extraction |
| Runtime overhead | None | Ghost references compile to nothing |

---

## Limitations

1. **Negative-cycle detection not implemented.** The precondition
   `non_negative_diagonal` (and the stronger condition that `fw_entry`
   diagonal entries remain non-negative at all levels) is assumed, not
   checked at runtime.  If the input contains negative cycles, the
   algorithm will silently produce incorrect results.

2. **Fixed infinity sentinel.** The sentinel value `1000000` is
   hardcoded.  Graphs with edge weights approaching this value may
   produce incorrect results due to integer overflow in path sums.
   The `weights_bounded` predicate guards against this but is a
   precondition, not a runtime check.

3. **No predecessor matrix.** CLRS §25.2 also describes maintaining a
   predecessor matrix Π to reconstruct shortest paths.  This is not
   implemented — only shortest-path *weights* are computed.

4. **In-place update.** The algorithm overwrites the input distance
   matrix.  The original input is available only as a ghost value
   (`#contents`).

---

## Proof Techniques

1. **Imperative-mirroring specification**: The pure spec directly
   encodes the loop structure.  This makes the refinement proof between
   implementation and spec nearly trivial — each loop iteration is one
   unfolding of the corresponding recursive function.

2. **Remaining-work invariants**: Instead of tracking "what I've done
   so far", invariants assert that "applying remaining work to current
   state = applying all work to initial state".  Loop-exit reasoning
   is immediate (remaining work is the identity).

3. **Cached reads matching the spec**: The imperative code reads
   `d[i][k]` once before the j-loop.  The pure spec takes `d_ik` as a
   parameter for the same reason — if the spec re-read `d[i][k]`
   inside the j-loop, it could observe intermediate updates.

4. **Unconditional writes**: Always writes `min(d[i][j], d[i][k] + d[k][j])`
   rather than conditionally.  This avoids branching on ghost state in
   Pulse.

5. **Exact complexity via decomposition**: Cost decomposes as
   `vk * n² + vi * n + vj` across the three loops.

6. **Ghost erasure**: Both `#contents` and the tick counter are ghost
   values, fully erased at runtime.

---

## CLRS Section Mapping

| CLRS Section | Content | Module |
|---|---|---|
| §25.2 | Floyd-Warshall algorithm | `Impl.fst` |
| Equation 25.5 | DP recurrence d^(k)[i][j] | `Spec.fst` (`fw_entry`) |
| §25.2 | Matrix representation | `Spec.fst` (flat array, row-major) |
| §25.1 | Shortest paths and walks | `Paths.fst` |

---

## Build Instructions

```bash
cd ch25-apsp
make    # Verifies all modules
```

## Example

See `CLRS.Ch25.FloydWarshall.SpecTest.fst` for a complete 3×3 test:

```
Input:                After Floyd-Warshall:
  0   5  inf            0   5   20
 50   0   15           45   0   15
 30  inf  0            30  35   0
```

All 9 output entries are verified by the SMT solver.
