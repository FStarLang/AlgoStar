# Rod Cutting (CLRS §15.1)

## Top-Level Signature

Here is the top-level signature proven about Rod Cutting in
`CLRS.Ch15.RodCutting.Impl.fsti`:

```fstar
fn rod_cutting
  (#p: perm)
  (prices: A.array nat)
  (n: SZ.t)
  (#s_prices: erased (Seq.seq nat))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to prices #p s_prices **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s_prices /\
      SZ.v n == A.length prices /\
      SZ.fits (SZ.v n + 1)
    )
  returns result: nat
  ensures exists* (cf: nat).
    A.pts_to prices #p s_prices **
    GR.pts_to ctr cf **
    pure (
      result == optimal_revenue s_prices (SZ.v n) /\
      rod_cutting_bounded cf (reveal c0) (SZ.v n)
    )
```

### Parameters

* `prices` is a read-only array of `nat` (the `#p: perm` allows shared
  access). `s_prices` is the ghost snapshot, where `prices[i]` is the price
  for a piece of length `i+1`.

* `n` is the rod length, of type `SZ.t` (machine-sized integer).

* `ctr` is a ghost counter for tracking the number of inner-loop iterations.
  Initial value is `c0`.

### Preconditions

* `SZ.v n == Seq.length s_prices`: The length parameter matches the price
  array length.

* `SZ.v n == A.length prices`: Physical array length matches.

* `SZ.fits (SZ.v n + 1)`: The DP table of size `n+1` fits in machine
  integers.

Note: No `n > 0` precondition — the implementation correctly handles the
empty rod case (`n = 0`), returning 0.

### Postcondition

The `ensures` clause states that there exists a final counter value `cf`
such that:

* `result == optimal_revenue s_prices (SZ.v n)` — The result is the optimal
  revenue for a rod of length `n`.

* `rod_cutting_bounded cf (reveal c0) (SZ.v n)` — The number of inner-loop
  iterations is exactly `n(n+1)/2`.

## Auxiliary Definitions

### `optimal_revenue` (from `CLRS.Ch15.RodCutting.Spec`)

```fstar
let optimal_revenue (prices: seq nat) (j: nat) : nat =
  index (build_opt prices j) j
```

This is defined via a bottom-up DP table `build_opt`, which recursively
builds a sequence of length `j+1` where entry `k` is the optimal revenue
for a rod of length `k`. The recurrence uses `accum_max`, which takes the
maximum over all first-cut positions `i ∈ [1,j]` of
`prices[i-1] + r[j-i]`.

### `rod_cutting_bounded` (from `CLRS.Ch15.RodCutting.Impl.fsti`)

```fstar
let triangle (n: nat) : nat = op_Multiply n (Prims.op_Addition n 1) / 2

let rod_cutting_bounded (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == triangle n
```

This says the total number of inner-loop iterations is exactly `n(n+1)/2`.
This is the **exact count**, not just an upper bound: the inner loop runs
`j` iterations for each outer iteration `j = 1, ..., n`, giving
`1 + 2 + ... + n = n(n+1)/2`.

### `valid_cutting` and `cutting_revenue` (from `CLRS.Ch15.RodCutting.Spec`)

```fstar
let rec valid_cutting (n: nat) (cuts: list nat) : prop =
  match cuts with
  | [] -> n = 0
  | piece :: rest -> piece > 0 /\ piece <= n /\ valid_cutting (n - piece) rest

let rec cutting_revenue (prices: seq nat) (cuts: list nat) : nat =
  match cuts with
  | [] -> 0
  | piece :: rest ->
    if piece > 0 && piece - 1 < length prices
    then index prices (piece - 1) + cutting_revenue prices rest
    else 0 + cutting_revenue prices rest
```

A cutting is a list of positive piece sizes summing to `n`. Revenue is the
sum of prices for each piece.

### `dp_correct` (from `CLRS.Ch15.RodCutting.Spec`)

```fstar
let dp_correct (prices: seq nat) (sr: seq nat) (bound: nat) : prop =
  (forall (k: nat). k <= bound /\ k < length sr ==>
    index sr k == optimal_revenue prices k)
```

The loop invariant: the first `bound+1` entries of the DP table match
`optimal_revenue`.

## What Is Proven

The postcondition `result == optimal_revenue s_prices (SZ.v n)` states that
the imperative bottom-up DP computation returns the **exact optimal revenue**
as defined by the pure recursive specification.

The specification is further validated by the lemmas in
`CLRS.Ch15.RodCutting.Lemmas`:

* **Optimal substructure** (`optimal_substructure`): The recurrence
  `optimal_revenue(n) = max_{1≤i≤n}(prices[i-1] + optimal_revenue(n-i))`
  is proven equivalent to `build_opt`.

* **Upper bound** (`cutting_revenue_le_optimal`): For every valid cutting,
  `cutting_revenue ≤ optimal_revenue`.

* **Achievability** (`construct_optimal_cutting`): There exists a cutting
  whose revenue equals `optimal_revenue`.

Together, these establish that `optimal_revenue` truly is the maximum over
all valid cuttings — the **strongest possible correctness specification**.

The complexity bound `cf - c0 == n(n+1)/2` is the **exact iteration count**,
proven by threading a ghost counter through the Pulse implementation.

**Extended variant.** `CLRS.Ch15.RodCutting.Extended` proves the same
correctness plus `cuts_are_optimal`: each `cuts[j]` is a valid first piece
`1 ≤ cuts[j] ≤ j` such that
`prices[cuts[j]-1] + optimal_revenue(j - cuts[j]) == optimal_revenue(j)`.
It also proves `reconstruct_cutting_sums`: following the cuts array produces
pieces that sum to `j`.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. ~~**`n > 0` precondition.**~~ **RESOLVED.** The implementation now
   handles `n = 0` (empty rod). The outer loop naturally does not execute
   when `n = 0`, and `r[0] = 0 = optimal_revenue prices 0`. The `n > 0`
   precondition has been removed from both the basic and extended variants.

2. **`n ≤ |prices|` implicit assumption.** The specification defines
   `optimal_revenue` for any `n`, but if `n > |prices|`, `build_opt`
   returns 0 for lengths exceeding the price table. The implementation
   requires `n == |prices|`, so this is not an issue in practice, but the
   spec could be clearer about this boundary.

3. **Integer-valued prices only.** Prices are `nat` (non-negative
   integers). The specification does not handle fractional prices or
   negative prices.

4. **Hardcoded sentinel.** The Matrix Chain implementation uses a sentinel
   value `1000000000`, but Rod Cutting does not — it correctly initializes
   `q = 0` and takes the max. This is noted as a positive: no sentinel
   dependency.

5. **No best-case complexity.** The complexity is exactly `n(n+1)/2`
   regardless of input — the algorithm always explores all subproblems.
   This matches CLRS's bottom-up approach.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Inner-loop iterations | O(n²) = n(n+1)/2 | ✅ Ghost counter | Exact count |

The complexity is **fully linked** to the imperative implementation: the
ghost counter `ctr` is incremented once per inner-loop iteration in the
Pulse code, and the postcondition directly constrains `cf - c0`.

## Proof Structure

The proof uses an outer loop invariant maintaining `dp_correct s_prices sr
(vj - 1)`: after processing `j`, all entries `r[0..j]` equal
`optimal_revenue`. The inner loop computes `accum_max` by scanning
`i = 1, ..., j`. The key bridge lemma `accum_max_dp_correct` shows that
when the DP table is correct for indices `< j`, the `accum_max` computation
over the table equals `optimal_revenue(j)`.

## Profiling & Proof Stability

| File | z3rlimit | Build time | Assessment |
|------|----------|------------|------------|
| `RodCutting.Spec.fst` | default | ~5s | ✅ Fast |
| `RodCutting.Lemmas.fst` | default | ~30s | ✅ Good |
| `RodCutting.Impl.fst` | 50, fuel 2, ifuel 2 | ~30s | ✅ Good |
| `RodCutting.Extended.fst` | 80 (base), 200 (localized) | **~2 min** | ✅ Improved (was 400/7min) |
| `RodCutting.Test.fst` | default | ~3s | ✅ Fast |

The Extended variant's proof stability was improved by localizing rlimits:
the monolithic z3rlimit 400 was split into z3rlimit 80 for most of the file
and z3rlimit 200 for a single lemma (`cuts_optimal_from_dp`), reducing build
time from ~7 minutes to ~2 minutes. The inner loop still has a missing
`decreases` clause (TODO at line 463).

## Files

| File | Lines | Role |
|------|-------|------|
| `CLRS.Ch15.RodCutting.Impl.fsti` | 48 | Public interface (this signature) |
| `CLRS.Ch15.RodCutting.Impl.fst` | 164 | Pulse implementation with ghost counter |
| `CLRS.Ch15.RodCutting.Spec.fst` | 155 | `optimal_revenue`, `accum_max`, `dp_correct`, `build_opt` |
| `CLRS.Ch15.RodCutting.Lemmas.fsti` | 75 | Lemma signatures (optimal substructure, achievability) |
| `CLRS.Ch15.RodCutting.Lemmas.fst` | 172 | Lemma proofs |
| `CLRS.Ch15.RodCutting.Extended.fst` | 560 | Extended variant with cuts array |
| `CLRS.Ch15.RodCutting.Test.fst` | 55 | Test cases (CLRS example) |

## Checklist

- [x] Spec.fst — pure specification with `optimal_revenue`, `build_opt`
- [x] Lemmas.fst / .fsti — optimal substructure, upper bound, achievability
- [x] Impl.fst / .fsti — Pulse implementation with correctness + complexity
- [x] Extended.fst — EXTENDED-BOTTOM-UP-CUT-ROD with cuts array
- [x] Test.fst — CLRS example test
- [x] Zero admits, zero assumes
- [x] Complexity linked via ghost counter (exact n(n+1)/2)
- [x] Reduce z3rlimit in Extended.fst (400 → 80/200 localized, ~2 min)
- [ ] Add `decreases` clause to Extended.fst inner loop (line 463 TODO)
