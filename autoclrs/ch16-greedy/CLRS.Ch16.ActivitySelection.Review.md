# Activity Selection (CLRS §16.1)

## Top-Level Signature

Here is the top-level signature proven about Activity Selection in
`CLRS.Ch16.ActivitySelection.Impl.fsti`:

```fstar
fn activity_selection 
  (#p: perm)
  (start_times finish_times: A.array int) 
  (out: A.array SZ.t)
  (n: SZ.t)
  (#ss #sf: Ghost.erased (Seq.seq int))
  (#sout0: Ghost.erased (Seq.seq SZ.t))
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires 
    A.pts_to start_times #p ss ** A.pts_to finish_times #p sf **
    A.pts_to out sout0 **
    GR.pts_to ctr c0 **
    pure (activity_selection_pre n ss sf sout0 start_times finish_times out)
  returns count: SZ.t
  ensures exists* sout (cf: nat).
    A.pts_to start_times #p ss ** 
    A.pts_to finish_times #p sf **
    A.pts_to out sout **
    GR.pts_to ctr cf **
    pure (activity_selection_post count n sout cf (reveal c0) ss sf)
```

### Parameters

* `start_times`, `finish_times` are read-only arrays of `int` — start and
  finish times for `n` activities.

* `out` is a mutable output array where selected activity indices are written.

* `n` is the number of activities.

* `ctr` is a ghost counter for comparisons.

### Preconditions (from `activity_selection_pre`)

```fstar
let activity_selection_pre (n: SZ.t) (ss sf: Seq.seq int) (sout0: Seq.seq SZ.t)
  (start_times finish_times: A.array int) (out: A.array SZ.t) : prop =
  SZ.v n == Seq.length ss /\ SZ.v n == Seq.length sf /\
  SZ.v n == A.length start_times /\ SZ.v n == A.length finish_times /\
  SZ.v n == A.length out /\ SZ.v n == Seq.length sout0 /\
  L.finish_sorted sf /\
  (forall (i:nat). i < Seq.length ss ==> L.valid_activity ss sf i)
```

* Activities sorted by finish time (`finish_sorted`).
* All activities valid: `start[i] < finish[i]`.
* No minimum activity count required — `n = 0` is handled.

### Postconditions (from `activity_selection_post`)

```fstar
let activity_selection_post
  (count: SZ.t) (n: SZ.t) (sout: Seq.seq SZ.t) (cf: nat) (c0: nat) (ss sf: Seq.seq int)
: prop =
  SZ.v count <= SZ.v n /\
  Seq.length sout == SZ.v n /\
  cf >= c0 /\
  SZ.v count == S.max_compatible_count ss sf (SZ.v n) /\
  (SZ.v n == 0 ==> SZ.v count == 0 /\ cf == c0) /\
  (SZ.v n > 0 ==>
    SZ.v count >= 1 /\
    complexity_bounded_linear cf c0 (SZ.v n) /\
    (exists (sel: Seq.seq nat).
      Seq.length sel == SZ.v count /\
      out_matches_sel sout sel (SZ.v count) (SZ.v n) /\
      L.all_valid_indices sel (SZ.v n) /\
      L.strictly_increasing sel /\
      L.pairwise_compatible sel ss sf /\
      Seq.index sel 0 == 0 /\
      L.earliest_compatible sel ss sf (SZ.v n) (SZ.v n)))
```

The postcondition guarantees:

* `count <= n` — never selects more activities than exist.
* `count == max_compatible_count` — **optimality** (for all n, including 0).
* When `n = 0`: `count == 0` and zero comparisons (`cf == c0`).
* When `n > 0`:
  - `count >= 1` — at least one activity is selected.
  - `complexity_bounded_linear cf c0 n` — exactly `n-1` comparisons.
  - A ghost selection sequence `sel` witnessing:
    - Selected indices are valid, strictly increasing, and pairwise compatible.
    - Activity 0 is always selected first.
    - Each selected activity is the **earliest compatible** one.

## Auxiliary Definitions

### `pairwise_compatible` (from `CLRS.Ch16.ActivitySelection.Lemmas`)

```fstar
let pairwise_compatible (sel: seq nat) (s f: seq int) : prop =
  (forall (i: nat). i < Seq.length sel ==> Seq.index sel i < Seq.length s /\ Seq.index sel i < Seq.length f) /\
  (forall (i: nat). i + 1 < Seq.length sel ==>
    Seq.index f (Seq.index sel i) <= Seq.index s (Seq.index sel (i + 1)))
```

Consecutive selected activities are non-overlapping: finish of current ≤
start of next.

### `earliest_compatible` (from `CLRS.Ch16.ActivitySelection.Lemmas`)

```fstar
let earliest_compatible (sel: seq nat) (s f: seq int) (n: nat) (processed: nat) : prop =
  Seq.length sel >= 1 /\
  (forall (i: nat). i + 1 < Seq.length sel ==>
    (forall (z: nat). Seq.index sel i < z /\ z < Seq.index sel (i + 1) /\
                       z < n /\ z < Seq.length s /\ z < Seq.length f ==>
      Seq.index s z < Seq.index f (Seq.index sel i))) /\
  (forall (z: nat). Seq.index sel (Seq.length sel - 1) < z /\ z < processed /\
                     z < n /\ z < Seq.length s /\ z < Seq.length f ==>
    Seq.index s z < Seq.index f (Seq.index sel (Seq.length sel - 1)))
```

Between any two consecutive selections, every skipped activity is
incompatible with the previous selection (its start is before the previous
finish).

### `max_compatible_count` (from `CLRS.Ch16.ActivitySelection.Spec`)

```fstar
[@@"opaque_to_smt"]
let max_compatible_count (start: Seq.seq int) (finish: Seq.seq int) (n: nat) : GTot nat =
  find_max_compatible start finish n n
```

The maximum cardinality of any mutually compatible subset. Defined by
searching downward from `n` for the largest `k` such that a compatible set
of size `k` exists. Marked `opaque_to_smt` for proof performance.

### `complexity_bounded_linear` (from `CLRS.Ch16.ActivitySelection.Complexity`)

```fstar
let complexity_bounded_linear (cf c0 n: nat) : prop =
  cf >= c0 /\ cf - c0 == n - 1
```

Exactly `n-1` comparisons — one per candidate activity after activity 0.

## What Is Proven

The postcondition establishes the **strongest possible specification** for
greedy activity selection:

1. **Functional correctness**: The selected activities are pairwise
   compatible and form a valid selection.

2. **Greedy optimality**: `count == max_compatible_count` — the greedy
   algorithm achieves the maximum cardinality. This is proven via:
   - **Greedy choice property** (`lemma_greedy_choice`): Any optimal
     solution can be modified to include activity 0 without losing
     optimality. Proven by exchange argument: since activities are sorted
     by finish time, `f[0] ≤ f[k]` for any first selected activity `k`,
     so replacing `k` with `0` preserves compatibility.
   - **Optimal substructure**: After selecting the earliest-finishing
     activity, the remaining problem has optimal substructure.
   - **Main theorem** (`theorem_implementation_optimal`): The greedy
     selection satisfying `earliest_compatible` is an optimal selection.

3. **Complexity**: Exactly `n-1` comparisons.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. ~~**`n > 0` precondition.**~~ **ADDRESSED.** The algorithm now handles
   `n = 0` by returning 0 (trivially optimal). The precondition no longer
   requires `SZ.v n > 0`, and the postcondition is structured conditionally:
   for `n = 0`, it asserts `count == 0` with zero comparisons; for `n > 0`,
   the full greedy optimality proof applies.

2. **Pre-sorted input required.** The precondition requires
   `finish_sorted sf`. The algorithm itself is O(n) for sorted input, but
   CLRS notes that the sorting step is O(n log n). The sorting is not part
   of this implementation.

3. **Activity 0 always selected.** The postcondition asserts
   `Seq.index sel 0 == 0` — the earliest-finishing activity is always
   selected. This is correct by the greedy choice property but means the
   algorithm is not parametric over which activity to start with.

4. **Output format.** Selected indices are written to the first `count`
   positions of the `out` array. The remaining positions are unspecified.
   The ghost `sel` sequence witnesses correctness, but the correspondence
   `out_matches_sel` only covers positions `< count`.

5. **`max_compatible_count` uses `StrongExcludedMiddle`.** The definition
   of `find_max_compatible` uses `FStar.StrongExcludedMiddle.strong_excluded_middle`
   to search for the existence of a compatible set of a given size. This is
   a specification-level axiom (consistent with F\*'s logic) that does not
   affect extracted code but is a non-constructive element in the spec.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Comparisons | O(n) = n−1 | ✅ Ghost counter | Exact count |

The complexity is **fully linked** to the imperative implementation: the
ghost counter `ctr` is incremented once per candidate activity (activities
1 through n-1), giving exactly `n-1` comparisons.

## Proof Structure

The Pulse proof maintains the `greedy_selection_inv` invariant through the
main loop:

```fstar
let greedy_selection_inv (sel: seq nat) (s f: seq int) (n: nat) (processed: nat) (last_finish: int) : prop =
  Seq.length sel >= 1 /\
  all_valid_indices sel n /\
  strictly_increasing sel /\
  pairwise_compatible sel s f /\
  (forall (i: nat). i < Seq.length sel ==> Seq.index sel i < processed) /\
  Seq.index sel (Seq.length sel - 1) < Seq.length f /\
  Seq.index f (Seq.index sel (Seq.length sel - 1)) == last_finish /\
  Seq.index sel 0 == 0 /\
  earliest_compatible sel s f n processed
```

At each step, either the activity is selected (extending `sel`) or skipped,
and both cases preserve the invariant. After the loop, the optimality
theorem converts `earliest_compatible` into `max_compatible_count`.

## Files

| File | Role |
|------|------|
| `CLRS.Ch16.ActivitySelection.Impl.fsti` | Public interface |
| `CLRS.Ch16.ActivitySelection.Impl.fst` | Pulse implementation |
| `CLRS.Ch16.ActivitySelection.Spec.fst` | `max_compatible_count`, optimality theorems |
| `CLRS.Ch16.ActivitySelection.Lemmas.fsti` | Invariant definitions, lemma signatures |
| `CLRS.Ch16.ActivitySelection.Lemmas.fst` | Invariant preservation proofs, greedy choice |
| `CLRS.Ch16.ActivitySelection.Complexity.fsti` | `complexity_bounded_linear` definition |
| `CLRS.Ch16.ActivitySelection.Complexity.fst` | (Module body, re-exports definition) |
