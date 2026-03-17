# Naive String Matching (CLRS §32.1)

**Last reviewed**: 2026-03-16

## Top-Level Signature

Here is the top-level signature proven about the naive string matcher in
`CLRS.Ch32.NaiveStringMatch.fst`:

```fstar
fn naive_string_match
  (#a: eqtype)
  (#p_text: perm)
  (#p_pat: perm)
  (text: array a)
  (pattern: array a)
  (#s_text: Ghost.erased (Seq.seq a))
  (#s_pat: Ghost.erased (Seq.seq a))
  (n: SZ.t)
  (m: SZ.t)
  (ctr: GR.ref nat)
  (#c0: erased nat)
  requires
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n == Seq.length s_text /\
      SZ.v m == Seq.length s_pat /\
      Seq.length s_text <= A.length text /\
      Seq.length s_pat <= A.length pattern /\
      SZ.v m > 0 /\
      SZ.v m <= SZ.v n /\
      SZ.fits (SZ.v n - SZ.v m + 2) /\
      SZ.fits (op_Multiply (SZ.v n - SZ.v m + 1) (SZ.v m))
    )
  returns result: SZ.t
  ensures exists* (cf: nat).
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    GR.pts_to ctr cf **
    pure (
      SZ.v result <= SZ.v n - SZ.v m + 1 /\
      SZ.v result == count_matches_up_to s_text s_pat (SZ.v n - SZ.v m + 1) /\
      string_match_complexity_bounded cf (reveal c0) (SZ.v n) (SZ.v m)
    )
```

### Parameters

* `text` and `pattern` are arrays over any type with decidable equality
  (`eqtype`). Ghost sequences `s_text` and `s_pat` capture their contents.
  Both arrays are accessed with fractional permissions (`p_text`, `p_pat`),
  meaning they are **read-only** — the algorithm does not modify the input.

* `n` is the text length, `m` is the pattern length (both `SZ.t`).

* `ctr` is a **ghost counter** tracking character comparisons.

### Preconditions

* `SZ.v m > 0` — The pattern must be non-empty.
* `SZ.v m <= SZ.v n` — The pattern must not be longer than the text.
* `SZ.fits` constraints ensure machine arithmetic does not overflow.

### Postcondition

* `SZ.v result == count_matches_up_to s_text s_pat (n - m + 1)` — The result
  is the total count of positions where the pattern matches the text.

* `string_match_complexity_bounded cf (reveal c0) n m` — The number of
  comparisons is at most `(n - m + 1) * m`.

## Auxiliary Definitions

### `matches_at` (from `CLRS.Ch32.NaiveStringMatch.Spec`)

```fstar
let matches_at (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat) : prop =
  s + Seq.length pattern <= Seq.length text /\
  (forall (j: nat). j < Seq.length pattern ==>
    Seq.index text (s + j) == Seq.index pattern j)
```

Propositional predicate: the pattern matches text starting at position `s`.

### `matches_at_dec` (from `CLRS.Ch32.NaiveStringMatch.Spec`)

```fstar
let matches_at_dec (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (s: nat) : bool =
  s + Seq.length pattern <= Seq.length text && check_match_at text pattern s 0
```

Decidable (boolean) version of `matches_at`, used in the count function.

### `count_matches_up_to` (from `CLRS.Ch32.NaiveStringMatch.Spec`)

```fstar
let rec count_matches_up_to (#a: eqtype) (text: Seq.seq a) (pattern: Seq.seq a) (limit: nat)
  : Tot nat (decreases limit)
  = if limit = 0 then 0
    else count_matches_up_to text pattern (limit - 1) +
         (if matches_at_dec text pattern (limit - 1) then 1 else 0)
```

Counts the number of matching positions in `[0, limit)`.

### `string_match_complexity_bounded` (from `CLRS.Ch32.NaiveStringMatch.Complexity`)

```fstar
let string_match_complexity_bounded (cf c0 n m: nat) : prop =
  cf >= c0 /\ cf - c0 <= (n - m + 1) * m
```

The standard O((n−m+1)·m) worst-case bound for naive string matching.

## What Is Proven

1. **Functional correctness**: The return value equals the exact count of
   pattern occurrences in the text, as computed by `count_matches_up_to`.

2. **Completeness**: Since `count_matches_up_to` iterates over all valid
   starting positions, the result counts *all* matches — no false negatives.

3. **Match equivalence** (`matches_at_dec_correct`): The decidable check
   `matches_at_dec` is proven equivalent to the propositional `matches_at`,
   bridging the boolean computation to the logical specification.

4. **Complexity bound**: `cf - c0 ≤ (n - m + 1) * m`. The ghost counter is
   incremented once per character comparison in the inner loop.

5. **Non-destructive**: Both arrays are accessed with fractional permissions
   and returned unchanged.

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **Returns count, not positions.** The algorithm returns the number of
   matches, not the list of matching positions. CLRS prints each matching
   shift; this implementation counts them.

2. **Pattern must be non-empty.** The precondition requires `m > 0` and
   `m ≤ n`. Empty patterns and patterns longer than text are excluded.

3. **No best-case or adaptive complexity.** The bound `(n - m + 1) * m` is
   worst-case. For inputs where mismatches occur early, far fewer comparisons
   are performed. The specification does not capture this.

4. **Generic over eqtype.** The implementation is polymorphic over any
   `eqtype`, not restricted to `int` or `char`. This is stronger than CLRS
   (which assumes characters) but the complexity bound is the same.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Comparisons | O(nm) = (n−m+1)·m | ✅ Ghost counter | Upper bound only |

The complexity is **fully linked** to the imperative implementation: `tick ctr`
is called once per character comparison in the inner verification loop. The
outer loop runs `n - m + 1` iterations; the inner loop runs at most `m`
iterations per outer iteration. An additional lemma `naive_worst_case_quadratic`
proves `(n - m + 1) * m ≤ n * m`.

## Proof Structure

The outer loop invariant maintains:

* `count == count_matches_up_to text pattern s` — count is correct up to
  position `s`.
* `vc - c0 ≤ s * m` — comparisons are bounded.

The inner loop checks characters one by one, maintaining a boolean `all_match`
and tracking the index `j`. After the inner loop, `matches_at_dec_correct`
bridges the loop result to the propositional specification, and
`count_matches_up_to_unfold` extends the count by one position.

## Profiling

| File | Approx. time |
|------|-------------|
| `NaiveStringMatch.fst` | ~5s |
| `NaiveStringMatch.Spec.fst` | <1s |
| `NaiveStringMatch.Lemmas.fst` | ~1s |
| `NaiveStringMatch.Complexity.fst` | <1s |

No bottlenecks. All proofs are fast and stable.

## Files

| File | Role |
|------|------|
| `CLRS.Ch32.NaiveStringMatch.fst` | Pulse implementation (uses `CLRS.Common.Complexity.tick`) |
| `CLRS.Ch32.NaiveStringMatch.Spec.fst` | `matches_at`, `matches_at_dec`, `count_matches_up_to` |
| `CLRS.Ch32.NaiveStringMatch.Complexity.fsti` | `string_match_complexity_bounded` |
| `CLRS.Ch32.NaiveStringMatch.Complexity.fst` | `naive_worst_case_quadratic`, `complexity_nonneg` |
| `CLRS.Ch32.NaiveStringMatch.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch32.NaiveStringMatch.Lemmas.fst` | `matches_at_dec_correct`, unfolding, bounded |

## Spec Validation (2026-03-17)

**Test file**: `CLRS.Ch32.NaiveStringMatch.ImplTest.fst`

| Check | Result |
|-------|--------|
| Precondition satisfiable | ✅ Proven (text=[1,2,1,2,1], pat=[1,2,1]) |
| Postcondition precise | ✅ count=2 uniquely determined |
| Match positions verified | ✅ pos 0 ✓, pos 1 ✗, pos 2 ✓ |
| No admits/assumes in test | ✅ |

**Finding**: The postcondition is precise — `count_matches_up_to` uniquely
determines the output for any concrete input. No specification weaknesses found.

## Checklist

- [x] Functional correctness (count == spec)
- [x] Complexity bound proven and linked via ghost counter
- [x] Zero admits / assumes
- [x] CLRS-faithful algorithm
- [x] Spec/Impl separation (factored into Spec, Lemmas, Complexity)
- [x] Interface (.fsti) files for Lemmas and Complexity
- [x] Uses shared `CLRS.Common.Complexity.tick`
- [x] Fast, stable proofs (<10s total)
- [x] Spec validation test (`ImplTest.fst`) — postcondition precision verified
- [ ] Missing `Impl.fsti` — no public interface file for the Pulse implementation
- [ ] `matches_at` / `count_matches_up_to` duplicated across Naive, RabinKarp, KMP
