# Rabin-Karp String Matching (CLRS §32.2)

## Top-Level Signature

The Pulse implementation signature is in `CLRS.Ch32.RabinKarp.fst`:

```fstar
fn rabin_karp
  (#p_text: perm)
  (#p_pat: perm)
  (text: array nat)
  (pattern: array nat)
  (#s_text: Ghost.erased (Seq.seq nat))
  (#s_pat: Ghost.erased (Seq.seq nat))
  (n: SZ.t)
  (m: SZ.t)
  (d: nat)
  (q: pos)
  requires
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    pure (
      SZ.v n == Seq.length s_text /\
      SZ.v m == Seq.length s_pat /\
      Seq.length s_text <= A.length text /\
      Seq.length s_pat <= A.length pattern /\
      SZ.v m > 0 /\
      SZ.v m <= SZ.v n /\
      SZ.fits (SZ.v n - SZ.v m + 2) /\
      SZ.fits (SZ.v n + 1)
    )
  returns result: int
  ensures
    A.pts_to text #p_text s_text **
    A.pts_to pattern #p_pat s_pat **
    pure (result >= 0 /\ result <= SZ.v n - SZ.v m + 1 /\
          result == count_matches_up_to s_text s_pat (SZ.v n - SZ.v m + 1))
```

### Parameters

* `text` and `pattern` are arrays of `nat` (not `int` or generic `eqtype`).
  Ghost sequences capture their contents.

* `n` is text length, `m` is pattern length.

* `d` is the radix (alphabet size) and `q` is a positive modulus for the hash
  function. These are caller-supplied — the algorithm is parametric in the
  hash parameters.

### Preconditions

* `SZ.v m > 0` and `SZ.v m <= SZ.v n` — non-empty pattern fits within text.
* `SZ.fits` constraints for machine arithmetic safety.

### Postcondition

* `result == count_matches_up_to s_text s_pat (n - m + 1)` — The result is
  the exact count of all match positions.

* `result >= 0 /\ result <= n - m + 1` — Bounds on the count.

**Note:** Unlike GCD, ModExp, and Naive String Match, the Rabin-Karp Pulse
implementation does **not** have a ghost counter or a complexity bound in its
postcondition.

## Auxiliary Definitions

### `hash` (from `CLRS.Ch32.RabinKarp.Spec`)

```fstar
let rec hash (x:Seq.seq nat) (d:nat) (q:nat{q <> 0})
             (i:nat) (j:nat{i <= j /\ j <= Seq.length x})
  : Tot nat (decreases j - i)
  = if i = j then 0
    else (d * hash x d q i (j - 1) + Seq.index x (j - 1)) % q
```

CLRS polynomial hash via Horner's rule (left-to-right). The leftmost character
gets the highest power of `d`: `hash(x, d, q, i, j) = (x[i]·d^(j-i-1) + ... +
x[j-1]·d^0) mod q`.

### `rolling_hash_step` (from `CLRS.Ch32.RabinKarp.Spec`)

```fstar
let rolling_hash_step (ts:nat) (old_char:nat) (new_char:nat)
                      (d:nat) (q:pos) (h:nat) : nat =
  (d * ((ts + q - (old_char * h) % q) % q) + new_char) % q
```

CLRS equation 32.2: `t_{s+1} = (d · (t_s - T[s] · d^(m-1)) + T[s+m]) mod q`.
Uses `(ts + q - ...)` to avoid negative intermediate values.

### `matches_at` (from `CLRS.Ch32.RabinKarp.Spec`)

```fstar
let matches_at (text pattern:Seq.seq nat) (s:nat) : prop =
  s + Seq.length pattern <= Seq.length text /\
  (forall (j:nat). j < Seq.length pattern ==>
    Seq.index text (s + j) == Seq.index pattern j)
```

### `count_matches_up_to` (from `CLRS.Ch32.RabinKarp.fst`)

```fstar
let rec count_matches_up_to (text pattern: Seq.seq nat) (limit: nat)
  : Tot nat (decreases limit)
  = if limit = 0 then 0
    else count_matches_up_to text pattern (limit - 1) +
         (if RKSpec.matches_at_dec text pattern (limit - 1) then 1 else 0)
```

Defined locally in the Pulse module (not in Spec).

## What Is Proven

### Pulse Implementation (CLRS.Ch32.RabinKarp.fst)

1. **Functional correctness**: The Pulse `rabin_karp` function returns the
   exact match count, equivalent to checking every position with full
   character comparison.

2. **Rolling hash correctness** (`rolling_hash_step_correct`): The rolling
   hash update computes the same value as recomputing the hash from scratch.

3. **No false negatives in Pulse**: On a hash match, the implementation
   performs full character-by-character verification. On a match at position
   `s`, `hash_match_lemma` proves the hashes must be equal, so verification
   always occurs and succeeds.

### Pure Specification (CLRS.Ch32.RabinKarp.Spec.fst)

4. **No false positives** (`rabin_karp_matches_no_false_positives`): Every
   position returned by `rabin_karp_matches` satisfies `matches_at`.

5. **No false negatives** (`rabin_karp_matches_no_false_negatives`): Every
   valid match position appears in the result list. The proof relies on
   `hash_match_lemma`: equal substrings produce equal hashes, so
   `verify_match` always succeeds for true matches.

6. **Combined correctness** (`rabin_karp_find_all_correct`): The pure
   `rabin_karp_find_all` is proven both sound and complete.

7. **Hash algebra**: `hash_inversion` (extracting the most-significant digit),
   `remove_msd_lemma`, `rolling_hash_proven`, `hash_slice_lemma` (equal
   substrings → equal hashes), and `pow_mod_correct` (connecting `pow_mod` to
   mathematical `pow`).

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **No ghost counter in Pulse implementation.** Unlike the other algorithms
   in this project, the Pulse `rabin_karp` function does not thread a ghost
   counter. The postcondition contains no complexity bound.

2. **Complexity analysis is separate and not linked.** The complexity bounds
   in `CLRS.Ch32.RabinKarp.Complexity` define best-case O(n+m) and worst-case
   O(nm) as pure functions, but these are **not connected** to the Pulse
   implementation. They are standalone mathematical lemmas.

3. **Worst-case O(nm).** When all hash values collide, every position requires
   full verification, yielding O((n−m+1)·m) = O(nm) comparisons. The
   specification makes no probabilistic argument about expected O(n+m) with
   a good hash function.

4. **Elements restricted to `nat`.** The implementation uses `nat` arrays (not
   generic `eqtype`), because the hash function requires arithmetic on
   character values. This is less general than the naive matcher's `eqtype`.

5. **Two implementations.** The codebase contains both a Pulse implementation
   (in `CLRS.Ch32.RabinKarp.fst`) and a pure recursive implementation (in
   `CLRS.Ch32.RabinKarp.Spec.fst`). Both are separately verified.

6. **Returns count, not positions.** The Pulse version returns a count. The
   pure version returns a `list nat` of positions.

7. **Hash parameters are caller-supplied.** The algorithm is parametric in `d`
   (radix) and `q` (modulus). The correctness proofs hold for any `d : nat`
   and `q : pos`. No guidance on choosing good parameters is formalized.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| Best case (pure) | O(n+m) = m + (n−m+1) | ❌ Not linked | Exact formula |
| Worst case (pure) | O(nm) = m + (n−m+1)·m | ❌ Not linked | Exact formula |
| Pulse implementation | — | ❌ No ghost counter | Not tracked |

The complexity bounds in `CLRS.Ch32.RabinKarp.Complexity` are proven as pure
mathematical lemmas:

```fstar
let rk_best_case (n m: nat) : nat =
  m + (if n >= m then n - m + 1 else 0)

let rk_worst_case (n m: nat) : nat =
  m + (if n >= m then (n - m + 1) * m else 0)
```

Supporting lemmas include `rk_best_linear` (best case ≤ n+1),
`rk_worst_quadratic` (worst case ≤ n·m+1), and `rk_best_le_worst`.

## Proof Structure

### Pulse Implementation

The main loop iterates over starting positions `s = 0, ..., n-m`. At each
position:

1. Compare `t_hash` (rolling hash of `text[s..s+m]`) with `p_hash` (pattern
   hash).
2. If hashes match, verify character-by-character in an inner loop.
3. Update the rolling hash for position `s+1` using `rolling_hash_step`.

The loop invariant tracks `vt_hash == RKSpec.hash s_text d q s (s+m)` and
`vcount == count_matches_up_to s_text s_pat s`. The key combined lemma
`should_count_correct` bridges the inner loop result to `matches_at_dec`.

### Pure Specification

The pure `rabin_karp_matches` is a recursive function that maintains the
rolling hash. Correctness is proven by structural induction. The
no-false-negatives proof uses `hash_match_lemma`: if `matches_at text pattern
s`, then `hash text d q s (s+m) == hash pattern d q 0 m`, so
`verify_match` returns `true`.

## Files

| File | Role |
|------|------|
| `CLRS.Ch32.RabinKarp.fst` | Pulse implementation + local `count_matches_up_to` |
| `CLRS.Ch32.RabinKarp.Spec.fst` | Hash function, pure RK, rolling hash, correctness proofs |
| `CLRS.Ch32.RabinKarp.Lemmas.fsti` | Correctness lemma signatures |
| `CLRS.Ch32.RabinKarp.Lemmas.fst` | Correctness lemma proofs (no false pos/neg) |
| `CLRS.Ch32.RabinKarp.Complexity.fsti` | `rk_best_case`, `rk_worst_case` |
| `CLRS.Ch32.RabinKarp.Complexity.fst` | Complexity lemma proofs |
