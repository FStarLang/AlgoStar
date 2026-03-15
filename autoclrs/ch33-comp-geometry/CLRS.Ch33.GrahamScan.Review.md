# Graham Scan Building Blocks (CLRS §33.3)

## Top-Level Signatures

Here are the top-level signatures proven about the Graham scan building
blocks in `CLRS.Ch33.GrahamScan.Impl.fsti`:

### `find_bottom`

```fstar
fn find_bottom (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len > 0 /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys
    )
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v result == find_bottom_spec sxs sys /\
      SZ.v result < SZ.v len
    )
```

### `polar_cmp`

```fstar
fn polar_cmp (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t) (p0 a b: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v p0 < SZ.v len /\
      SZ.v a < SZ.v len /\
      SZ.v b < SZ.v len /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys
    )
  returns result: int
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (result == polar_cmp_spec sxs sys (SZ.v p0) (SZ.v a) (SZ.v b))
```

### `pop_while`

```fstar
fn pop_while (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (#ph: perm) (hull: array SZ.t)
  (#shull: Ghost.erased (Seq.seq SZ.t))
  (top_in: SZ.t) (p_idx: SZ.t) (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    A.pts_to hull #ph shull **
    pure (
      SZ.v top_in >= 2 /\
      SZ.v top_in <= Seq.length shull /\
      SZ.v p_idx < SZ.v len /\
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys /\
      Seq.length shull == A.length hull /\
      (forall (i: nat). i < SZ.v top_in ==> SZ.v (Seq.index shull i) < SZ.v len)
    )
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    A.pts_to hull #ph shull **
    pure (
      SZ.v result == pop_while_spec sxs sys shull (SZ.v top_in) (SZ.v p_idx) /\
      SZ.v result <= SZ.v top_in
    )
```

### Parameters

Points are stored in parallel arrays `xs` and `ys` of `int`. The ghost
variables `sxs` and `sys` capture the initial contents. The `#p` permission
parameter means the arrays are read-only (fractional permission).

* `len` is the number of points (`SZ.t`, machine-sized).
* `p0`, `a`, `b` are point indices (`SZ.t`) for `polar_cmp`.
* `hull` is an array of point indices (`SZ.t`) representing the hull stack
  for `pop_while`. The ghost `shull` captures its contents.
* `top_in` is the current stack height, `p_idx` is the new point index.

### Preconditions

* **`find_bottom`**: Arrays have equal length, `len > 0`, lengths match
  physical array sizes.
* **`polar_cmp`**: Arrays have equal length, all three indices (`p0`, `a`,
  `b`) are in bounds.
* **`pop_while`**: Stack has at least 2 elements (`top_in >= 2`), new point
  is in bounds, all hull indices are valid (each `hull[i] < len`).

### Postconditions

Each function's result is proven equal to its pure specification:

* **`find_bottom`**: `result == find_bottom_spec sxs sys` and
  `result < len` (in-bounds).
* **`polar_cmp`**: `result == polar_cmp_spec sxs sys p0 a b`.
* **`pop_while`**: `result == pop_while_spec sxs sys shull top_in p_idx`
  and `result <= top_in` (stack can only shrink).

All three functions return arrays unchanged (read-only access).

### `graham_scan_step`

```fstar
fn graham_scan_step (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (hull: array SZ.t)
  (#shull: Ghost.erased (Seq.seq SZ.t))
  (top_in: SZ.t) (p_idx: SZ.t) (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    A.pts_to hull shull **
    pure (
      SZ.v top_in >= 2 /\
      SZ.v top_in < Seq.length shull /\
      SZ.v p_idx < SZ.v len /\
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys /\
      Seq.length shull == A.length hull /\
      Seq.length shull <= SZ.v len /\
      (forall (i: nat). i < SZ.v top_in ==> SZ.v (Seq.index shull i) < SZ.v len)
    )
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    (exists* shull'.
      A.pts_to hull shull' **
      pure (
        shull' == fst (scan_step_sz_spec sxs sys shull (SZ.v top_in) p_idx) /\
        SZ.v result == snd (scan_step_sz_spec sxs sys shull (SZ.v top_in) p_idx) /\
        SZ.v result >= 2 /\
        SZ.v result <= Seq.length shull
      ))
```

This function performs a complete scan step: calls `pop_while` to remove
non-left-turn entries, then pushes `p_idx` onto the hull stack. Unlike the
building-block functions, it takes the hull array with **full permission**
and returns it modified. The result `scan_step_sz_spec` matches the pure
specification.

## Auxiliary Definitions

### `find_bottom_spec` (from `CLRS.Ch33.GrahamScan.Spec`)

```fstar
let rec find_bottom_aux (xs ys: Seq.seq int) (i best: nat)
  : Tot nat (decreases (Seq.length xs - i)) =
  if best >= Seq.length xs || Seq.length ys <> Seq.length xs then best
  else if i >= Seq.length xs then best
  else
    let new_best =
      if Seq.index ys i < Seq.index ys best ||
         (Seq.index ys i = Seq.index ys best && Seq.index xs i < Seq.index xs best)
      then i
      else best
    in
    find_bottom_aux xs ys (i + 1) new_best

let find_bottom_spec (xs ys: Seq.seq int) : nat =
  if Seq.length xs = 0 then 0
  else find_bottom_aux xs ys 1 0
```

Finds the index of the bottom-most point (minimum y, breaking ties by
minimum x). This is the starting point of Graham scan — CLRS guarantees
that this point is on the convex hull.

### `polar_cmp_spec` (from `CLRS.Ch33.GrahamScan.Spec`)

```fstar
let polar_cmp_spec (xs ys: Seq.seq int) (p0 a b: nat) : int =
  if p0 >= Seq.length xs || a >= Seq.length xs || b >= Seq.length xs ||
     Seq.length ys <> Seq.length xs
  then 0
  else
    cross_prod
      (Seq.index xs p0) (Seq.index ys p0)
      (Seq.index xs a) (Seq.index ys a)
      (Seq.index xs b) (Seq.index ys b)
```

Compares polar angles of points `a` and `b` relative to pivot `p0` using
the cross product. Returns positive if `a` has a smaller polar angle (comes
first in CCW order), negative if `b` comes first, zero if collinear.

### `pop_while_spec` (from `CLRS.Ch33.GrahamScan.Spec`)

```fstar
let rec pop_while_spec (xs ys: Seq.seq int) (hull: Seq.seq SZ.t) (top: nat) (p_idx: nat)
  : Tot nat (decreases top) =
  if top < 2 || top > Seq.length hull then top
  else
    let t1 = SZ.v (Seq.index hull (top - 1)) in
    let t2 = SZ.v (Seq.index hull (top - 2)) in
    if t1 >= Seq.length xs || t2 >= Seq.length xs || p_idx >= Seq.length xs ||
       Seq.length ys <> Seq.length xs
    then top
    else
      let cp = cross_prod
        (Seq.index xs t2) (Seq.index ys t2)
        (Seq.index xs t1) (Seq.index ys t1)
        (Seq.index xs p_idx) (Seq.index ys p_idx) in
      if cp <= 0 then pop_while_spec xs ys hull (top - 1) p_idx
      else top
```

Pops non-left-turn entries from the hull stack. Repeatedly checks whether
the top two hull points and the new point `p_idx` make a left turn
(`cross_prod > 0`). If not (`cp <= 0`), the top is popped. Returns the new
stack height.

### `is_bottommost` (from `CLRS.Ch33.GrahamScan.Spec`)

```fstar
let is_bottommost (xs ys: Seq.seq int) (m: nat) : prop =
  m < Seq.length xs /\
  Seq.length ys == Seq.length xs /\
  (forall (k: nat). k < Seq.length xs ==>
    Seq.index ys m < Seq.index ys k \/
    (Seq.index ys m = Seq.index ys k /\ Seq.index xs m <= Seq.index xs k))
```

Characterizes the bottom-most point: for all other points, either `m` has
a strictly smaller y-coordinate, or equal y and smaller-or-equal x.

### `all_left_turns` (from `CLRS.Ch33.GrahamScan.Spec`)

```fstar
let all_left_turns (xs ys: Seq.seq int) (hull: Seq.seq nat) (top: nat) : prop =
  top <= Seq.length hull /\
  Seq.length ys == Seq.length xs /\
  (forall (i: nat). i + 2 < top ==>
    Seq.index hull i < Seq.length xs /\
    Seq.index hull (i + 1) < Seq.length xs /\
    Seq.index hull (i + 2) < Seq.length xs /\
    cross_prod (Seq.index xs (Seq.index hull i))
               (Seq.index ys (Seq.index hull i))
               (Seq.index xs (Seq.index hull (i + 1)))
               (Seq.index ys (Seq.index hull (i + 1)))
               (Seq.index xs (Seq.index hull (i + 2)))
               (Seq.index ys (Seq.index hull (i + 2))) > 0)
```

The convex-position invariant: every consecutive triple of hull vertices
makes a strictly left turn (positive cross product). This is the key
invariant maintained by Graham scan (CLRS Theorem 33.1).

## What Is Proven

Each Pulse function is proven to return the exact same value as its pure
specification. Additionally, the lemma module proves:

* **`find_bottom_spec_bounded`**: The result is always a valid index
  (`< Seq.length xs`).
* **`find_bottom_is_bottommost`**: The result satisfies `is_bottommost` —
  it truly is the lexicographic minimum (y, then x).
* **`pop_while_spec_bounded`**: The result is at most `top_in` (stack only
  shrinks).
* **`pop_while_ensures_left_turn`**: When `pop_while_spec` stops with
  `top' >= 2`, the top two hull points and the new point form a left turn
  (`cross_prod > 0`). This is the key invariant maintenance step.

* **`all_left_turns_sz_prefix`**: The `all_left_turns_sz` property is
  monotone — reducing `top` preserves convex position.

* **`pop_while_spec_ge_1`**: `pop_while_spec` returns at least 1 when
  starting with `top >= 2`.

* **`scan_step_preserves_left_turns`**: A full scan step (pop non-left-turns,
  then push) preserves the `all_left_turns_sz` invariant. This is the
  CLRS Theorem 33.1 maintenance step, now formally connected.

The Spec file also provides pure specifications for the complete Graham scan
algorithm (`pop_non_left`, `scan_step`, `graham_loop`, `graham_scan_sorted`),
as well as `scan_step_sz_spec` (SZ.t-compatible scan step spec) and
`all_left_turns_sz` (SZ.t-compatible convex position property).

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **No sorting implementation.** Graham scan requires sorting points by
   polar angle. No verified sort is provided in this module. A caller must
   supply a correct sort to assemble the full algorithm.

2. **`pop_while` requires `top_in >= 2`.** The function cannot be called on
   a stack with fewer than 2 elements. The full scan handles this by
   initializing the stack with the first 3 points, but the precondition
   means `pop_while` alone cannot handle degenerate inputs.

3. **No end-to-end convex hull output correctness.** The `all_left_turns`
   property is defined, and `scan_step_preserves_left_turns` proves that
   each scan step maintains it, but there is no end-to-end theorem
   stating "the output of the full scan satisfies `all_left_turns`" —
   that would require composing the scan loop with sorting.

4. **No complexity linking.** The Spec file defines operation counts
   (`find_bottom_ops`, `pop_while_ops`, `graham_scan_ops`) and proves
   `graham_scan_ops n <= 4 * n * n`, but these are not linked to the Pulse
   implementations via ghost counters.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| `find_bottom` | O(n) | ❌ Not linked | n−1 comparisons (spec only) |
| `polar_cmp` | O(1) | ❌ Not linked | 8 ops (spec only) |
| `pop_while` | O(top) | ❌ Not linked | ≤ top iterations (spec only) |
| Full scan | O(n²) with insertion sort | ❌ Not linked | Spec-level only |

The complexity analysis exists as pure definitions in the Spec file but is
not connected to the Pulse implementations via ghost counters.

## Proof Structure

* **`find_bottom`** uses a while loop with invariant: `find_bottom_aux sxs
  sys (SZ.v vi) (SZ.v vbest) == find_bottom_spec sxs sys`. The invariant
  states that completing the scan from position `vi` with current best
  `vbest` yields the same result as the full spec. The `find_bottom_spec_bounded`
  lemma is called before the loop to establish that the result is in bounds.

* **`polar_cmp`** is a straight-line computation with no loop. The Pulse
  body directly computes `(ax - px) * (b_y - py) - (bx - px) * (ay - py)`,
  which F\* verifies equals `polar_cmp_spec` by unfolding.

* **`pop_while`** uses a while loop with a boolean flag `keep_going` and
  invariant relating the current `vt` to the spec: when `keep_going` is
  true, `pop_while_spec` from `vt` equals `pop_while_spec` from `top_in`;
  when false, `vt` equals the final result. Uses `--fuel 2 --ifuel 0`
  for the recursive spec unfolding. The `pop_while_spec_bounded` lemma
  is called to establish the bound.

## Files

| File | Role |
|------|------|
| `CLRS.Ch33.GrahamScan.Impl.fsti` | Public interface (these signatures) |
| `CLRS.Ch33.GrahamScan.Impl.fst` | Pulse implementation |
| `CLRS.Ch33.GrahamScan.Spec.fst` | Pure specifications (including full scan spec) |
| `CLRS.Ch33.GrahamScan.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch33.GrahamScan.Lemmas.fst` | Lemma proofs |
| `CLRS.Ch33.GrahamScan.fst` | Standalone module (specs + proofs + Pulse, all-in-one) |
| `CLRS.Ch33.Segments.Spec.fst` | `cross_product_spec` used by `cross_prod` alias |

### New Definitions

| Definition | Location |
|------------|----------|
| `all_left_turns_sz` | `CLRS.Ch33.GrahamScan.Spec` |
| `scan_step_sz_spec` | `CLRS.Ch33.GrahamScan.Spec` |
| `all_left_turns_sz_prefix` | `CLRS.Ch33.GrahamScan.Lemmas` |
| `pop_while_spec_ge_1` | `CLRS.Ch33.GrahamScan.Lemmas` |
| `scan_step_preserves_left_turns` | `CLRS.Ch33.GrahamScan.Lemmas` |
| `graham_scan_step` | `CLRS.Ch33.GrahamScan.Impl` |
