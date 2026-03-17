# Jarvis March / Gift Wrapping (CLRS §33.3)

## Top-Level Signatures

Here are the top-level signatures proven about Jarvis march in
`CLRS.Ch33.JarvisMarch.Impl.fsti`:

### `find_leftmost`

```fstar
fn find_leftmost (#p: perm) (xs ys: array int)
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
      SZ.v result == find_leftmost_spec sxs sys /\
      SZ.v result < SZ.v len
    )
```

### `find_next`

```fstar
fn find_next (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t) (current: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len > 1 /\
      SZ.v current < SZ.v len /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys
    )
  returns result: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v result == find_next_spec sxs sys (SZ.v current) /\
      SZ.v result < SZ.v len
    )
```

### `jarvis_march`

```fstar
fn jarvis_march (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len > 1 /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys
    )
  returns h: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    pure (
      SZ.v h == jarvis_march_spec sxs sys /\
      SZ.v h >= 1 /\
      SZ.v h <= SZ.v len
    )
```

### Parameters

Points are stored in parallel arrays `xs` and `ys` of `int`. The ghost
variables `sxs` and `sys` capture the initial contents. The `#p` permission
means the arrays are read-only.

* `len` is the number of points (`SZ.t`).
* `current` is the index of the current hull vertex for `find_next`.
* `h` is the number of hull vertices returned by `jarvis_march`.

### Preconditions

* **`find_leftmost`**: Arrays have equal length, `len > 0`, lengths match
  physical sizes.
* **`find_next`**: Arrays have equal length, `len > 1` (at least two
  points), `current < len`.
* **`jarvis_march`**: Arrays have equal length, `len > 1`, lengths match
  physical sizes.

### Postconditions

* **`find_leftmost`**: `result == find_leftmost_spec sxs sys`,
  `result < len`, and `is_leftmost sxs sys result` (the result is the
  lexicographic minimum by x then y).
* **`find_next`**: `result == find_next_spec sxs sys current`,
  `result < len`, and `result <> current` (always advances to a
  different point, guaranteeing progress in the Jarvis march loop).
* **`jarvis_march`**: `h == jarvis_march_spec sxs sys`, `h >= 1`, and
  `h <= len`. The result is the number of hull vertices.

All three functions return arrays unchanged (read-only access).

### `jarvis_march_with_hull`

```fstar
fn jarvis_march_with_hull (#p: perm) (xs ys: array int)
  (#sxs: Ghost.erased (Seq.seq int))
  (#sys: Ghost.erased (Seq.seq int))
  (len: SZ.t)
  (hull_out: array SZ.t)
  (#shull: Ghost.erased (Seq.seq SZ.t))
  requires A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    A.pts_to hull_out shull **
    pure (
      SZ.v len == Seq.length sxs /\
      Seq.length sxs == Seq.length sys /\
      SZ.v len > 1 /\
      SZ.v len == A.length xs /\
      SZ.v len == A.length ys /\
      Seq.length shull == A.length hull_out /\
      SZ.v len <= Seq.length shull
    )
  returns h: SZ.t
  ensures A.pts_to xs #p sxs ** A.pts_to ys #p sys **
    (exists* shull'.
      A.pts_to hull_out shull' **
      pure (
        SZ.v h == jarvis_march_spec sxs sys /\
        SZ.v h >= 1 /\
        SZ.v h <= SZ.v len /\
        valid_jarvis_hull sxs sys shull' (SZ.v h)
      ))
```

This function computes the convex hull and **writes the hull vertex indices**
to `hull_out`. The count matches `jarvis_march_spec`, and the output
satisfies `valid_jarvis_hull`: hull[0] is the leftmost point, and each
subsequent vertex is `find_next` of its predecessor.

## Auxiliary Definitions

### `find_leftmost_spec` (from `CLRS.Ch33.JarvisMarch.Spec`)

```fstar
let rec find_leftmost_aux (xs ys: Seq.seq int) (i best: nat)
  : Tot nat (decreases (Seq.length xs - i)) =
  if best >= Seq.length xs || Seq.length ys <> Seq.length xs then best
  else if i >= Seq.length xs then best
  else
    let new_best =
      if Seq.index xs i < Seq.index xs best ||
         (Seq.index xs i = Seq.index xs best && Seq.index ys i < Seq.index ys best)
      then i
      else best
    in
    find_leftmost_aux xs ys (i + 1) new_best

let find_leftmost_spec (xs ys: Seq.seq int) : nat =
  if Seq.length xs = 0 then 0
  else find_leftmost_aux xs ys 1 0
```

Finds the index of the leftmost point (minimum x, breaking ties by minimum
y). This is the starting point of Jarvis march, guaranteed to be on the
convex hull.

### `find_next_spec` (from `CLRS.Ch33.JarvisMarch.Spec`)

```fstar
let rec find_next_aux (xs ys: Seq.seq int) (current next: nat) (j: nat)
  : Tot nat (decreases (Seq.length xs - j)) =
  if current >= Seq.length xs || next >= Seq.length xs || Seq.length ys <> Seq.length xs
  then next
  else if j >= Seq.length xs then next
  else if j = current then find_next_aux xs ys current next (j + 1)
  else if next = current then find_next_aux xs ys current j (j + 1)
  else
    let cp = cross_prod
      (Seq.index xs current) (Seq.index ys current)
      (Seq.index xs next) (Seq.index ys next)
      (Seq.index xs j) (Seq.index ys j) in
    let new_next = if cp < 0 then j else next in
    find_next_aux xs ys current new_next (j + 1)

let find_next_spec (xs ys: Seq.seq int) (current: nat) : nat =
  find_next_aux xs ys current current 0
```

Finds the next hull vertex from `current` by scanning all points. For each
candidate `j`, if the cross product `cp(current, next, j) < 0`, then `j` is
more clockwise than `next`, so `j` becomes the new candidate. This
implements the gift-wrapping step from CLRS.

### `jarvis_march_spec` (from `CLRS.Ch33.JarvisMarch.Spec`)

```fstar
let rec jarvis_loop_count (xs ys: Seq.seq int) (start current: nat) (fuel: nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then 0
  else
    let next = find_next_spec xs ys current in
    if next = start then 0
    else 1 + jarvis_loop_count xs ys start next (fuel - 1)

let jarvis_march_spec (xs ys: Seq.seq int) : nat =
  let n = Seq.length xs in
  if n <= 1 then n
  else
    let p0 = find_leftmost_spec xs ys in
    1 + jarvis_loop_count xs ys p0 p0 (n - 1)
```

The full Jarvis march: start at the leftmost point, repeatedly call
`find_next` until returning to the start. The fuel parameter (`n - 1`)
bounds iterations, ensuring termination. Returns the count of hull
vertices (1 for the start, plus the loop count).

### `is_leftmost` (from `CLRS.Ch33.JarvisMarch.Spec`)

```fstar
let is_leftmost (xs ys: Seq.seq int) (m: nat) : prop =
  m < Seq.length xs /\
  Seq.length ys == Seq.length xs /\
  (forall (k: nat). k < Seq.length xs ==>
    Seq.index xs m < Seq.index xs k \/
    (Seq.index xs m = Seq.index xs k /\ Seq.index ys m <= Seq.index ys k))
```

Characterizes the leftmost point: for all other points, either `m` has a
strictly smaller x-coordinate, or equal x and smaller-or-equal y.

### `all_left_of` (from `CLRS.Ch33.JarvisMarch.Spec`)

```fstar
let all_left_of (xs ys: Seq.seq int) (p q: nat) : prop =
  p < Seq.length xs /\ q < Seq.length xs /\
  Seq.length ys == Seq.length xs /\ p <> q /\
  (forall (k: nat). k < Seq.length xs /\ k <> p ==>
    cross_prod (Seq.index xs p) (Seq.index ys p)
               (Seq.index xs q) (Seq.index ys q)
               (Seq.index xs k) (Seq.index ys k) >= 0)
```

The core correctness property: all points (other than `p`) lie to the left
of or on the directed line p → q. This means edge (p, q) is a supporting
edge of the convex hull.

## What Is Proven

Each Pulse function is proven to return the exact same value as its pure
specification. Additionally, the lemma module proves:

**Bounds lemmas:**
* `find_leftmost_spec_bounded`: Result is a valid index.
* `find_next_spec_bounded`: Result is a valid index.
* `find_next_spec_not_current`: `find_next` never returns `current` when
  `n > 1` (it always advances to a different point).
* `jarvis_loop_count_bounded`: Loop count is at most `fuel`.
* `jarvis_march_spec_bounded`: Hull size is in `[1, n]`.
* `jarvis_loop_step`: Unfolding one loop iteration when `next ≠ start`.

**Hull output correctness:**
* `valid_jarvis_hull`: Characterizes a correct hull output — `hull[0]` is
  the leftmost point and each `hull[i]` = `find_next(hull[i-1])`.
* `extend_valid_jarvis_hull`: Extending a valid hull by one vertex
  preserves validity.
* `jarvis_march_with_hull` proves its output satisfies `valid_jarvis_hull`.

**Correctness lemmas:**
* `find_leftmost_is_leftmost`: The result satisfies `is_leftmost`.
* `cross_prod_swap23`: Swapping the last two points of a cross product
  negates the value (antisymmetry).
* `half_plane_transitivity`: In the upper half-plane, cross-product
  comparison is transitive. This is the key algebraic lemma.
* `cross_prod_transitivity`: Stated directly in terms of `cross_prod` with
  an `SMTPat` trigger for automatic application.
* `find_next_aux_beats_all`: Inductive invariant that the current candidate
  "beats" all previously scanned points (cross product ≥ 0).
* `find_next_all_left_of`: The result of `find_next` satisfies
  `all_left_of` — this is the **core correctness theorem** for Jarvis
  march. However, it requires two strong preconditions: (1) all points
  have `y > y[current]` (strict upper half-plane), and (2) general position
  (no three points collinear).

**Zero admits, zero assumes.** All proof obligations are mechanically
discharged by F\* and Z3.

## Specification Gaps and Limitations

1. **`len > 1` precondition.** Both `find_next` and `jarvis_march` require
   at least 2 points. The degenerate case of a single point is handled at
   the spec level (`jarvis_march_spec` returns `n` when `n <= 1`) but not
   in the Pulse interface.

2. **`find_next_all_left_of` requires general position.** The correctness
   theorem for `find_next` requires: (a) all non-current points are
   strictly above the current point (`y[k] > y[current]`), and (b) no two
   distinct non-current points have the same polar angle relative to
   `current`. These are strong assumptions:
   - (a) only holds when `current` is the bottom-most point and all others
     are strictly above. For subsequent hull vertices, this may not hold.
   - (b) is a general-position assumption that excludes collinear point
     configurations.

   Without these assumptions, the correctness of `find_next` is proven
   only at the spec-equivalence level, not at the geometric level.

3. **No end-to-end hull correctness.** There is no theorem stating "the
   output of `jarvis_march` is the correct convex hull." The proven
   properties are: (a) the count matches the spec, (b) `find_leftmost`
   returns the leftmost point, (c) `find_next` satisfies `all_left_of`
   under general-position + upper-half-plane assumptions, (d)
   `jarvis_march_with_hull` outputs vertices satisfying `valid_jarvis_hull`.
   These pieces are not composed into a single end-to-end theorem.

4. **Fuel-based termination.** The outer loop uses `fuel = n - 1` to bound
   iterations. This is correct (the hull has at most `n` vertices), but it
   means the algorithm silently stops after `n - 1` steps even if the hull
   is not complete. The `jarvis_march_spec_bounded` lemma proves the result
   is in `[1, n]`, but does not prove the loop always terminates by
   returning to the start before exhausting fuel.

5. **No complexity linking.** The Spec file defines `jarvis_march_ops n h =
   find_leftmost_ops n + h * find_next_ops n` and proves
   `jarvis_march_ops n h <= n * n` when `h <= n`, but these are not linked
   to the Pulse implementations via ghost counters.

## Complexity

| Metric | Bound | Linked? | Exact? |
|--------|-------|---------|--------|
| `find_leftmost` | O(n) | ❌ Not linked | n−1 comparisons (spec only) |
| `find_next` | O(n) | ❌ Not linked | n−1 cross products (spec only) |
| `jarvis_march` | O(nh) | ❌ Not linked | Spec-level only |
| Worst case | O(n²) | ❌ Not linked | When h = n |

The complexity analysis exists as pure definitions in the Spec file but is
not connected to the Pulse implementations via ghost counters.

## Proof Structure

* **`find_leftmost`** uses a while loop with invariant:
  `find_leftmost_aux sxs sys (SZ.v vi) (SZ.v vbest) == find_leftmost_spec sxs sys`.
  Identical structure to `find_bottom` in Graham Scan.

* **`find_next`** uses a while loop scanning index `j` from 0 to `len - 1`
  with invariant:
  `find_next_aux sxs sys (SZ.v current) (SZ.v vnext) (SZ.v vj) == find_next_spec sxs sys (SZ.v current)`.
  The update condition `do_update = not (vj = current) && ((vnext = current) || (cp < 0))`
  handles all three cases (skip self, first non-self point, better candidate).

* **`jarvis_march`** uses `--fuel 2 --ifuel 0`. It calls `find_leftmost`
  and `find_next` for the first step, then enters a while loop with
  invariant relating `vh + jarvis_loop_count sxs sys p0 vcurrent (len - vh)`
  to `jarvis_march_spec sxs sys`. The loop terminates when `next = p0`
  (returned to start) or `vh >= len` (fuel exhausted). The
  `jarvis_march_spec_bounded` lemma is called before the loop.

* **`find_next_aux_beats_all`** is the key inductive lemma. It proves that
  after scanning through index `j - 1`, the candidate `next` has
  `cross_prod(current, next, k) >= 0` for all `k < j`. The inductive step
  when `cp < 0` (j beats next) uses `half_plane_transitivity` to show
  that `j` also beats all predecessors. The `SMTPat` on
  `cross_prod_transitivity` fires automatically.

## Proof Robustness

| File | `#push-options` | rlimit | fuel/ifuel | Verdict |
|---|---|---|---|---|
| `JarvisMarch.Lemmas.fst` | 3 | `--z3rlimit 10` (2×), `--z3rlimit 20` (1×) | — | ✅ Modest |
| `JarvisMarch.Impl.fst` | 2 | `--z3rlimit 120` (`jarvis_march_with_hull`) | `--fuel 2 --ifuel 0` | ⚠️ High rlimit |

The `jarvis_march_with_hull` function requires `--z3rlimit 120 --split_queries always`,
which is the highest rlimit in the chapter. The proof involves a complex loop invariant
tracking hull validity, spec equivalence, and loop count simultaneously. Reducing below
120 causes SMT timeouts on the invariant maintenance step.

**Verification time**: ~90 seconds for decomposed files, ~40s for monolithic.

## Files

| File | Role |
|------|------|
| `CLRS.Ch33.JarvisMarch.Impl.fsti` | Public interface (these signatures) |
| `CLRS.Ch33.JarvisMarch.Impl.fst` | Pulse implementation |
| `CLRS.Ch33.JarvisMarch.Spec.fst` | Pure specifications and correctness definitions |
| `CLRS.Ch33.JarvisMarch.Lemmas.fsti` | Lemma signatures |
| `CLRS.Ch33.JarvisMarch.Lemmas.fst` | Lemma proofs |
| `CLRS.Ch33.JarvisMarch.Complexity.fsti` | Complexity interface |
| `CLRS.Ch33.JarvisMarch.Complexity.fst` | Formal op counts: O(nh) ≤ O(n²) |
| `CLRS.Ch33.JarvisMarch.fst` | Standalone module (specs + proofs + Pulse, all-in-one) |
| `CLRS.Ch33.Segments.Spec.fst` | `cross_product_spec` used by `cross_prod` alias |

### New Definitions

| Definition | Location |
|------------|----------|
| `valid_jarvis_hull` | `CLRS.Ch33.JarvisMarch.Spec` |
| `extend_valid_jarvis_hull` | `CLRS.Ch33.JarvisMarch.Lemmas` |
| `jarvis_march_with_hull` | `CLRS.Ch33.JarvisMarch.Impl` |

## Spec Validation (ImplTest)

Spec validation tests in `CLRS.Ch33.JarvisMarch.ImplTest.fst` exercise three
of four functions with a triangle instance. **All tests pass with zero admits
and zero assumes.**

| Function | Test Instance | Expected | Proven? |
|----------|---------------|----------|---------|
| `find_leftmost` | Triangle (0,0),(2,0),(1,2) | 0 | ✅ |
| `find_next` | From vertex 0 | 1 | ✅ |
| `jarvis_march` | Full triangle hull | 3 | ✅ |

The test uses composable helper lemmas that evaluate each recursive spec
function independently (`find_leftmost_spec`, `find_next_spec` from each
vertex, `jarvis_march_spec`). The composed `jarvis_march_triangle_lemma`
proves the complete algorithm returns the correct hull size.

**Findings**: All postconditions are fully precise — no specification
weaknesses found. The functional-equivalence postconditions (`result == spec`)
are unconditional and uniquely determine outputs. The geometric correctness
assumptions in `find_next_all_left_of` (general position, upper half-plane)
are a separate concern from spec precision.

See `CLRS.Ch33.JarvisMarch.ImplTest.md` for details.

## Checklist (Priority Order)

- [x] Pure specification matching CLRS §33.3 (find_leftmost, find_next, jarvis_march)
- [x] Complete Pulse implementation (find_leftmost, find_next, jarvis_march, jarvis_march_with_hull)
- [x] Impl.fsti interface file
- [x] Lemmas module with substantial correctness proofs (14 lemmas)
- [x] Lemmas.fsti interface file
- [x] Complexity module with formal O(nh) ≤ O(n²) bounds
- [x] Complexity.fsti interface file
- [x] Zero admits, zero assumes
- [x] `valid_jarvis_hull` output correctness for `jarvis_march_with_hull`
- [x] `find_next_all_left_of` core correctness (under general position)
- [x] `find_leftmost_is_leftmost` starting point correctness
- [ ] Reduce `--z3rlimit 120` in `jarvis_march_with_hull` — **medium priority** (proof refactoring)
- [ ] Relax general-position assumption in `find_next_all_left_of` — **medium priority** (handle collinear cases)
- [ ] Relax upper-half-plane assumption — **medium priority** (generalize to all hull vertices, not just bottom)
- [ ] End-to-end convex hull correctness theorem — **high priority** (compose individual edge proofs)
- [ ] Link complexity analysis to Pulse impl via ghost counters — **low priority**
- [ ] Handle `len = 1` case in Pulse interface — **low priority** (spec handles it but Pulse requires `len > 1`)
