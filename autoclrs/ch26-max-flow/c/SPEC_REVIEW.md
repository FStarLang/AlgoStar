# SPEC_REVIEW: ch26 Max Flow C Implementation vs Impl.fsti

## Summary

The C implementation (`max_flow.c`) is verified admit-free via c2pulse translation
to Pulse.  It proves Int32 overflow safety for all arithmetic under the
`MAX_CAP = 46340` bound.  However, its postconditions are significantly weaker
than the target `Impl.fsti` specification.

## What IS Verified

- **No admits or assumes** — all proof obligations discharged by Z3.
- **Int32 overflow safety** — every `Int32.add`, `Int32.sub`, `Int32.mul`
  is proven to not overflow under the MAX_CAP=46340 bound.
- **Array bounds safety** — every array read/write is within bounds.
- **Termination** — all recursive functions (`bfs_loop`, `find_bottleneck_rec`,
  `augment_flow_rec`, `max_flow_loop`) have verified decreasing measures.
- **Flow element bounds preserved** — after augmentation, all flow values
  remain in [0, 46340].
- **No complexity instrumentation** — already clean.
- **No computationally relevant code in `_include_pulse`** — only opens
  `CLRS.Ch26.MaxFlow.C.BridgeLemmas`.

## Spec Deviations

### 1. Missing `imp_valid_flow` postcondition (HIGH)

**Impl.fsti** guarantees:
`imp_valid_flow flow_seq' cap_seq n source sink`
which encodes capacity constraints (`0 ≤ flow ≤ cap`) and flow conservation
at every non-source/non-sink vertex.

**C code** only ensures:
`flow[p] >= 0 && flow[p] <= 46340` (per-element bounds) and array lengths.

**Gap:** The C code does not prove that the resulting flow satisfies capacity
constraints or conservation.  Proving this requires a loop invariant in
`augment_flow_rec` showing each update preserves `flow[u→v] ≤ cap[u→v]`
and conservation, plus connecting the flat-array representation to `valid_flow`.

### 2. Missing `no_augmenting_path` postcondition (HIGH)

**Impl.fsti** guarantees:
`no_augmenting_path cap_seq flow_seq' source sink`
(no residual s→t path exists when BFS returns "not found").

**C code** does not track any spec-level path reachability.  Proving this
requires connecting the BFS color/pred arrays to the graph-theoretic notion
of residual reachability — a substantial verification effort.

### 3. Missing `fv == imp_flow_value` postcondition (MEDIUM)

**Impl.fsti** guarantees the returned integer equals
`imp_flow_value flow_seq' n source`.

**C code** computes `fv` via `compute_flow_value` but does not prove the
result equals the spec-level `flow_value`.  This would require a loop
invariant connecting the accumulator to partial sums of the flow sequence.

### 4. Missing `fv >= 0` postcondition (LOW)

**Impl.fsti** guarantees `fv >= 0`.

**C code** does not assert this.  It follows from valid flow + conservation,
so proving deviation #1 would likely yield this for free.

### 5. Representation mismatch: c2pulse arrays vs Pulse sequences (STRUCTURAL)

**Impl.fsti** uses `A.pts_to capacity cap_seq` with `Seq.seq int` ghost
state (standard Pulse arrays).

**C code** (via c2pulse) uses `array_pts_to` with `Seq.seq (option Int32.t)`
ghost state plus mask predicates.  These are structurally different types.

Bridging requires either a wrapper layer that converts between representations,
or proving a refinement relation between `array_pts_to` and `A.pts_to`.

### 6. `valid_caps` precondition vs explicit bounds (LOW)

**Impl.fsti** requires `valid_caps cap_seq n` (abstract predicate: all caps ≥ 0).

**C code** requires `cap[k] >= 0 && cap[k] <= 46340` — strictly stronger
(adds upper bound) but uses a concrete forall rather than the abstract
`valid_caps` predicate.

### 7. Capacity array is not read-only (LOW)

**Impl.fsti** separates `capacity` (read-only) from `flow` (output).

**C code** passes `cap` as mutable (c2pulse limitation) though it is never
written.  The postcondition preserves lengths but does not guarantee cap
contents are unchanged (though the merged quantified invariant does).

## Recommendations for Closing Gaps

1. **Flow validity (#1, #4):** Add ghost state tracking a `valid_flow`
   invariant through the augmentation loop.

2. **No augmenting path (#2):** After BFS returns "not found", prove that
   all sink-reachable vertices in the residual graph are colored BLACK.

3. **Flow value equality (#3):** Strengthen `compute_flow_value` loop
   invariant to track partial sums matching `flow_value`.

4. **Representation bridge (#5):** Write a Pulse wrapper that converts
   between c2pulse's `array_pts_to` and standard `A.pts_to`.
