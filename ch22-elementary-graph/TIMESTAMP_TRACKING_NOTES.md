# Timestamp Tracking for stack_dfs

## Goal
Eliminate the `assume_` at line 748 in `stack_dfs` by adding timestamp tracking invariants.

The assume currently covers 4 properties:
1. All vertices BLACK: `forall u. color[u] == 2`
2. All d > 0: `forall u. d[u] > 0`
3. All f > 0: `forall u. f[u] > 0`
4. Discovery < finish: `forall u. d[u] < f[u]`

## Strategy
Properties 2-4 can be proven via timestamp tracking invariants:
- Track that BLACK vertices always have valid timestamps (d > 0, f > 0, d < f)
- Track that non-WHITE vertices always have d > 0
- Track that GRAY vertices have d <= current_time

Property 1 (all BLACK) requires proving "no GRAY vertices remain" after outer loop, which needs count_gray or equivalent stack-to-GRAY bijection tracking.

## Challenges Encountered

### 1. Pulse Quantifier Complexity
Adding quantified postconditions that reference both input and output state causes Pulse elaboration to fail with "incomplete quantifiers". For example:

```pulse
ensures ...
  pure (
    // This fails: references both input scolor and output scolor'
    (forall (u:nat). u < n /\ Seq.index scolor u == 2 ==>
      Seq.index scolor' u == 2)
  )
```

**Workaround**: Keep low-level function postconditions simple, track complex properties only in loop invariants.

### 2. Precondition Propagation
Adding `Seq.index scolor (SZ.v vv) == 0` (vv is WHITE) to `discover_vertex_dfs` requires proving this at all call sites. This created cascading changes.

### 3. Stack Invariant Maintenance
Adding `(forall i. i < vtop ==> stack[i] < n)` to postconditions requires explicit proof in function bodies using assertions about array updates.

## Recommended Incremental Approach

### Phase 1: Add Minimal Timestamp Postconditions
Instead of complex quantifiers, add simple facts:
- `discover_vertex_dfs`: "vv becomes GRAY with d[vv] = time+1"
- `finish_vertex`: "u becomes BLACK with f[u] = time+1"

### Phase 2: Loop Invariant Tracking
Add to `dfs_visit` while loop invariant:
```pulse
pure (
  // BLACK vertices have valid timestamps
  (forall u. u < n /\ color[u] == 2 ==>
    d[u] > 0 /\ f[u] > 0 /\ d[u] < f[u]) /\
  // Non-WHITE have d > 0
  (forall u. u < n /\ color[u] <> 0 ==> d[u] > 0) /\
  // GRAY have d <= time
  (forall u. u < n /\ color[u] == 1 ==> d[u] <= time)
)
```

### Phase 3: Invariant Maintenance Proofs
At each loop iteration:
- **discover branch**: Establish properties for newly GRAY vertex
- **finish branch**: Establish properties for newly BLACK vertex (requires knowing u was GRAY, which needs "top of stack is GRAY" invariant)

### Phase 4: Propagate to Outer Functions
- `dfs_visit` postcondition inherits BLACK timestamp property from loop exit
- `stack_dfs` loop inherits and maintains
- Final postcondition proven from loop invariant

## Current Status
- Added simple preconditions (vv is WHITE) to `discover_vertex_dfs` ✓
- Added stack bounds preservation to postconditions (partial)
- Encountered Pulse quantifier issues with complex timestamp tracking
- File currently has verification errors due to incomplete quantifier proofs

## Next Steps
1. Revert to minimal working state (original code verifies)
2. Add timestamp tracking ONE function at a time
3. Use `assume_` temporarily for complex properties until proof strategy is solid
4. Focus first on proving "BLACK ⟹ valid timestamps" as this is most achievable
5. Leave "all BLACK" as remaining assume (requires count_gray or alternative approach)

## Key Insights
- Pulse prefers simple postconditions on low-level functions
- Complex invariants belong in loop annotations, not function specs
- Quantifier instantiation is fragile; explicit assertions help
- Array update reasoning requires manual guidance via assertions
