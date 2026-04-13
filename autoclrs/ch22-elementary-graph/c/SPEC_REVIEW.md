# Ch22 C Code — Specification Review

## Overview

This document reviews the specification gaps between the C code in `ch22/c/` and
the Pulse implementations in `ch22/*.Impl.fsti`.

## Issue 1: `_include_pulse` blocks with computational code

### DFS.c
- `_include_pulse(open CLRS.Ch22.DFS.C.BridgeLemmas)` — OK (module open)
- `_include_pulse(open CLRS.Ch22.DFS.C.FinishStep)` — OK (module open)
- `_ghost_stmt(CLRS.Ch22.DFS.C.FinishStep.finish_ordering_step ...)` — calls a ghost fn
  that uses `assume_`. **This is an assume — must be eliminated.**

### FinishStep.fst
- `finish_ordering_step` uses `assume_ (pure (pred_finish_ok_c ...))` — **UNSOUND**.
  The `BridgeLemmas.finish_ordering_preserved` lemma exists and proves this,
  but `finish_ordering_step` doesn't call it; it just assumes. Must be fixed to
  call the lemma properly.

### BFS.c and TopologicalSort.c
- No `_include_pulse` blocks with computational code. ✓

## Issue 2: Complexity instrumentation to remove

### BFS.c
- No complexity code. ✓

### DFS.c
- No explicit complexity counter. ✓
- The `fuel` parameter is for termination, not complexity. Keep it.

### TopologicalSort.c
- No complexity code. ✓

### Impl.fsti files
- All three .fsti files have complexity postconditions (`cf >= c0`, `cf - c0 <= ...`).
  These are in the fsti and we are told NOT to change fsti. The C code doesn't need
  to prove these — they apply to the Pulse implementation only.

## Issue 3: BFS Specification Gaps

### Impl.fsti proves (that C code does NOT):
1. **Reachability**: `reachable_in sadj n source w (dist[w])` for all discovered w
2. **Completeness**: every reachable vertex is discovered
3. **Predecessor edge validity**: `adj[pred[v]*n+v] != 0` when pred[v] valid

### C code currently proves:
1. ✓ Source visited with dist[source] = 0
2. ✓ Distance soundness: visited ⟹ dist ≥ 0
3. ✓ Predecessor distance consistency: pred[v] < n ⟹ color[pred[v]] ≠ 0 ∧ dist[v] = dist[pred[v]] + 1
4. ✗ **Missing**: Predecessor edge validity (adj[pred[v]*n+v] ≠ 0)
5. ✗ **Missing**: Reachability (reachable_in)
6. ✗ **Missing**: Completeness

### Plan for BFS:
- **Predecessor edge validity**: Add `_ensures` and maintain through loop invariants.
  This is straightforward — when we set `pred[v] = u`, we already checked `adj[u*n+v] != 0`.
- **Reachability**: Requires defining `reachable_in` in terms of c2pulse types (Int32/SizeT).
  Need bridge lemmas. This is complex but doable — the key insight is that when we set
  `pred[v] = u` and `dist[v] = dist[u] + 1`, we can inductively prove reachability.
- **Completeness**: Very hard to prove in C directly. Requires showing all neighbors of
  visited vertices eventually get queued. May need substantial ghost state.

### Priority: pred_edge_validity (easy), reachability (medium), completeness (hard)

## Issue 4: DFS Specification Gaps

### Impl.fsti proves (that C code may not):
1. ✓ All vertices BLACK
2. ✓ d[u] > 0, f[u] > 0, d[u] < f[u]
3. ✗ **Missing**: Timestamp bounds d[u] ≤ 2n, f[u] ≤ 2n
4. ✓ pred_edge_ok (edge exists, parent non-white, d[pred[v]] < d[v])
5. ✓ Predecessor finish ordering (f[v] < f[pred[v]])

### DFS issues:
- `assume_(pure False)` in unreachable branches — **UNSOUND**. Must prove these
  branches are truly unreachable, or use a proper counting invariant.
- `finish_ordering_step` uses `assume_` — **UNSOUND**. Must call the actual lemma.
- **Timestamp bounds**: The fsti requires `d[u] ≤ 2n` and `f[u] ≤ 2n`. The C code
  uses `time_ref[0] < 65534` as an overflow guard but doesn't prove the 2n bound.
  Need a counting invariant (total time ≤ 2n since each vertex gets discovered and
  finished exactly once).

### Plan for DFS:
1. Fix `finish_ordering_step` to call `finish_ordering_preserved` instead of `assume_`.
2. Add a counting invariant to prove `time_ref[0] ≤ 2*n`, eliminating the `assume_(pure False)`.
3. Add timestamp bound postconditions.

## Issue 5: TopologicalSort Specification Gaps

### Impl.fsti proves (that C code does NOT):
1. ✗ **Missing**: All elements non-negative (`output[i] ≥ 0`) — trivially true for size_t
2. ✗ **Missing**: All elements distinct (`all_distinct`)
3. ✗ **Missing**: Valid topological order (`is_topological_order`)
4. ✗ **Missing**: DAG precondition (`~has_cycle`)

### C code currently proves:
1. ✓ All output entries < n (valid vertex indices)

### This is the weakest C implementation — essentially only proves safety.

### Plan for TopologicalSort:
- **Distinctness**: Track a visited set. When dequeuing u, assert u hasn't been output before.
- **Topological order**: For each edge (u,v), must prove u appears before v in output.
  This requires maintaining that when u is output, all its predecessors have already
  been output. Kahn's algorithm naturally ensures this via in-degree tracking.
- **DAG precondition**: The fsti requires `~has_cycle` as precondition. The C code
  must accept this as a precondition (via `_requires`).

## Work Priority

1. **DFS: Remove assumes** — Fix finish_ordering_step, eliminate assume_(pure False)
2. **BFS: Add pred edge validity** — Easy invariant maintenance
3. **BFS: Add reachability** — Medium difficulty, needs bridge lemmas
4. **TopologicalSort: Add distinctness and topo order** — Significant work
5. **BFS: Add completeness** — Hard, may need ghost state

## Checklist

- [ ] DFS: Fix FinishStep.fst to call lemma instead of assume_
- [ ] DFS: Add counting invariant to eliminate assume_(pure False)  
- [ ] DFS: Add timestamp bounds (d[u] ≤ 2n, f[u] ≤ 2n)
- [ ] BFS: Add predecessor edge validity postcondition
- [ ] BFS: Add reachability specification with bridge lemmas
- [ ] BFS: Add completeness specification
- [ ] TopSort: Add DAG precondition
- [ ] TopSort: Add all_distinct specification
- [ ] TopSort: Add is_topological_order specification
