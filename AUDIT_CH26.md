# Audit Report — Chapter 26: Maximum Flow (Ford-Fulkerson / Edmonds-Karp)

**Date**: 2025-07-18  
**Auditor**: Copilot  
**Scope**: `ch26-max-flow/` — 5 files, 3321 lines total  
**Verification status**: All 5 `.checked` files present in `_cache/`

---

## File Inventory

| File | Lines | Role |
|------|------:|------|
| `CLRS.Ch26.MaxFlow.Spec.fst` | 1125 | Pure spec: flow networks, residual graphs, augmenting paths, cuts, MFMC theorem |
| `CLRS.Ch26.MaxFlow.fst` | 913 | Imperative Pulse implementation: BFS-based Ford-Fulkerson (Edmonds-Karp) |
| `CLRS.Ch26.MaxFlow.Proofs.fst` | 679 | Proofs: augmentation preserves validity, increases flow value |
| `CLRS.Ch26.MaxFlow.Complexity.fst` | 548 | O(VE²) complexity proof with ghost tick counter |
| `CLRS.Ch26.MaxFlow.Test.fst` | 56 | Smoke test on 3-vertex graph |

---

## 1. CLRS Fidelity

### FORD-FULKERSON-METHOD (CLRS §26.2, p. 714)

CLRS pseudocode:
```
FORD-FULKERSON-METHOD(G, s, t)
1  initialize flow f to 0
2  while there exists an augmenting path p in G_f
3      augment flow f along p
4  return f
```

**Implementation mapping** (`CLRS.Ch26.MaxFlow.fst`, `fn max_flow`):

| CLRS step | Implementation | Fidelity |
|-----------|---------------|----------|
| Line 1: init f to 0 | `zero_init_flow flow nn` | ✅ Exact match |
| Line 2: while ∃ augmenting path in G_f | `bfs_residual` returns `found: bool` | ✅ BFS on residual graph |
| Line 3: augment f along p | `find_bottleneck_imp` + `augment_imp` | ✅ Walk pred array, update flow |
| Line 4: return f | Returns `valid: bool` + flow in array | ✅ |

**Residual graph** (CLRS Definition 26.2): Correctly models both forward edges (`c(u,v) - f(u,v) > 0`) and backward edges (`f(v,u) > 0`). See `maybe_discover` and `Spec.residual_capacity` / `Spec.residual_capacity_backward`.

### Edmonds-Karp Specialization (CLRS p. 727)

CLRS specifies: "choose the augmenting path as a shortest path from s to t in the residual network, where each edge has unit distance (weight)."

- **BFS for shortest path**: ✅ `bfs_residual` performs standard BFS with queue, color (white=0/gray=1/black=2), and predecessor arrays. This guarantees shortest augmenting paths.
- **Augmentation via pred array**: ✅ `find_bottleneck_imp` and `augment_imp` walk the predecessor chain from sink to source — exactly as described in CLRS.

### Spec-level Ford-Fulkerson (`Spec.fst`)

Two versions provided:
1. `ford_fulkerson` (line 203): Takes an explicit list of paths — clean functional specification.
2. `ford_fulkerson_fuel` (line 215): Takes a `find_path` oracle + fuel bound — models the iterative algorithm more closely.

Both faithfully capture the CLRS method.

### Fidelity Gaps

| Gap | Severity | Detail |
|-----|----------|--------|
| **No skew symmetry** | Low | CLRS uses skew-symmetric flow (f(u,v) = −f(v,u)). Implementation uses non-negative flow representation with separate forward/backward residual capacity. This is a valid alternative formulation (equivalent). |
| **Adjacency matrix, not adjacency list** | Low | CLRS assumes adjacency-list representation. Implementation uses flat n×n matrix. This changes constant factors but not algorithmic complexity class. BFS scans all n neighbors per vertex instead of only adjacent ones. |
| **No antiparallel edge handling** | Low | CLRS §26.1 discusses handling antiparallel edges. The n×n matrix representation implicitly avoids the issue since `cap[u][v]` and `cap[v][u]` are independent cells. |

**Fidelity verdict: HIGH** — The implementation is a faithful Edmonds-Karp (BFS Ford-Fulkerson) with standard design choices for verified code.

---

## 2. Specification Strength

### Max-Flow Min-Cut Theorem (CLRS Theorem 26.6)

**Fully proven** in `Spec.fst`, line 1076: `max_flow_min_cut_theorem`.

Statement:
> If `f` is a valid flow and there is no augmenting path (bottleneck ≤ 0 for all source-to-sink paths), then there exists an s-t cut `(S,T)` such that `|f| = c(S,T)`.

This encodes the (2) ⟹ (3) direction of Theorem 26.6 — the constructive direction that matters for algorithmic correctness. The proof:
1. Defines `S = {v : reachable from s in G_f}` via bounded `is_reachable` (line 699+).
2. Shows `s ∈ S`, `t ∉ S` (by contradiction through `lemma_sink_not_reachable`).
3. Shows no S→T edge has residual capacity (`no_cross_residual`).
4. Proves `|f| = net_flow_across(S,T) = c(S,T)` via Lemma 26.4 + saturation.

The proof is **zero-admit** and uses `IndefiniteDescription` for existential witnesses and `Fin.pigeonhole` for path shortening — both sound.

### Flow Conservation (CLRS Definition 26.1)

**Fully proven** in `Proofs.fst`, line 628: `augment_preserves_valid`.

Statement: For any valid flow and valid augmenting path with `bn ≤ bottleneck`, the augmented flow satisfies:
- Capacity constraints: `0 ≤ f'(u,v) ≤ c(u,v)` for all `u,v`
- Flow conservation: `Σ f'(v,u) = Σ f'(u,v)` for all `u ≠ s,t`

The proof handles three cases for each vertex `w`:
- `w ∉ path`: sums unchanged (`lemma_augment_aux_preserves_vertex_sums`)
- `w` intermediate on path: incoming and outgoing augmentations cancel (`lemma_augment_aux_conservation`)
- `w = source` or `w = sink`: not required to conserve

### Capacity Constraints

Proven at two levels:
1. **Spec-level**: `lemma_augment_preserves_capacity` (Proofs.fst, line 323) — inductive proof along path.
2. **Imperative-level**: `check_capacity_fn` (MaxFlow.fst) performs runtime verification and produces a proof that `∀ idx < n*n. 0 ≤ flow[idx] ≤ cap[idx]`.

### Flow Value Increases

**Fully proven** in `Proofs.fst`, line 656: `augment_increases_value`.

Statement: After augmentation, `flow_value(f') > flow_value(f)`.

### Supporting Theorems

| CLRS Result | Location | Status |
|-------------|----------|--------|
| Lemma 26.4: `|f| = net flow across any cut` | Spec.fst:582 `lemma_flow_value_eq_net_flow` | ✅ Proven |
| Corollary 26.5: Weak duality `|f| ≤ c(S,T)` | Spec.fst:597 `weak_duality` | ✅ Proven |
| Theorem 26.6: Max-flow min-cut | Spec.fst:1076 `max_flow_min_cut_theorem` | ✅ Proven |
| Zero flow valid | Proofs.fst:672 `zero_flow_valid` | ✅ Proven |
| Path shortening (pigeonhole) | Spec.fst:877+ `lemma_shorten_path` | ✅ Proven |

### Specification Gap: Imperative ↔ Spec Linkage

**Critical observation**: The imperative `max_flow` function's postcondition guarantees:
```
valid ==> imp_valid_flow flow_seq' cap_seq (SZ.v n) (SZ.v source) (SZ.v sink)
```

This is established via a **runtime check** (`check_imp_valid_flow_fn`), not by a static proof that the BFS loop maintains `valid_flow`. The main loop invariant only tracks:
- Array lengths
- `SZ.fits` constraints

It does **not** carry `valid_flow` or relate the imperative state to the spec-level `augment`. This means:
1. The spec-level theorems (MFMC, conservation, etc.) are fully proven in isolation.
2. The imperative implementation is memory-safe and terminates.
3. The connection between them relies on the runtime validity check returning `true`.

This is a **defense-in-depth** approach: if the implementation has a bug, the runtime check catches it and returns `false`. However, it means the static guarantee is weaker than a full refinement proof.

**Specification strength verdict: STRONG for spec-level theory; MODERATE for imperative correctness** — The MFMC theorem and all supporting lemmas are fully proven. The imperative implementation validates its output at runtime rather than carrying the invariant through the loop.

---

## 3. Complexity

### Edmonds-Karp O(VE²) (CLRS Theorem 26.8)

**Proven** in `Complexity.fst`, line 315: `edmonds_karp_complexity`.

The proof structure:
1. **Ghost tick counter**: `augmentation_cost(E) = 2E` (BFS + path walk) — line 35.
2. **Max augmentations**: `max_augmentations(V, E) = V * E` — line 297.
3. **Total cost**: `V * E * 2E = O(VE²)` — line 315.

Corollaries:
- Dense graphs (E = V²): O(V⁵) — line 348 `edmonds_karp_dense_graph_complexity`.
- Sparse graphs (E = O(V)): O(V³) — line 361 `edmonds_karp_sparse_graph_complexity`.
- Full tick-counting theorem: line 510 `edmonds_karp_verified_complexity`.

### Strength of Complexity Proof

| CLRS Component | Implementation | Status |
|----------------|---------------|--------|
| Lemma 26.7: distances non-decreasing | `lemma_distances_nondecreasing` (line 55) | ⚠️ **Vacuous** — see below |
| Lemma 26.8: each edge critical ≤ V/2 times | `lemma_edge_critical_bound` (line 299) | ⚠️ **Trivial** (ensures True) |
| Critical edge creation per augmentation | `lemma_augmentation_creates_critical_edge` (line 207) | ✅ Proven by induction |
| O(VE²) arithmetic bound | `edmonds_karp_complexity` (line 315) | ✅ Proven |

### Critical Weakness in Complexity Proof

**`shortest_path_distance`** (line 40) is defined as:
```fstar
if source = v then 0 else n
```
This is a **constant function** independent of the flow. Consequently:

1. **`lemma_distances_nondecreasing`** (line 55) is vacuously true — both sides of the inequality are equal regardless of augmentation. The actual CLRS Lemma 26.7 requires a genuine BFS distance computation.

2. **`lemma_edge_critical_bound`** (line 299) has postcondition `True` — it proves nothing. The comment correctly describes the CLRS argument but the formal statement is trivial.

The arithmetic bound `max_augmentations * augmentation_cost ≤ V * E * 2E` is correctly proven, but it relies on `max_augmentations = V * E` being taken as a **definition** rather than being derived from Lemmas 26.7–26.8. The chain of reasoning is:
- ✅ Each augmentation creates ≥ 1 critical edge (proven).
- ❌ Each edge becomes critical at most V/2 times (stated but not proven — trivial lemma).
- ❌ Therefore total augmentations ≤ VE (not derived from the above; defined directly).

**Complexity verdict: PARTIAL** — The O(VE²) arithmetic is proven, and critical-edge creation is proven, but the key lemmas (distance monotonicity, criticality bound) that justify the augmentation count are either vacuous or trivially `True`.

---

## 4. Code Quality

### Strengths

1. **Clean decomposition**: BFS initialization, neighbor exploration, BFS main loop, bottleneck, augmentation — each is a separate `fn` with clear pre/post conditions.
2. **Defensive programming**: Both `find_bottleneck_imp` and `augment_imp` handle `u_int < 0` (unreachable predecessor) gracefully by jumping to source.
3. **Runtime validity check**: `check_imp_valid_flow_fn` provides defense-in-depth — even if there's a bug in the augmentation logic, the caller sees `valid = false`.
4. **Proper resource cleanup**: BFS workspace (`color`, `pred`, `queue`) is allocated and freed within `max_flow`.
5. **Total helper functions**: `seq_get` and `seq_get_sz` avoid partial `Seq.index`.

### Concerns

| Issue | Location | Severity |
|-------|----------|----------|
| **No termination proof for main loop** | `max_flow` while-loop (line 858+) | Medium — loop has no decreasing measure; relies on BFS eventually finding no path. With integer capacities this is guaranteed but not formally proven. |
| **Bottleneck initialized to INT_MAX** | `find_bottleneck_imp` line ~520 (`2147483647`) | Low — magic number; should use a named constant. Works correctly for reasonable inputs but overflows for flows near INT_MAX. |
| **BFS queue bounded by n** | `maybe_discover` checks `vt <^ n` | Low — each vertex discovered at most once, so n is sufficient. But the bound is implicit; no explicit proof that vertices aren't enqueued twice. |
| **No skew-symmetry in augmentation** | `augment_imp` | Low — forward/backward case split mirrors the spec `augment_edge`, but the if-condition uses `cap_val - flow_fwd > 0` which may differ from the BFS discovery condition when both forward and backward residual are positive. |
| **README accuracy** | README.md | Medium — see §6. |

### Style

- Consistent use of `#push-options`/`#pop-options` for Z3 settings per function.
- Good use of erased/ghost parameters for spec-level sequences.
- Loop invariants are explicit and readable.
- Comments explain non-obvious design decisions.

**Code quality verdict: GOOD** — Well-structured imperative code with careful pre/post conditions. Main concern is the missing termination argument for the outer loop.

---

## 5. Proof Quality — Admits and Assumes

### Complete Inventory

| # | File | Line | Construct | Context |
|---|------|------|-----------|---------|
| 1 | `CLRS.Ch26.MaxFlow.Test.fst` | 42 | `assume_ (pure (valid_caps sc2 (SZ.v n)))` | Test only — assumes capacity matrix is non-negative after manual array writes. Reasonable for test harness; not propagated to production code. |

**Total admits/assumes in production code: 0**  
**Total assumes in test code: 1**

### Vacuous Proofs (Not Admits, but Weak)

| # | File | Line | Function | Issue |
|---|------|------|----------|-------|
| 1 | `Complexity.fst` | 55 | `lemma_distances_nondecreasing` | Postcondition is true by definition of `shortest_path_distance` being constant w.r.t. flow |
| 2 | `Complexity.fst` | 299 | `lemma_edge_critical_bound` | Postcondition is literally `True` |
| 3 | `Complexity.fst` | 297 | `max_augmentations` | Defined as `V * E` directly — not derived from Lemmas 26.7/26.8 |

These are **not** unsoundnesses — the proofs are accepted by F* — but they represent gaps in the logical chain where CLRS-level reasoning is assumed via definition rather than proven.

### Proof Techniques

| Technique | Usage |
|-----------|-------|
| Structural induction on lists | `augment_preserves_capacity`, `augment_aux_conservation`, `augment_increases_value_aux` |
| Quantifier instantiation (`forall_intro`, `move_requires`) | Conservation and capacity proofs |
| Pigeonhole principle (`FStar.Fin.pigeonhole`) | Path shortening in MFMC proof |
| Indefinite description (`IndefiniteDescription`) | Existential witness extraction for reachability |
| Induction on `|S|` (set cardinality) | `lemma_ss_outer_zero` — S×S cancellation |
| Bounded reachability with fuel | `is_reachable` / `check_any_predecessor` — avoids higher-order SMT issues |

**Proof quality verdict: EXCELLENT for Spec+Proofs (zero admits, deep lemmas); FAIR for Complexity (vacuous key lemmas)**

---

## 6. Documentation Accuracy

### README.md

The README is **significantly outdated**. It describes a different (earlier) version of the code:

| README claim | Actual code | Issue |
|--------------|------------|-------|
| "simplified version that iteratively augments flow edge-by-edge" | Full BFS-based Edmonds-Karp with path augmentation | **Wrong** — README describes a trivial greedy algorithm |
| "Does not use admits or assumes" | 0 admits in production code | ✅ Correct |
| "does not use BFS-based path finding (Edmonds-Karp)" | `bfs_residual` implements full BFS | **Wrong** — README explicitly disclaims BFS but code has it |
| "Runs exactly n rounds" | While-loop until no augmenting path | **Wrong** |
| "138 lines, verified ✅" | 913 lines | **Wrong** |
| Files listed: no Spec/Proofs/Complexity | These files exist and are verified | **Incomplete** |
| "does not prove full functional correctness of max flow value" | MFMC theorem fully proven | **Wrong** |

**Documentation verdict: POOR** — README describes a prior version of the code and is misleading in multiple critical ways.

### In-Code Documentation

- Module headers in each file are accurate and helpful.
- Comments in the Pulse code are clear and match the code.
- CLRS theorem references (26.4, 26.5, 26.6, 26.7, 26.8) are correctly cited.
- The Complexity.fst header comment claims "NO admits for core complexity bounds" — technically true since the weaknesses are vacuous proofs, not admits.

---

## 7. Task List

### Priority 0 (Critical)

| ID | Task | Rationale |
|----|------|-----------|
| P0.1 | **Rewrite README.md** | README describes a completely different algorithm than what's implemented. Must document: BFS-based Edmonds-Karp, 5-file structure, MFMC theorem, 3321 LOC. |

### Priority 1 (High)

| ID | Task | Rationale |
|----|------|-----------|
| P1.1 | **Strengthen main loop invariant** | The `max_flow` while-loop invariant should carry `imp_valid_flow` (or a weaker precursor) so the postcondition doesn't depend on the runtime check. This would upgrade the imperative correctness from "runtime-verified" to "statically proven". |
| P1.2 | **Prove or properly axiomatize shortest-path distance monotonicity** | `shortest_path_distance` (Complexity.fst:40) is a constant — replace with a proper BFS distance abstraction and prove Lemma 26.7 non-vacuously. |
| P1.3 | **Prove edge criticality bound** | `lemma_edge_critical_bound` (Complexity.fst:299) has postcondition `True`. State and prove the actual bound: each edge becomes critical ≤ V/2 times. |
| P1.4 | **Add termination proof for main loop** | The `max_flow` while-loop needs a decreasing measure. Natural candidate: `max_flow_value - current_flow_value` (bounded by sum of capacities, decreases by ≥1 per iteration for integer capacities). |

### Priority 2 (Medium)

| ID | Task | Rationale |
|----|------|-----------|
| P2.1 | **Establish imperative-spec refinement** | Connect the Pulse `augment_imp` to the spec-level `augment_edge` with a simulation lemma, so each loop iteration provably corresponds to a spec-level `ford_fulkerson_step`. |
| P2.2 | **Strengthen test** | The test uses `assume_` for `valid_caps`. Either prove it from the array writes or add multiple test cases with varied topologies. |
| P2.3 | **Named constant for INT_MAX** | Replace `2147483647` in `find_bottleneck_imp` with a named constant. |
| P2.4 | **Derive augmentation bound from criticality** | In Complexity.fst, derive `max_augmentations = V * E` from `lemma_augmentation_creates_critical_edge` + `lemma_edge_critical_bound`, rather than defining it directly. |

### Priority 3 (Low)

| ID | Task | Rationale |
|----|------|-----------|
| P3.1 | **Prove BFS correctness** | BFS in `bfs_residual` lacks a postcondition relating the pred array to an actual shortest path in the residual graph. Adding this would close the gap between the BFS implementation and the Edmonds-Karp spec. |
| P3.2 | **Add adjacency-list variant** | The n×n matrix representation means BFS is O(V²) per iteration instead of O(V+E). An adjacency-list variant would achieve true O(VE²). |
| P3.3 | **Prove anti-symmetry of forward/backward augmentation** | Show that the BFS discovery condition and the augmentation condition agree — i.e., if BFS discovered `v` from `u` via forward residual, then `augment_imp` will take the forward branch. |

---

## Summary

| Dimension | Rating | Notes |
|-----------|--------|-------|
| **CLRS Fidelity** | ★★★★☆ | Faithful Edmonds-Karp with BFS; minor representation differences |
| **Specification Strength** | ★★★★☆ | MFMC fully proven; imperative link via runtime check |
| **Complexity** | ★★★☆☆ | O(VE²) arithmetic proven; key CLRS lemmas vacuous |
| **Code Quality** | ★★★★☆ | Clean, well-structured Pulse; missing termination proof |
| **Proof Quality** | ★★★★★ | Zero admits in 2917 lines of Spec+Proofs+Complexity |
| **Documentation** | ★★☆☆☆ | README severely outdated; in-code docs good |

**Overall: STRONG implementation with excellent pure-spec proofs. Main weaknesses are the outdated README, vacuous complexity lemmas, and the runtime-check-based imperative postcondition.**
