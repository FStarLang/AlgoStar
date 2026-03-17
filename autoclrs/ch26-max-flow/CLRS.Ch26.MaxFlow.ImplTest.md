# CLRS.Ch26.MaxFlow.ImplTest — Spec Validation Test

## Overview

This file validates that the postcondition of `max_flow` (from `Impl.fsti`) is
**precise enough** to uniquely determine the output flow values for a concrete
network instance. The methodology follows the intent-formalization approach from
[microsoft/intent-formalization](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/).

## Test Cases

### Test 1: Single-Edge Network (flow_value = 7)

**Network**: 2-vertex single-edge graph
- n = 2, source = 0, sink = 1
- Capacity matrix: cap[0→1] = 7, all other capacities = 0
- Expected max flow: 7 (saturate the single edge)

### Test 2: Disconnected Network (flow_value = 0)

**Network**: 2-vertex disconnected graph
- n = 2, source = 0, sink = 1
- All capacities = 0
- Expected max flow: 0 (no path from source to sink)

## What Is Proven

### 1. Precondition Satisfiability
The precondition of `max_flow` is satisfiable:
- `valid_caps` established via `check_valid_caps_fn` + `valid_caps_intro` (no assume_)
- Array sizes, source/sink distinctness, and `SZ.fits` all hold

### 2. Postcondition Completeness (Main Result)
After calling `max_flow`, the postcondition (`imp_valid_flow` + `no_augmenting_path`)
**uniquely determines** all four flow values:

**Single-edge test**:
- `flow[0→1] = 7` (max flow on the single edge)
- `flow[0→0] = 0`, `flow[1→0] = 0`, `flow[1→1] = 0`

**Disconnected test**:
- All flows = 0 (zero-capacity edges force all flows to 0)

**Proof technique** (single-edge):
1. **Bridge lemma** (`imp_valid_flow_implies_valid_flow`): Converts opaque
   `imp_valid_flow` to transparent `valid_flow` from `Spec.fst`
2. **Capacity constraints** (from `valid_flow`): Zero-capacity edges force
   flow = 0, giving flow[0→0] = flow[1→0] = flow[1→1] = 0
3. **Optimality constraint** (from `no_augmenting_path`): Instantiating with
   path [0;1] gives `bottleneck([0;1]) ≤ 0`. Unfolding the bottleneck
   computation:
   - If `flow[0→1] < 7`, residual capacity = 7 − flow[0→1] > 0, so
     bottleneck > 0, contradicting ≤ 0
   - Therefore `flow[0→1] ≥ 7`, combined with capacity constraint `≤ 7`,
     gives `flow[0→1] = 7`

### 3. Return Value Correctness
The strengthened `max_flow` signature now returns `fv: int` with:
- `fv == imp_flow_value flow_seq' n source` (return value matches mathematical flow value)
- `fv >= 0` (flow value is non-negative)

Both tests verify the return value:
- Single-edge: `assert (pure (flow_val == 7))`
- Disconnected: `assert (pure (flow_val == 0))`

This validates that the return value is sufficiently constrained to uniquely
determine the flow value for both success (positive flow) and "error" (zero flow) cases.

### 4. Flow Value
- Single-edge: `flow_value(flow, 2, source=0) = 7`
- Disconnected: `flow_value(flow, 2, source=0) = 0`

### 5. MFMC Theorem Application
Proved that the `max_flow_min_cut_theorem` is applicable and yields:
there exists an s-t cut with capacity equal to the flow value (= 7).

## Pure Helper Lemmas

| Lemma | Purpose |
|-------|---------|
| `instantiate_no_aug_path` | Instantiates universally quantified `no_augmenting_path` with a concrete path |
| `single_edge_completeness` | Derives exact flow values from `valid_flow` + `no_augmenting_path` |
| `single_edge_flow_value` | Proves flow value = 7 |
| `single_edge_mfmc` | Applies MFMC theorem |
| `disconnected_completeness` | Derives all flows = 0 for disconnected network |
| `disconnected_flow_value` | Proves flow value = 0 for disconnected network |

## Soundness

- **Zero admits**: No `admit()` anywhere in the file
- **Zero assumes**: No `assume_` or `assume val` anywhere in the file
- **Runtime check only for valid_caps**: Uses `check_valid_caps_fn` + `valid_caps_intro`
  (same pattern as existing `Test.fst`)

## Spec Strengthening (2026-03-17)

The `max_flow` signature was strengthened to return the flow value:

| Change | Before | After |
|--------|--------|-------|
| Return type | `unit` | `returns fv: int` |
| Flow value in postcondition | Not exposed | `fv == imp_flow_value flow_seq' n source` |
| Non-negativity | Not stated | `fv >= 0` |
| `imp_flow_value` exported | No | Yes (via `Impl.fsti`) |
| `lemma_imp_flow_value_eq` exported | No | Yes (connects to `Spec.flow_value`) |

**Weakness identified**: The original spec returned `unit`, preventing callers
from directly obtaining the computed flow value. The implementation already
tracked `flow_val == imp_flow_value` in its loop invariant but discarded it.
The `fv >= 0` invariant was also conditional on the loop continuing, losing
non-negativity information at termination.

**Fix**: Added `returns fv: int` with `fv == imp_flow_value flow_seq' n source /\ fv >= 0`
to the postcondition. Made `fv >= 0` unconditional in the loop invariant (sound:
flow value starts at 0 and strictly increases with each augmentation).

## Spec Findings

The postcondition of `max_flow` is **fully precise** for both test cases:

| Property | Assessment |
|----------|-----------|
| Precondition strength | ✅ Satisfiable — `valid_caps_intro` bridges runtime check to abstract predicate |
| Postcondition precision | ✅ Complete — uniquely determines all flow values |
| Return value constraint | ✅ Uniquely determined — `fv == imp_flow_value` + bridge lemma gives exact value |
| `imp_valid_flow` usability | ✅ Bridge lemma effectively connects to `Spec.valid_flow` |
| `no_augmenting_path` usability | ✅ Can instantiate with concrete paths to derive flow bounds |
| MFMC theorem usability | ✅ Applicable via bridge lemma + `no_augmenting_path` |
| Success case (positive flow) | ✅ Return value = 7 for single-edge network |
| Zero-flow case (disconnected) | ✅ Return value = 0 for disconnected network |
