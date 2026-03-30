# CLRS.Ch26.MaxFlow.ImplTest — Spec Validation Test

## Overview

This file validates that the postcondition of `max_flow` (from `Impl.fsti`) is
**precise enough** to uniquely determine the output flow values for a concrete
network instance. The methodology follows the intent-formalization approach from
[microsoft/intent-formalization](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/).

All test functions return `bool` with runtime comparisons (`int_eq`) that
**survive extraction to C**, providing genuine runtime verification of computed
flow values. Ghost proofs are also present to verify postcondition completeness.

## Test Cases

### Test 1: Single-Edge Network (flow_value = 7) — Completeness Proven

**Network**: 2-vertex single-edge graph
- n = 2, source = 0, sink = 1
- Capacity matrix: cap[0→1] = 7, all other capacities = 0
- Expected max flow: 7 (saturate the single edge)
- **Runtime checks**: f01==7, f00==0, f10==0, f11==0, flow_val==7

### Test 2: Disconnected Network (flow_value = 0) — Completeness Proven

**Network**: 2-vertex disconnected graph
- n = 2, source = 0, sink = 1
- All capacities = 0
- Expected max flow: 0 (no path from source to sink)
- **Runtime checks**: f00==0, f01==0, f10==0, f11==0, flow_val==0

### Test 3: 3-Vertex Two-Path Network (flow_value = 20)

**Network**: 3-vertex graph with two augmenting paths
- n = 3, source = 0, sink = 2
- Edges: 0→1 cap 10, 1→2 cap 5, 0→2 cap 15
- Expected max flow: 20 (15 via 0→2 + 5 via 0→1→2)
- **Runtime check**: flow_val==20

### Test 4: Diamond Network (flow_value = 20)

**Network**: 4-vertex diamond with two disjoint paths
- n = 4, source = 0, sink = 3
- Edges: 0→1 cap 10, 0→2 cap 10, 1→3 cap 10, 2→3 cap 10
- Expected max flow: 20 (10 via 0→1→3 + 10 via 0→2→3)
- **Runtime check**: flow_val==20

### Test 5: Bottleneck Network (flow_value = 1)

**Network**: 3-vertex chain with bottleneck
- n = 3, source = 0, sink = 2
- Edges: 0→1 cap 100, 1→2 cap 1
- Expected max flow: 1 (limited by bottleneck edge 1→2)
- **Runtime check**: flow_val==1

## What Is Proven

### 1. Precondition Satisfiability
The precondition of `max_flow` is satisfiable:
- `valid_caps` established via `check_valid_caps_fn` + `valid_caps_intro` (no assume_)
- Array sizes, source/sink distinctness, and `SZ.fits` all hold

### 2. Postcondition Completeness (Tests 1-2)
After calling `max_flow`, the postcondition (`imp_valid_flow` + `no_augmenting_path`)
**uniquely determines** all flow values:

**Single-edge test**: `flow[0→1] = 7`, all other flows = 0

**Disconnected test**: All flows = 0 (zero-capacity edges force all flows to 0)

### 3. Runtime Result Verification (Tests 1-5)
All test functions return `bool` with `inline_for_extraction` `int_eq`
comparisons that survive extraction to C:
- Tests 1-2: Check all individual flow values AND the flow_val return value
- Tests 3-5: Check the flow_val return value against expected values

The extracted C code contains real `==` comparisons; `test_main.c` checks
the return values and reports PASS/FAIL.

### 4. MFMC Theorem Application (Test 1)
Proved that the `max_flow_min_cut_theorem` is applicable and yields:
there exists an s-t cut with capacity equal to the flow value (= 7).

## Soundness

- **Zero admits**: No `admit()` anywhere in the file
- **Zero assumes**: No `assume_` or `assume val` anywhere in the file

## Concrete Execution Results (C Extraction)

**Build command**: `make test-c` (in `autoclrs/ch26-max-flow/`)

```
=== CLRS Ch26 Max Flow: C Extraction Test ===
Test 1: Single-edge network (expected flow = 7) ... PASS
Test 2: Disconnected network (expected flow = 0) ... PASS
Test 3: 3-vertex two-path (expected flow = 20) ... PASS
Test 4: Diamond 4-vertex (expected flow = 20) ... PASS
Test 5: Bottleneck (expected flow = 1) ... PASS
=== All 5 tests passed ===
```

| Test | Network | Expected | Checks | Result |
|------|---------|----------|--------|--------|
| Single-edge (2v) | cap[0→1]=7 | 7 | All flows + flow_val | ✅ |
| Disconnected (2v) | all caps=0 | 0 | All flows + flow_val | ✅ |
| Two-path (3v) | 10+5+15 caps | 20 | flow_val | ✅ |
| Diamond (4v) | 4×cap 10 | 20 | flow_val | ✅ |
| Bottleneck (3v) | 100+1 caps | 1 | flow_val | ✅ |
