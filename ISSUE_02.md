# ISSUE 02: Seq.index refinement failure in Pulse `ensures` clauses under `exists*`

## Summary

When a Pulse function's `ensures` clause uses `Seq.index s i` inside a
`pure()` block where `s` is existentially quantified (via `exists*`), the
refinement check `i < Seq.length s` fails, even when `Seq.length s == n`
and `i < n` appear as **earlier conjuncts** in the same `pure()` block.

This prevents stating precise postconditions about array updates (e.g.,
"the element at index `i` is now `v`" or "all other elements are
unchanged").

## Reproduction

File: `ISSUE_02_seq_index_ensures.fst`

```bash
cd /path/to/AutoCLRS
fstar.exe --include $(realpath ../pulse)/out/lib/pulse ISSUE_02_seq_index_ensures.fst
```

The file contains 4 test cases:
- **Case 1** (`set_and_report_FAILS`): Direct `Seq.index s' (SZ.v idx) == value` — **FAILS**
- **Case 2** (`set_and_report_WORKS`): Same with `safe_index` wrapper — **WORKS**
- **Case 3** (`set_and_preserve_FAILS`): Quantified preservation — **FAILS**
- **Case 4** (`set_and_preserve_WORKS`): Same with `safe_index` — **WORKS**

## Error Message

```
* Error 19 at ISSUE_02_seq_index_ensures.fst(68,10-68,15):
  - Ill-typed term:
      (exists* (s':FStar.Seq.Base.seq Prims.int).
        Pulse.Lib.Array.PtsTo.pts_to arr s' **
        pure (FStar.Seq.Base.length s' == FStar.SizeT.v n /\
        FStar.Seq.Base.index s' (FStar.SizeT.v idx) == value))
  - Expected a term of type slprop
  - See also FStar.Seq.Base.fsti(32,40-32,52)
```

The error references `FStar.Seq.Base.fsti(32,40-32,52)` which is:
```fstar
val index: #a:Type -> s:seq a -> i:nat{i < length s} -> Tot a
```

## Root Cause

`Seq.index` has signature `s:seq a -> i:nat{i < length s} -> a`. The
refinement `i < length s` must hold for the term to be well-typed.

In the `ensures exists* s'. ... pure (Seq.length s' == n /\ Seq.index s' i == v)`,
`s'` is existentially quantified. When Pulse elaborates the postcondition
type, it checks that `Seq.index s' i` is well-typed. This requires
proving `i < Seq.length s'`.

The fact `Seq.length s' == n` is a **sibling conjunct** in the same
`pure()` block, and `i < n` is known from the precondition. However,
Pulse's elaboration does **not** use sibling conjuncts to discharge
refinement types during type-checking of the postcondition expression.

This is a well-formedness check, not a proof obligation — it happens at
elaboration time before any SMT interaction.

## Workaround

Define a guarded index wrapper that avoids the refinement:

```fstar
let safe_index (s: Seq.seq int) (i: nat) : int =
  if i < Seq.length s then Seq.index s i else 0
```

Then use `safe_index s' (SZ.v idx) == value` instead of
`Seq.index s' (SZ.v idx) == value` in postconditions.

The wrapper is always well-typed since it doesn't have a refinement on
its index parameter. When `i < Seq.length s` holds (which it does
from the context), `safe_index s i == Seq.index s i`, so the
postcondition is equivalent.

## Impact

This blocks adding precise update postconditions to helper functions in
the StackDFS module. Without knowing exactly what a function modified,
callers cannot re-establish quantified invariants (e.g., "all BLACK
vertices have valid timestamps") after the call.

Specifically, this prevents:
- `finish_vertex` from stating `Seq.index scolor' (SZ.v u) == 2` (u became BLACK)
- `discover_vertex_dfs` from stating `Seq.index sd' (SZ.v vv) == time+1` (discovery time set)
- Any function from stating element-wise preservation via quantified `Seq.index`

The `safe_index` workaround helps at the spec level but adds complexity
to SMT reasoning since the solver must unfold the wrapper to connect
`safe_index` facts to `Seq.index`-based invariants.

## Notes

- This issue is **specific to existentially quantified sequences** in
  `ensures`. Using `Seq.index` in `requires` or in loop invariants
  (where the sequence is bound by the invariant's own `exists*`) works
  fine when the length constraint appears **before** the index access.

- The conjunct ordering matters in `requires` and `invariant` blocks
  (left-to-right processing), but the issue in `ensures` seems more
  fundamental — the existential prevents the length from being available
  during elaboration.
