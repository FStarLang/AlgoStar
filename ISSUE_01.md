# ISSUE 01: Pulse generates unreduced lambda applications in proof obligations

## Summary

When calling a Pulse `fn` whose precondition references a recursive F*
function applied to erased sequences, from within a while loop with many
existential variables in its invariant, Pulse generates proof obligations
containing unreduced lambda applications. These lambdas are semantically
identity functions but are not reduced by the SMT solver, causing proof
failures.

## Reproduction

File: `ISSUE_01_lemma_call.fst`

```bash
cd /path/to/AutoCLRS
fstar.exe --include $(realpath ../pulse)/out/lib/pulse ISSUE_01_lemma_call.fst
```

## Error Pattern

The error message shows lambda terms where concrete values are expected:

```
Failed to prove pure property:
  ...
  count_ones ((fun _ _ _ _ _ _ _ _ _ _ _ -> __scolor_w2020) __vtop_w1818 __
        u_idx __ (...) __ (...) __ _if_hyp __ __)
    (FStar.SizeT.v n) ==
  FStar.SizeT.v ((fun _ _ _ _ _ _ _ _ _ _ _ -> __vtop_w1818) __vtop_w1818 __
        u_idx __ (...) __ (...) __ _if_hyp __ __)
```

The lambdas `(fun _ _ _ _ _ _ _ _ _ _ _ -> __scolor_w2020) ...` and
`(fun _ _ _ _ _ _ _ _ _ _ _ -> __vtop_w1818) ...` should beta-reduce to
just `__scolor_w2020` and `__vtop_w1818` respectively, but they are
presented to the SMT solver in unreduced form.

## Key Ingredients

The bug requires all of:

1. **A while loop with many existential variables** (8+ in our case:
   `vtop_w`, `vtime_w`, `scolor_w`, `sd_w`, `sf_w`, `spred_w`,
   `sstack_w`, `sscan_w`)

2. **A called function whose precondition references a recursive F*
   function** applied to one of the existential sequences (e.g.,
   `count_ones scolor (SZ.v n) == SZ.v vtop`)

3. **The call happening inside the while loop body**, especially after
   some local bindings (array reads, etc.)

## Impact

This blocks proving `vtop < n` in StackDFS's DFS algorithm. The proof
strategy requires:
- Tracking `count_gray(color, n) == stack_depth` as a loop invariant
- When a WHITE vertex is found: `count_gray < n` (since one vertex is
  non-GRAY), therefore `stack_depth < n`
- This requires calling a `count_gray_lt` lemma from inside the while
  loop body

Without this proof, three `assume_` calls remain in StackDFS (one per
call site that pushes onto the stack).

## Workaround

Use `assume_` for the facts that would be proven by the lemma call.
There is no known workaround that preserves the proof.

Attempted workarounds that also failed:
- Wrapping the lemma to take `nat` arguments instead of sequences
- Using `ghost fn` in Pulse instead of F* lemma
- Adding SMT patterns to make the lemma fire automatically

## Analysis

The lambda wrapping appears to come from how Pulse elaborates function
call precondition checks inside while loops. When checking whether the
current state satisfies the callee's precondition, Pulse creates a
continuation that captures all existential variables from the invariant.
If this continuation is not properly beta-reduced before being sent to
the SMT solver, the solver sees the unreduced lambdas and fails.

The issue may be related to how the Pulse checker handles the
interaction between:
- Existential variable instantiation (from the while loop invariant)
- Precondition checking for function calls
- Recursive F* function applications on erased types
