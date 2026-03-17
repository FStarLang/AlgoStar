# Stack Spec Validation — ImplTest.md

## Source

Adapted from
[Test.Stack.fst](https://github.com/microsoft/intent-formalization/blob/main/eval-autoclrs-specs/intree-tests/ch10-elementary-ds/Test.Stack.fst)
in the [intent-formalization](https://github.com/microsoft/intent-formalization)
repository (spec-validation methodology from
[arXiv:2406.09757](https://arxiv.org/abs/2406.09757)).

## Test Description

**File:** `CLRS.Ch10.Stack.ImplTest.fst`

The test creates a stack of capacity 5, pushes three integers `[1; 2; 3]`, and
then verifies all operations against concrete expected outputs.

### Operations tested

| Step | Operation | Expected result | Proven? |
|------|-----------|-----------------|---------|
| 1 | `create_stack int 0 5sz` | Empty stack | ✅ |
| 2 | `stack_empty` | `true` | ✅ |
| 3–5 | `push 1`, `push 2`, `push 3` | Contents = `[1; 2; 3]` | ✅ |
| 6 | `stack_empty` | `false` | ✅ |
| 7 | `peek` | Returns `3` (LIFO top) | ✅ |
| 8 | `pop` | Returns `3` (LIFO) | ✅ |
| 9 | `peek` | Returns `2` | ✅ |
| 10 | `pop` | Returns `2` | ✅ |
| 11 | `pop` | Returns `1` | ✅ |
| 12 | `stack_empty` | `true` | ✅ |

### What is proven

1. **Precondition satisfiability**: All five operations (`create_stack`, `push`,
   `pop`, `peek`, `stack_empty`) are successfully called, proving their
   preconditions are satisfiable.

2. **Pop postcondition precision**: After pushing `[1; 2; 3]`, the `pop`
   postcondition `exists* xs. stack_inv s xs ** pure (L.append xs [x] == contents)`
   is strong enough for Z3 to determine that `x == 3`, `x == 2`, `x == 1` in
   successive pops. The append-based decomposition uniquely identifies the
   popped element.

3. **Peek postcondition precision**: The strengthened peek postcondition
   `pure (Cons? contents /\ (if Cons? contents then x == L.last contents else True))`
   directly identifies the top element as `L.last contents`. Z3 normalizes
   `L.last [1;2;3]` to `3` and `L.last [1;2]` to `2` without any auxiliary
   lemmas. This is a significant improvement over the original `Prims.exists`
   formulation which required helper lemmas for classical elimination.

4. **stack_empty precision**: Returns `true` iff the contents list is empty.
   Verified at both empty and non-empty states.

5. **LIFO ordering**: The test verifies full LIFO behavior — elements come out
   in reverse order of insertion: push `1, 2, 3` → pop `3, 2, 1`.

### Auxiliary lemmas needed

**None.** The strengthened `peek` postcondition eliminates the need for helper
lemmas. Previously, `peek_last_3` and `peek_last_2` were required to eliminate
`Prims.exists` from the old `peek` postcondition. With the new direct `L.last`
formulation, Z3 handles everything automatically.

### Spec changes made

**peek postcondition strengthened** (2026-03-17):
- **Before:** `pure (exists (init:list t). L.append init [x] == reveal contents)`
  — Used `Prims.exists` (pure existential), requiring helper lemmas for
  classical elimination in tests.
- **After:** `pure (Cons? (reveal contents) /\ (if Cons? (reveal contents) then x == L.last (reveal contents) else True))`
  — Directly specifies the return value as `L.last contents`, usable by Z3
  without helper lemmas. The `if Cons?` guard makes the expression well-typed
  even though `L.last` has a `{Cons? l}` refinement.

### Verification

- **Admits**: 0
- **Assumes**: 0
- **Solver options**: None needed (default settings)
