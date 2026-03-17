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
| 7 | `pop` | Returns `3` (LIFO) | ✅ |
| 8 | `peek` | Returns `2` | ✅ |
| 9 | `pop` | Returns `2` | ✅ |
| 10 | `pop` | Returns `1` | ✅ |
| 11 | `stack_empty` | `true` | ✅ |

### What is proven

1. **Precondition satisfiability**: All five operations (`create_stack`, `push`,
   `pop`, `peek`, `stack_empty`) are successfully called, proving their
   preconditions are satisfiable.

2. **Pop postcondition precision**: After pushing `[1; 2; 3]`, the `pop`
   postcondition `exists* xs. stack_inv s xs ** pure (L.append xs [x] == contents)`
   is strong enough for Z3 to determine that `x == 3`, `x == 2`, `x == 1` in
   successive pops. The append-based decomposition uniquely identifies the
   popped element.

3. **Peek postcondition precision**: The peek postcondition
   `pure (exists init. L.append init [x] == contents)` uses a `Prims.exists`
   (not a sep-logic existential). An auxiliary lemma (`peek_last_2`) eliminates
   the pure existential to prove `x == 2`. This demonstrates the postcondition
   is precise but requires a small proof effort to extract the concrete value.

4. **stack_empty precision**: Returns `true` iff the contents list is empty.
   Verified at both empty and non-empty states.

5. **LIFO ordering**: The test verifies full LIFO behavior — elements come out
   in reverse order of insertion: push `1, 2, 3` → pop `3, 2, 1`.

### Auxiliary lemmas needed

- `peek_last_3`: Eliminates `Prims.exists` from peek on `[1;2;3]` → `x == 3`
- `peek_last_2`: Eliminates `Prims.exists` from peek on `[1;2]` → `x == 2`

These are needed because `peek`'s postcondition uses `Prims.exists` rather than
`exists*`. Z3 can handle the sep-logic `exists*` from `pop` directly, but the
pure `exists` from `peek` requires explicit classical elimination.

### Spec issues found

**None.** All preconditions are satisfiable and all postconditions are precise
enough to determine concrete outputs. The specification is complete.

**Minor observation**: The `peek` postcondition uses `Prims.exists` instead of
returning the witness directly. This is a minor inconvenience (requires a helper
lemma) but not a spec weakness — the postcondition is still precise.

### Verification

- **Admits**: 0
- **Assumes**: 0
- **Solver options**: None needed (default settings)
