# KaRaMeL Simplify.ml: `List.nth` out-of-bounds in `unused` function

## Bug

In `karamel/lib/Simplify.ml`, the `unused` function (line ~236) performs:

```ocaml
List.nth ts i = TUnit
```

without checking `i < List.length ts`. This raises `Invalid_argument "List.nth"` when `i >= List.length ts`.

## Root Cause

The `remove_unused_parameters` pass in `visit_EApp` (line ~334) processes function
call sites. It calls `flatten_arrow e.typ` to get the parameter types `ts` from the
callee's type annotation, then constructs `unused = unused parameter_table lid ts`.

Before checking whether `List.length es <= List.length ts` (line ~353), it calls
`self#update_table_current parameter_table unused i es` (line ~344). This method
iterates over all arguments `es` calling `unused arg_i` for each. When a call site
has more actual arguments than the callee's arrow type indicates, `arg_i` exceeds
`List.length ts`, and the unguarded `List.nth ts i` crashes.

The over-application (more args than arrows) happens when F* extracts curried calls
where the callee's type is not fully visible — e.g., polymorphic `assume val`, or
functions not in scope due to `noextract`. The comment at line ~346-349 acknowledges
this case but the crash occurs before the guard at line ~353.

## Fix

```diff
-    List.nth ts i = TUnit
+    i < List.length ts && List.nth ts i = TUnit
```

## Call Path

```
visit_EApp
  → let ts = flatten_arrow e.typ   (* parameter types from callee's type *)
  → let unused = unused parameter_table lid ts
  → self#update_table_current parameter_table unused i es
      → List.iteri (fun arg_i e -> ... unused arg_i ...) es
          → unused arg_i              (* arg_i can be >= List.length ts *)
              → unused_i arg_i
                  → List.nth ts i     (* CRASH when i >= List.length ts *)
```

## Triggering Pattern

The crash requires:
1. A function call in the krml AST where `List.length es > List.length ts`
   (more actual arguments than the callee's flattened arrow type has parameters)
2. The callee must be `private` (in the `parameter_table`) OR the code must
   reach the `List.nth ts i = TUnit` branch

This arises from F* extraction of curried/higher-order patterns, particularly:
- Polymorphic `assume val` declarations (not extracted, type info incomplete)
- `inline_for_extraction noextract` functions returning functions
- Pulse-generated code with callback patterns

## Minimal F* Pattern

```fstar
(* The polymorphic assume prevents F* from fully uncurrying the type *)
assume val poly_apply (#a: Type) (f: a -> a) : a -> a

(* After extraction, the EApp for poly_apply has 3 args (type, f, x)
   but flatten_arrow on the monomorphized type may show fewer arrows *)
private let helper (b: bool) : bool = poly_apply (fun x -> x) b
```

When extracted to `.krml` and processed by KaRaMeL with `-warn-error -2` (to
suppress the missing-implementation warning), this reaches the
`remove_unused_parameters` pass where the crash occurs.

## Workaround

Apply the one-line patch above to `karamel/lib/Simplify.ml` after
`git submodule update --init karamel`.
