/*
 * Pointer-based Stack — C implementation with c2pulse verification.
 *
 * A stack is a singly linked list where:
 *   - push  = prepend at head, O(1)
 *   - pop   = remove head, O(1)
 *   - peek  = read head data, O(1)
 *   - empty = null check, O(1)
 *
 * Reuses the same node struct and is_list predicate pattern as
 * SinglyLinkedListPtr.c. The stack pointer is just the head of the list.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>

typedef struct snode {
    int data;
    struct snode *next;
} snode;

_include_pulse(
  module L = FStar.List.Tot

  let safe_hd (l:list Int32.t) : Tot Int32.t =
    match l with | hd :: _ -> hd | _ -> 0l

  let safe_tl (l:list Int32.t) : Tot (list Int32.t) =
    match l with | _ :: tl -> tl | _ -> []

  let rec is_stack ([@@@mkey] top: $type(snode *)) (l: list Int32.t)
    : Tot slprop (decreases l)
  = match l with
    | [] -> pure (is_null top)
    | hd :: tl ->
      exists* (nd: $type(snode)).
        pure (not (is_null top)) **
        pts_to top nd **
        freeable top **
        pure (nd.struct_snode__data == hd) **
        is_stack nd.struct_snode__next tl

  ghost fn is_stack_nil_case (top: $type(snode *)) (#l: list Int32.t)
    requires is_stack top l ** pure (is_null top)
    ensures is_stack top l ** pure (l == ([] #Int32.t))
  {
    match l {
      Nil -> { () }
      Cons hd tl -> { unfold (is_stack top (hd :: tl)); unreachable () }
    }
  }

  ghost fn elim_is_stack_nonnull (top: $type(snode *)) (#l: list Int32.t)
    requires is_stack top l ** pure (not (is_null top))
    ensures exists* (nd: $type(snode)) (tl: list Int32.t).
      pts_to top nd ** freeable top **
      pure (l == nd.struct_snode__data :: tl) **
      is_stack nd.struct_snode__next tl
  {
    match l {
      Nil -> { unfold (is_stack top []); unreachable () }
      Cons hd tl -> { unfold (is_stack top (hd :: tl)) }
    }
  }

  ghost fn elim_is_stack_cons (top: $type(snode *)) (#l: list Int32.t)
    requires is_stack top l ** pure (Cons? l)
    ensures exists* (nd: $type(snode)) (tl: list Int32.t).
      pts_to top nd ** freeable top **
      pure (not (is_null top)) **
      pure (l == nd.struct_snode__data :: tl) **
      is_stack nd.struct_snode__next tl
  {
    match l {
      Nil -> { unreachable () }
      Cons hd tl -> { unfold (is_stack top (hd :: tl)) }
    }
  }

  ghost fn intro_is_stack_cons
    (top: $type(snode *))
    (nd: $type(snode))
    (#tl: list Int32.t)
    requires
      pure (not (is_null top)) **
      pts_to top nd **
      freeable top **
      is_stack nd.struct_snode__next tl
    ensures is_stack top (nd.struct_snode__data :: tl)
  {
    fold (is_stack top (nd.struct_snode__data :: tl))
  }
)

/* ── STACK-EMPTY ─────────────────────────────────────────────────── */
bool stack_empty(_plain snode *top)
    _requires((_slprop) _inline_pulse(is_stack $(top) $`l))
    _ensures((_slprop) _inline_pulse(
        is_stack $(top) $`l ** pure ($(return) <==> ($`l == ([] #Int32.t)))))
{
    if (top == NULL) {
        _ghost_stmt(is_stack_nil_case $(top));
        return true;
    }
    _ghost_stmt(
        elim_is_stack_nonnull $(top);
        Pulse.Lib.Reference.pts_to_not_null $(top);
        intro_is_stack_cons $(top) (!($(top)))
    );
    return false;
}

/* ── PUSH ────────────────────────────────────────────────────────── */
_plain snode *push(_plain snode *top, int x)
    _requires((_slprop) _inline_pulse(is_stack $(top) $`l))
    _ensures((_slprop) _inline_pulse(is_stack $(return) ($(x) :: $`l)))
{
    snode *n = (snode *) malloc(sizeof(snode));
    *n = (snode){ .data = x, .next = top };
    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null (!var_n);
        intro_is_stack_cons (!var_n) (!(!var_n))
    );
    return n;
}

/* ── POP ─────────────────────────────────────────────────────────── */
_plain snode *pop(_plain snode *top, _plain int *out)
    _requires((_slprop) _inline_pulse(
        is_stack $(top) $`l ** pure (Cons? $`l) ** pts_to $(out) $`v))
    _ensures((_slprop) _inline_pulse(
        is_stack $(return) (safe_tl $`l) ** pts_to $(out) (safe_hd $`l)))
{
    _ghost_stmt(
        elim_is_stack_cons $(top);
        struct_snode__aux_raw_unfold $(top)
    );
    *out = top->data;
    snode *nx = top->next;
    _ghost_stmt(
        struct_snode__aux_raw_fold $(top)
    );
    free(top);
    return nx;
}

/* ── PEEK ────────────────────────────────────────────────────────── */
int peek(_plain snode *top)
    _requires((_slprop) _inline_pulse(
        is_stack $(top) $`l ** pure (Cons? $`l)))
    _ensures((_slprop) _inline_pulse(
        is_stack $(top) $`l ** pure ($(return) == safe_hd $`l)))
{
    _ghost_stmt(
        elim_is_stack_cons $(top);
        struct_snode__aux_raw_unfold $(top)
    );
    int d = top->data;
    _ghost_stmt(
        struct_snode__aux_raw_fold $(top);
        Pulse.Lib.Reference.pts_to_not_null $(top);
        intro_is_stack_cons $(top) (!($(top)))
    );
    return d;
}
