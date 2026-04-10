/*
 * Pointer-based Doubly Linked List — C implementation with c2pulse verification.
 *
 * Operations:
 *   - list_insert: insert at head, O(1)
 *   - list_search: search for key, O(n)
 *   - list_delete: delete first occurrence, O(n)
 *
 * The DLL predicate is_dll tracks both forward and backward links:
 *   is_dll head prev l  where prev is the expected prev-pointer of head.
 * For a full list starting from head: is_dll head null l.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>

typedef struct dnode {
    int data;
    struct dnode *prev;
    struct dnode *next;
} dnode;

_include_pulse(
  module L = FStar.List.Tot

  let rec remove_first (k: Int32.t) (l: list Int32.t) : Tot (list Int32.t) (decreases l) =
    match l with
    | [] -> []
    | hd :: tl -> if hd = k then tl else hd :: remove_first k tl

  let rec is_dll ([@@@mkey] head: $type(dnode *)) (prev: $type(dnode *)) (l: list Int32.t)
    : Tot slprop (decreases l)
  = match l with
    | [] -> pure (is_null head)
    | hd :: tl ->
      exists* (nd: $type(dnode)).
        pure (not (is_null head)) **
        pts_to head nd **
        freeable head **
        pure (nd.struct_dnode__data == hd) **
        pure (nd.struct_dnode__prev == prev) **
        is_dll nd.struct_dnode__next head tl

  ghost fn is_dll_nil_case (head: $type(dnode *)) (prev: $type(dnode *))
    (#l: list Int32.t)
    requires is_dll head prev l ** pure (is_null head)
    ensures is_dll head prev l ** pure (l == ([] #Int32.t))
  {
    match l {
      Nil -> { () }
      Cons hd tl -> { unfold (is_dll head prev (hd :: tl)); unreachable () }
    }
  }

  ghost fn elim_is_dll_nonnull (head: $type(dnode *)) (prev: $type(dnode *))
    (#l: list Int32.t)
    requires is_dll head prev l ** pure (not (is_null head))
    ensures exists* (nd: $type(dnode)) (tl: list Int32.t).
      pts_to head nd ** freeable head **
      pure (l == nd.struct_dnode__data :: tl) **
      pure (nd.struct_dnode__prev == prev) **
      is_dll nd.struct_dnode__next head tl
  {
    match l {
      Nil -> { unfold (is_dll head prev []); unreachable () }
      Cons hd tl -> { unfold (is_dll head prev (hd :: tl)) }
    }
  }

  ghost fn elim_is_dll_cons (head: $type(dnode *)) (prev: $type(dnode *))
    (#l: list Int32.t)
    requires is_dll head prev l ** pure (Cons? l)
    ensures exists* (nd: $type(dnode)) (tl: list Int32.t).
      pts_to head nd ** freeable head **
      pure (not (is_null head)) **
      pure (l == nd.struct_dnode__data :: tl) **
      pure (nd.struct_dnode__prev == prev) **
      is_dll nd.struct_dnode__next head tl
  {
    match l {
      Nil -> { unreachable () }
      Cons hd tl -> { unfold (is_dll head prev (hd :: tl)) }
    }
  }

  ghost fn intro_is_dll_cons
    (head: $type(dnode *))
    (prev: $type(dnode *))
    (nd: $type(dnode))
    (#tl: list Int32.t)
    requires
      pure (not (is_null head)) **
      pts_to head nd **
      freeable head **
      pure (nd.struct_dnode__prev == prev) **
      is_dll nd.struct_dnode__next head tl
    ensures is_dll head prev (nd.struct_dnode__data :: tl)
  {
    fold (is_dll head prev (nd.struct_dnode__data :: tl))
  }

  ghost fn is_dll_null_rewrite
    (head: $type(dnode *))
    (prev1 prev2: $type(dnode *))
    (#l: list Int32.t)
    requires is_dll head prev1 l ** pure (is_null head)
    ensures is_dll head prev2 l
  {
    match l {
      Nil -> { unfold (is_dll head prev1 []); fold (is_dll head prev2 []) }
      Cons hd tl -> { unfold (is_dll head prev1 (hd :: tl)); unreachable () }
    }
  }
)

/* ── LIST-INSERT (at head, O(1)) ─────────────────────────────────── */
_plain dnode *list_insert(_plain dnode *head, int x)
    _requires((_slprop) _inline_pulse(is_dll $(head) (null #ty_dnode) $`l))
    _ensures((_slprop) _inline_pulse(
        is_dll $(return) (null #ty_dnode) ($(x) :: $`l)))
{
    dnode *n = (dnode *) malloc(sizeof(dnode));
    *n = (dnode){ .data = x, .prev = NULL, .next = head };
    if (head == NULL) {
        _ghost_stmt(
            is_dll_nil_case $(head) (null #ty_dnode);
            fold (is_dll (null #ty_dnode) (!var_n) ([] #Int32.t));
            Pulse.Lib.Reference.pts_to_not_null (!var_n);
            intro_is_dll_cons (!var_n) (null #ty_dnode) (!(!var_n))
        );
        return n;
    }
    _ghost_stmt(
        elim_is_dll_nonnull $(head) (null #ty_dnode);
        struct_dnode__aux_raw_unfold $(head)
    );
    head->prev = n;
    _ghost_stmt(
        struct_dnode__aux_raw_fold $(head);
        Pulse.Lib.Reference.pts_to_not_null $(head);
        intro_is_dll_cons $(head) (!var_n) (!($(head)))
    );
    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null (!var_n);
        intro_is_dll_cons (!var_n) (null #ty_dnode) (!(!var_n))
    );
    return n;
}

/* ── LIST-SEARCH (O(n)) ──────────────────────────────────────────── */
_rec bool list_search(_plain dnode *head, int k)
    _decreases((_slprop) _inline_pulse($`l))
    _requires((_slprop) _inline_pulse(is_dll $(head) $`prev $`l))
    _ensures((_slprop) _inline_pulse(
        is_dll $(head) $`prev $`l ** pure ($(return) <==> L.mem $(k) $`l)))
{
    if (head == NULL) {
        _ghost_stmt(is_dll_nil_case $(head) $`prev);
        return false;
    }
    _ghost_stmt(
        elim_is_dll_nonnull $(head) $`prev;
        struct_dnode__aux_raw_unfold $(head)
    );
    int d = head->data;
    dnode *nx = head->next;
    bool r = list_search(nx, k);
    _ghost_stmt(
        struct_dnode__aux_raw_fold $(head);
        Pulse.Lib.Reference.pts_to_not_null $(head);
        intro_is_dll_cons $(head) $`prev (!($(head)))
    );
    return r || d == k;
}

/* ── LIST-DELETE (O(n)) ──────────────────────────────────────────── */
_rec _plain dnode *list_delete(_plain dnode *head, _plain dnode *prev_ptr, int k)
    _decreases((_slprop) _inline_pulse($`l))
    _requires((_slprop) _inline_pulse(is_dll $(head) $(prev_ptr) $`l))
    _ensures((_slprop) _inline_pulse(
        is_dll $(return) $(prev_ptr) (remove_first $(k) $`l)))
{
    if (head == NULL) {
        _ghost_stmt(is_dll_nil_case $(head) $(prev_ptr));
        return head;
    }
    _ghost_stmt(
        elim_is_dll_nonnull $(head) $(prev_ptr);
        struct_dnode__aux_raw_unfold $(head)
    );
    int d = head->data;
    dnode *nx = head->next;
    dnode *new_next = nx;
    if (d != k) {
        new_next = list_delete(nx, head, k);
        head->next = new_next;
        _ghost_stmt(
            struct_dnode__aux_raw_fold $(head);
            Pulse.Lib.Reference.pts_to_not_null $(head);
            intro_is_dll_cons $(head) $(prev_ptr) (!($(head)))
        );
        return head;
    }
    /* d == k: delete this node */
    if (nx == NULL) {
        _ghost_stmt(
            is_dll_null_rewrite (!var_nx) $(head) $(prev_ptr);
            struct_dnode__aux_raw_fold $(head)
        );
        free(head);
        return nx;
    }
    /* d == k && nx != NULL: update nx->prev then delete */
    _ghost_stmt(
        elim_is_dll_nonnull (!var_nx) $(head);
        struct_dnode__aux_raw_unfold (!var_nx)
    );
    nx->prev = prev_ptr;
    _ghost_stmt(
        struct_dnode__aux_raw_fold (!var_nx);
        Pulse.Lib.Reference.pts_to_not_null (!var_nx);
        intro_is_dll_cons (!var_nx) $(prev_ptr) (!(!var_nx))
    );
    _ghost_stmt(struct_dnode__aux_raw_fold $(head));
    free(head);
    return nx;
}
