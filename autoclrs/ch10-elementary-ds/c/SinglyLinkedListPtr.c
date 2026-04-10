/*
 * Pointer-based Singly Linked List — C implementation with c2pulse verification.
 *
 * Uses a proper recursive struct node { data, next } with heap allocation.
 * The recursive is_list predicate and ghost fold/unfold helpers are defined
 * inline via _include_pulse. All operations (insert, search, delete) are
 * implemented in C with _plain parameters and _ghost_stmt proof steps.
 *
 * Operations (matching CLRS §10.2):
 *   - list_insert: prepend element at head, O(1)
 *   - list_search: scan for key, O(n)
 *   - list_delete: remove first occurrence of key, O(n)
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>

typedef struct node {
    int data;
    struct node *next;
} node;

/* ── Pulse predicates and ghost helpers ──────────────────────────────
 *
 * The _include_pulse block defines the is_list ownership predicate and
 * ghost fold/unfold helpers. These are used in _ghost_stmt blocks within
 * the C functions below.
 */
_include_pulse(
  module L = FStar.List.Tot

  (* Recursive ownership predicate: the ref chain from head represents list l. *)
  let rec is_list ([@@@mkey] head: $type(node *)) (l: list Int32.t)
    : Tot slprop (decreases l)
  = match l with
    | [] -> pure (is_null head)
    | hd :: tl ->
      exists* (nd: $type(node)).
        pure (not (is_null head)) **
        pts_to head nd **
        freeable head **
        pure (nd.struct_node__data == hd) **
        is_list nd.struct_node__next tl

  ghost fn elim_is_list_nil (head: $type(node *))
    requires is_list head ([] #Int32.t)
    ensures pure (is_null head)
  {
    unfold (is_list head ([] #Int32.t))
  }

  ghost fn intro_is_list_nil (head: $type(node *))
    requires pure (is_null head)
    ensures is_list head ([] #Int32.t)
  {
    fold (is_list head ([] #Int32.t))
  }

  (* Case-split for null head: establishes l == [] while preserving is_list. *)
  ghost fn is_list_nil_case (head: $type(node *)) (#l: list Int32.t)
    requires is_list head l ** pure (is_null head)
    ensures is_list head l ** pure (l == ([] #Int32.t))
  {
    match l {
      Nil -> { () }
      Cons hd tl -> { unfold (is_list head (hd :: tl)); unreachable () }
    }
  }

  ghost fn intro_is_list_cons
    (head: $type(node *))
    (nd: $type(node))
    (#tl: list Int32.t)
    requires
      pure (not (is_null head)) **
      pts_to head nd **
      freeable head **
      is_list nd.struct_node__next tl
    ensures is_list head (nd.struct_node__data :: tl)
  {
    fold (is_list head (nd.struct_node__data :: tl))
  }

  ghost fn elim_is_list_nonnull (head: $type(node *)) (#l: list Int32.t)
    requires is_list head l ** pure (not (is_null head))
    ensures exists* (nd: $type(node)) (tl: list Int32.t).
      pts_to head nd ** freeable head **
      pure (l == nd.struct_node__data :: tl) **
      is_list nd.struct_node__next tl
  {
    match l {
      Nil -> {
        unfold (is_list head []);
        unreachable ()
      }
      Cons hd tl -> {
        unfold (is_list head (hd :: tl))
      }
    }
  }

  let rec remove_first (k: Int32.t) (l: list Int32.t)
    : Tot (list Int32.t) (decreases l)
  = match l with
    | [] -> []
    | hd :: tl -> if hd = k then tl else hd :: remove_first k tl
)

/* ── LIST-INSERT ─────────────────────────────────────────────────── */
_plain node *list_insert(_plain node *head, int x)
    _requires((_slprop) _inline_pulse(is_list $(head) $`l))
    _ensures((_slprop) _inline_pulse(is_list $(return) ($(x) :: $`l)))
{
    node *n = (node *) malloc(sizeof(node));
    *n = (node){ .data = x, .next = head };
    _ghost_stmt(
      Pulse.Lib.Reference.pts_to_not_null (!var_n);
      intro_is_list_cons (!var_n) (!(!var_n))
    );
    return n;
}

/* ── LIST-SEARCH ─────────────────────────────────────────────────── */
_rec bool list_search(_plain node *head, int k)
    _decreases((_slprop) _inline_pulse($`l))
    _requires((_slprop) _inline_pulse(is_list $(head) $`l))
    _ensures((_slprop) _inline_pulse(
        is_list $(head) $`l ** pure ($(return) <==> L.mem $(k) $`l)))
{
    if (head == NULL) {
        _ghost_stmt(is_list_nil_case $(head));
        return false;
    }
    _ghost_stmt(
        elim_is_list_nonnull $(head);
        struct_node__aux_raw_unfold $(head)
    );
    int d = head->data;
    node *nx = head->next;
    if (d == k) {
        _ghost_stmt(
            struct_node__aux_raw_fold $(head);
            Pulse.Lib.Reference.pts_to_not_null $(head);
            intro_is_list_cons $(head) (!($(head)))
        );
        return true;
    }
    bool r = list_search(nx, k);
    _ghost_stmt(
        struct_node__aux_raw_fold $(head);
        Pulse.Lib.Reference.pts_to_not_null $(head);
        intro_is_list_cons $(head) (!($(head)))
    );
    return r;
}

/* ── LIST-DELETE ─────────────────────────────────────────────────── */
_rec _plain node *list_delete(_plain node *head, int k)
    _decreases((_slprop) _inline_pulse($`l))
    _requires((_slprop) _inline_pulse(is_list $(head) $`l))
    _ensures((_slprop) _inline_pulse(is_list $(return) (remove_first $(k) $`l)))
{
    if (head == NULL) {
        _ghost_stmt(is_list_nil_case $(head));
        return head;
    }
    _ghost_stmt(
        elim_is_list_nonnull $(head);
        struct_node__aux_raw_unfold $(head)
    );
    int d = head->data;
    node *nx = head->next;
    if (d == k) {
        _ghost_stmt(
            struct_node__aux_raw_fold $(head)
        );
        free(head);
        return nx;
    }
    node *new_tail = list_delete(nx, k);
    head->next = new_tail;
    _ghost_stmt(
        struct_node__aux_raw_fold $(head);
        Pulse.Lib.Reference.pts_to_not_null $(head);
        intro_is_list_cons $(head) (!($(head)))
    );
    return head;
}
