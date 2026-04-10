/*
 * Pointer-based Singly Linked List — C implementation with c2pulse verification.
 *
 * Uses a proper recursive struct node { data, next } with heap allocation.
 * The recursive is_list predicate and ghost fold/unfold helpers are defined
 * inline via _include_pulse. list_insert is implemented in C; list_search
 * and list_delete are written as Pulse fn rec in _include_pulse (since they
 * require recursive pattern-matching on the ghost list, which _ghost_stmt
 * cannot express).
 *
 * Operations (matching CLRS §10.2):
 *   - list_insert: prepend element at head, O(1) — C function
 *   - list_search: scan for key, O(n)  — Pulse fn rec in _include_pulse
 *   - list_delete: remove first occurrence of key, O(n) — Pulse fn rec
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

/* ── Pulse helpers and operations ──────────────────────────────────
 *
 * is_list predicate, ghost fold/unfold helpers, and list_search/list_delete
 * are all defined in this _include_pulse block. They use the c2pulse-generated
 * struct_node type and field accessors.
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

  (* LIST-SEARCH: traverse from head looking for key k. O(n). *)
  fn rec list_search (head: $type(node *)) (k: Int32.t)
    preserves is_list head $`l
    returns found: bool
    ensures pure (found <==> L.mem k $`l)
    decreases $`l
  {
    if (is_null head) {
      is_list_nil_case head;
      false
    } else {
      elim_is_list_nonnull head;
      let nd = !head;
      let d = nd.struct_node__data;
      if (d = k) {
        Pulse.Lib.Reference.pts_to_not_null head;
        intro_is_list_cons head nd;
        true
      } else {
        let r = list_search nd.struct_node__next k;
        Pulse.Lib.Reference.pts_to_not_null head;
        intro_is_list_cons head nd;
        r
      }
    }
  }

  (* LIST-DELETE: remove first occurrence of key k. O(n). *)
  fn rec list_delete (head: $type(node *)) (k: Int32.t)
    requires is_list head $`l
    returns new_head: $type(node *)
    ensures is_list new_head (remove_first k $`l)
    decreases $`l
  {
    if (is_null head) {
      is_list_nil_case head;
      head
    } else {
      elim_is_list_nonnull head;
      let nd = !head;
      let d = nd.struct_node__data;
      let nx = nd.struct_node__next;
      rewrite each nd.struct_node__next as nx;
      if (d = k) {
        Pulse.Lib.C.Ref.free_ref head;
        nx
      } else {
        let new_tail = list_delete nx k;
        head := { struct_node__data = d; struct_node__next = new_tail };
        Pulse.Lib.Reference.pts_to_not_null head;
        intro_is_list_cons head { struct_node__data = d; struct_node__next = new_tail };
        head
      }
    }
  }
)

/* ── LIST-INSERT ─────────────────────────────────────────────────── */
/* Allocate a new node with key x and prepend it to the list.
 * Returns the new head. O(1).
 */
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
