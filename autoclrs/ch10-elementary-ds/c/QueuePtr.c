/*
 * Pointer-based Queue — C implementation with c2pulse verification.
 *
 * A queue is a FIFO linked list where:
 *   - enqueue = append at tail, O(n) via recursion
 *   - dequeue = remove head, O(1)
 *   - queue_empty = null check, O(1)
 *
 * Uses the same node/predicate pattern as SinglyLinkedListPtr.c and StackPtr.c.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>

typedef struct qnode {
    int data;
    struct qnode *next;
} qnode;

_include_pulse(
  module L = FStar.List.Tot

  let safe_hd (l:list Int32.t) : Tot Int32.t =
    match l with | hd :: _ -> hd | _ -> 0l

  let safe_tl (l:list Int32.t) : Tot (list Int32.t) =
    match l with | _ :: tl -> tl | _ -> []

  let rec is_queue ([@@@mkey] head: $type(qnode *)) (l: list Int32.t)
    : Tot slprop (decreases l)
  = match l with
    | [] -> pure (is_null head)
    | hd :: tl ->
      exists* (nd: $type(qnode)).
        pure (not (is_null head)) **
        pts_to head nd **
        freeable head **
        pure (nd.struct_qnode__data == hd) **
        is_queue nd.struct_qnode__next tl

  ghost fn is_queue_nil_case (head: $type(qnode *)) (#l: list Int32.t)
    requires is_queue head l ** pure (is_null head)
    ensures is_queue head l ** pure (l == ([] #Int32.t))
  {
    match l {
      Nil -> { () }
      Cons hd tl -> { unfold (is_queue head (hd :: tl)); unreachable () }
    }
  }

  ghost fn elim_is_queue_nonnull (head: $type(qnode *)) (#l: list Int32.t)
    requires is_queue head l ** pure (not (is_null head))
    ensures exists* (nd: $type(qnode)) (tl: list Int32.t).
      pts_to head nd ** freeable head **
      pure (l == nd.struct_qnode__data :: tl) **
      is_queue nd.struct_qnode__next tl
  {
    match l {
      Nil -> { unfold (is_queue head []); unreachable () }
      Cons hd tl -> { unfold (is_queue head (hd :: tl)) }
    }
  }

  ghost fn elim_is_queue_cons (head: $type(qnode *)) (#l: list Int32.t)
    requires is_queue head l ** pure (Cons? l)
    ensures exists* (nd: $type(qnode)) (tl: list Int32.t).
      pts_to head nd ** freeable head **
      pure (not (is_null head)) **
      pure (l == nd.struct_qnode__data :: tl) **
      is_queue nd.struct_qnode__next tl
  {
    match l {
      Nil -> { unreachable () }
      Cons hd tl -> { unfold (is_queue head (hd :: tl)) }
    }
  }

  ghost fn intro_is_queue_cons
    (head: $type(qnode *))
    (nd: $type(qnode))
    (#tl: list Int32.t)
    requires
      pure (not (is_null head)) **
      pts_to head nd **
      freeable head **
      is_queue nd.struct_qnode__next tl
    ensures is_queue head (nd.struct_qnode__data :: tl)
  {
    fold (is_queue head (nd.struct_qnode__data :: tl))
  }
)

/* ── QUEUE-EMPTY ─────────────────────────────────────────────────── */
bool queue_empty(_plain qnode *head)
    _requires((_slprop) _inline_pulse(is_queue $(head) $`l))
    _ensures((_slprop) _inline_pulse(
        is_queue $(head) $`l ** pure ($(return) <==> ($`l == ([] #Int32.t)))))
{
    if (head == NULL) {
        _ghost_stmt(is_queue_nil_case $(head));
        return true;
    }
    _ghost_stmt(
        elim_is_queue_nonnull $(head);
        Pulse.Lib.Reference.pts_to_not_null $(head);
        intro_is_queue_cons $(head) (!($(head)))
    );
    return false;
}

/* ── ENQUEUE helper: create singleton ─────────────────────────────── */
_plain qnode *enqueue_nil(int x)
    _requires((_slprop) _inline_pulse(emp))
    _ensures((_slprop) _inline_pulse(is_queue $(return) [$(x)]))
{
    qnode *n = (qnode *) malloc(sizeof(qnode));
    *n = (qnode){ .data = x, .next = NULL };
    _ghost_stmt(
        fold (is_queue (null #ty_qnode) ([] #Int32.t));
        Pulse.Lib.Reference.pts_to_not_null (!var_n);
        intro_is_queue_cons (!var_n) (!(!var_n))
    );
    return n;
}

/* ── ENQUEUE (append at tail) ────────────────────────────────────── */
_rec _plain qnode *enqueue(_plain qnode *head, int x)
    _decreases((_slprop) _inline_pulse($`l))
    _requires((_slprop) _inline_pulse(is_queue $(head) $`l))
    _ensures((_slprop) _inline_pulse(is_queue $(return) (L.append $`l [$(x)])))
{
    if (head == NULL) {
        _ghost_stmt(is_queue_nil_case $(head));
        return enqueue_nil(x);
    }
    _ghost_stmt(
        elim_is_queue_nonnull $(head);
        struct_qnode__aux_raw_unfold $(head)
    );
    int d = head->data;
    qnode *nx = head->next;
    qnode *new_next = enqueue(nx, x);
    head->next = new_next;
    _ghost_stmt(
        struct_qnode__aux_raw_fold $(head);
        Pulse.Lib.Reference.pts_to_not_null $(head);
        intro_is_queue_cons $(head) (!($(head)))
    );
    return head;
}

/* ── DEQUEUE (pop from head) ─────────────────────────────────────── */
_plain qnode *dequeue(_plain qnode *head, _plain int *out)
    _requires((_slprop) _inline_pulse(
        is_queue $(head) $`l ** pure (Cons? $`l) ** pts_to $(out) $`v))
    _ensures((_slprop) _inline_pulse(
        is_queue $(return) (safe_tl $`l) ** pts_to $(out) (safe_hd $`l)))
{
    _ghost_stmt(
        elim_is_queue_cons $(head);
        struct_qnode__aux_raw_unfold $(head)
    );
    *out = head->data;
    qnode *nx = head->next;
    _ghost_stmt(
        struct_qnode__aux_raw_fold $(head)
    );
    free(head);
    return nx;
}
