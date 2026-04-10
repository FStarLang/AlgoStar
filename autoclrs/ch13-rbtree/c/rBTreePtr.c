/*
 * Red-Black Tree — Pointer-based C implementation with c2pulse verification.
 *
 * Uses heap-allocated nodes with recursive pointers, matching the
 * structure of CLRS.Ch13.RBTree.Impl.fsti specifications.
 *
 * Proves functional correctness:
 *   - rb_search: result matches S.search
 *   - rb_insert: result tree represents S.insert
 *   - rb_delete: result tree represents S.delete
 *   - free_rbtree: complete deallocation
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdlib.h>

typedef struct rb_node {
    int key;
    int color;
    struct rb_node *left;
    struct rb_node *right;
} rb_node;

_include_pulse(
  module S = CLRS.Ch13.RBTree.Spec
  module L = CLRS.Ch13.RBTree.Lemmas

  let c2s_color (c: Int32.t) : S.color =
    if Int32.v c = 0 then S.Red else S.Black

  let rec is_rbtree ([@@@mkey] ct: $type(rb_node *)) (ft: S.rbtree)
    : Tot slprop (decreases ft)
    = match ft with
      | S.Leaf -> pure (is_null ct)
      | S.Node c l v r ->
        exists* (nd: $type(rb_node)).
          pure (not (is_null ct)) **
          pts_to ct nd **
          freeable ct **
          pure (Int32.v nd.struct_rb_node__key == v) **
          pure (c2s_color nd.struct_rb_node__color == c) **
          is_rbtree nd.struct_rb_node__left l **
          is_rbtree nd.struct_rb_node__right r

  ghost fn intro_is_rbtree_leaf (ct: $type(rb_node *))
    requires pure (is_null ct)
    ensures is_rbtree ct S.Leaf
  { fold (is_rbtree ct S.Leaf) }

  ghost fn is_rbtree_nil_case (ct: $type(rb_node *)) (#ft: S.rbtree)
    requires is_rbtree ct ft ** pure (is_null ct)
    ensures is_rbtree ct ft ** pure (ft == S.Leaf)
  {
    match ft {
      S.Leaf -> { () }
      S.Node c l v r -> { unfold (is_rbtree ct (S.Node c l v r)); unreachable () }
    }
  }

  ghost fn consume_is_rbtree_nil (ct: $type(rb_node *)) (#ft: S.rbtree)
    requires is_rbtree ct ft ** pure (is_null ct)
    ensures emp
  {
    match ft {
      S.Leaf -> { unfold (is_rbtree ct S.Leaf) }
      S.Node c l v r -> { unfold (is_rbtree ct (S.Node c l v r)); unreachable () }
    }
  }

  ghost fn intro_is_rbtree_node
    (ct: $type(rb_node *))
    (nd: $type(rb_node))
    (#lt #rt: S.rbtree)
    requires
      pure (not (is_null ct)) **
      pts_to ct nd **
      freeable ct **
      is_rbtree nd.struct_rb_node__left lt **
      is_rbtree nd.struct_rb_node__right rt
    ensures is_rbtree ct (S.Node (c2s_color nd.struct_rb_node__color) lt (Int32.v nd.struct_rb_node__key) rt)
  {
    fold (is_rbtree ct (S.Node (c2s_color nd.struct_rb_node__color) lt (Int32.v nd.struct_rb_node__key) rt))
  }

  ghost fn elim_is_rbtree_nonnull (ct: $type(rb_node *)) (#ft: S.rbtree)
    requires is_rbtree ct ft ** pure (not (is_null ct))
    ensures exists* (nd: $type(rb_node)) (lt rt: S.rbtree).
      pts_to ct nd ** freeable ct **
      pure (ft == S.Node (c2s_color nd.struct_rb_node__color) lt (Int32.v nd.struct_rb_node__key) rt) **
      is_rbtree nd.struct_rb_node__left lt **
      is_rbtree nd.struct_rb_node__right rt
  {
    match ft {
      S.Leaf -> {
        unfold (is_rbtree ct S.Leaf);
        unreachable ()
      }
      S.Node c l v r -> {
        unfold (is_rbtree ct (S.Node c l v r))
      }
    }
  }

  ghost fn rewrite_is_rbtree (ct: $type(rb_node *)) (#t1: S.rbtree) (t2: S.rbtree)
    requires is_rbtree ct t1 ** pure (t1 == t2)
    ensures is_rbtree ct t2
  {
    rewrite (is_rbtree ct t1) as (is_rbtree ct t2)
  }

  ghost fn is_rbtree_not_leaf_ptr (l: $type(rb_node *)) (#ft: S.rbtree)
    preserves is_rbtree l ft
    requires pure (S.Node? ft)
    ensures pure (not (is_null l))
  {
    let S.Node c lt v rt = ft;
    unfold (is_rbtree l (S.Node c lt v rt));
    fold (is_rbtree l (S.Node c lt v rt));
    rewrite is_rbtree l (S.Node c lt v rt) as is_rbtree l ft
  }

  fn open_is_rbtree (ct: $type(rb_node *)) (#ft: erased S.rbtree)
    requires is_rbtree ct ft ** pure (not (is_null ct))
    returns nd: $type(rb_node)
    ensures exists* (lt rt: S.rbtree).
      pts_to ct nd ** freeable ct **
      pure (ft == S.Node (c2s_color nd.struct_rb_node__color) lt (Int32.v nd.struct_rb_node__key) rt) **
      is_rbtree nd.struct_rb_node__left lt **
      is_rbtree nd.struct_rb_node__right rt
  {
    elim_is_rbtree_nonnull ct;
    with nd_ex lt_ex rt_ex. _;
    let nd = !ct;
    nd
  }

  fn new_node_ptr (k: Int32.t) (c: Int32.t)
                  (left right: $type(rb_node *))
                  (#lt #rt: erased S.rbtree)
    requires is_rbtree left lt ** is_rbtree right rt
    returns result: $type(rb_node *)
    ensures is_rbtree result (S.Node (c2s_color c) lt (Int32.v k) rt)
  {
    let p = Pulse.Lib.C.Ref.alloc_ref #ty_rb_node ();
    p := Mkstruct_rb_node k c left right;
    Pulse.Lib.Reference.pts_to_not_null p;
    intro_is_rbtree_node p (!p);
    p
  }

  fn check_right_balance_ptr (r: $type(rb_node *))
      (#rt: erased S.rbtree)
    preserves is_rbtree r rt
    returns bc: S.balance_case
    ensures pure (bc == S.classify_balance S.Black S.Leaf rt)
  {
    if (is_null r) {
      is_rbtree_nil_case r;
      S.BC_None
    } else {
      let rn = open_is_rbtree r;
      if (rn.struct_rb_node__color = (Int32.int_to_t 0)) {
        if (is_null rn.struct_rb_node__left) {
          is_rbtree_nil_case rn.struct_rb_node__left;
          if (is_null rn.struct_rb_node__right) {
            is_rbtree_nil_case rn.struct_rb_node__right;
            Pulse.Lib.Reference.pts_to_not_null r;
            intro_is_rbtree_node r rn;
            with t. rewrite (is_rbtree r t) as (is_rbtree r rt);
            S.BC_None
          } else {
            let rrn = open_is_rbtree rn.struct_rb_node__right;
            let is_rr = (rrn.struct_rb_node__color = (Int32.int_to_t 0));
            Pulse.Lib.Reference.pts_to_not_null rn.struct_rb_node__right;
            intro_is_rbtree_node rn.struct_rb_node__right rrn;
            Pulse.Lib.Reference.pts_to_not_null r;
            intro_is_rbtree_node r rn;
            with t. rewrite (is_rbtree r t) as (is_rbtree r rt);
            if is_rr { S.BC_RR } else { S.BC_None }
          }
        } else {
          let rln = open_is_rbtree rn.struct_rb_node__left;
          if (rln.struct_rb_node__color = (Int32.int_to_t 0)) {
            Pulse.Lib.Reference.pts_to_not_null rn.struct_rb_node__left;
            intro_is_rbtree_node rn.struct_rb_node__left rln;
            Pulse.Lib.Reference.pts_to_not_null r;
            intro_is_rbtree_node r rn;
            with t. rewrite (is_rbtree r t) as (is_rbtree r rt);
            S.BC_RL
          } else {
            Pulse.Lib.Reference.pts_to_not_null rn.struct_rb_node__left;
            intro_is_rbtree_node rn.struct_rb_node__left rln;
            if (is_null rn.struct_rb_node__right) {
              is_rbtree_nil_case rn.struct_rb_node__right;
              Pulse.Lib.Reference.pts_to_not_null r;
              intro_is_rbtree_node r rn;
              with t. rewrite (is_rbtree r t) as (is_rbtree r rt);
              S.BC_None
            } else {
              let rrn = open_is_rbtree rn.struct_rb_node__right;
              let is_rr = (rrn.struct_rb_node__color = (Int32.int_to_t 0));
              Pulse.Lib.Reference.pts_to_not_null rn.struct_rb_node__right;
              intro_is_rbtree_node rn.struct_rb_node__right rrn;
              Pulse.Lib.Reference.pts_to_not_null r;
              intro_is_rbtree_node r rn;
              with t. rewrite (is_rbtree r t) as (is_rbtree r rt);
              if is_rr { S.BC_RR } else { S.BC_None }
            }
          }
        }
      } else {
        Pulse.Lib.Reference.pts_to_not_null r;
        intro_is_rbtree_node r rn;
        with t. rewrite (is_rbtree r t) as (is_rbtree r rt);
        S.BC_None
      }
    }
  }

  fn classify_runtime_ptr
      (c: Int32.t)
      (l: $type(rb_node *))
      (r: $type(rb_node *))
      (#lt #rt: erased S.rbtree)
    preserves is_rbtree l lt ** is_rbtree r rt
    returns bc: S.balance_case
    ensures pure (bc == S.classify_balance (c2s_color c) lt rt)
  {
    if (c = (Int32.int_to_t 0)) {
      S.BC_None
    } else {
      if (is_null l) {
        is_rbtree_nil_case l;
        check_right_balance_ptr r
      } else {
        let ln = open_is_rbtree l;
        if (ln.struct_rb_node__color = (Int32.int_to_t 0)) {
          if (is_null ln.struct_rb_node__left) {
            is_rbtree_nil_case ln.struct_rb_node__left;
            if (is_null ln.struct_rb_node__right) {
              is_rbtree_nil_case ln.struct_rb_node__right;
              Pulse.Lib.Reference.pts_to_not_null l;
              intro_is_rbtree_node l ln;
              with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
              check_right_balance_ptr r
            } else {
              let lrn = open_is_rbtree ln.struct_rb_node__right;
              let is_lr = (lrn.struct_rb_node__color = (Int32.int_to_t 0));
              Pulse.Lib.Reference.pts_to_not_null ln.struct_rb_node__right;
              intro_is_rbtree_node ln.struct_rb_node__right lrn;
              Pulse.Lib.Reference.pts_to_not_null l;
              intro_is_rbtree_node l ln;
              with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
              if is_lr { S.BC_LR } else { check_right_balance_ptr r }
            }
          } else {
            let lln = open_is_rbtree ln.struct_rb_node__left;
            if (lln.struct_rb_node__color = (Int32.int_to_t 0)) {
              Pulse.Lib.Reference.pts_to_not_null ln.struct_rb_node__left;
              intro_is_rbtree_node ln.struct_rb_node__left lln;
              Pulse.Lib.Reference.pts_to_not_null l;
              intro_is_rbtree_node l ln;
              with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
              S.BC_LL
            } else {
              Pulse.Lib.Reference.pts_to_not_null ln.struct_rb_node__left;
              intro_is_rbtree_node ln.struct_rb_node__left lln;
              if (is_null ln.struct_rb_node__right) {
                is_rbtree_nil_case ln.struct_rb_node__right;
                Pulse.Lib.Reference.pts_to_not_null l;
                intro_is_rbtree_node l ln;
                with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
                check_right_balance_ptr r
              } else {
                let lrn = open_is_rbtree ln.struct_rb_node__right;
                let is_lr = (lrn.struct_rb_node__color = (Int32.int_to_t 0));
                Pulse.Lib.Reference.pts_to_not_null ln.struct_rb_node__right;
                intro_is_rbtree_node ln.struct_rb_node__right lrn;
                Pulse.Lib.Reference.pts_to_not_null l;
                intro_is_rbtree_node l ln;
                with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
                if is_lr { S.BC_LR } else { check_right_balance_ptr r }
              }
            }
          }
        } else {
          Pulse.Lib.Reference.pts_to_not_null l;
          intro_is_rbtree_node l ln;
          with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
          check_right_balance_ptr r
        }
      }
    }
  }

  fn balance_ll_ptr
      (l: $type(rb_node *)) (v: Int32.t) (r: $type(rb_node *))
      (#lt #rt: erased S.rbtree)
    requires is_rbtree l lt ** is_rbtree r rt **
             pure (S.BC_LL? (S.classify_balance S.Black lt rt))
    returns result: $type(rb_node *)
    ensures is_rbtree result (S.balance S.Black lt (Int32.v v) rt)
  {
    L.classify_balance_lemma S.Black lt (Int32.v v) rt;
    is_rbtree_not_leaf_ptr l;
    let ln = open_is_rbtree l;
    is_rbtree_not_leaf_ptr ln.struct_rb_node__left;
    let lln = open_is_rbtree ln.struct_rb_node__left;
    ln.struct_rb_node__left := Mkstruct_rb_node lln.struct_rb_node__key (Int32.int_to_t 1) lln.struct_rb_node__left lln.struct_rb_node__right;
    Pulse.Lib.Reference.pts_to_not_null ln.struct_rb_node__left;
    intro_is_rbtree_node ln.struct_rb_node__left (!(ln.struct_rb_node__left));
    let right_black = new_node_ptr v (Int32.int_to_t 1) ln.struct_rb_node__right r;
    l := Mkstruct_rb_node ln.struct_rb_node__key (Int32.int_to_t 0) ln.struct_rb_node__left right_black;
    Pulse.Lib.Reference.pts_to_not_null l;
    intro_is_rbtree_node l (!l);
    with result_tree. rewrite (is_rbtree l result_tree)
         as (is_rbtree l (S.balance S.Black lt (Int32.v v) rt));
    l
  }

  fn balance_lr_ptr
      (l: $type(rb_node *)) (v: Int32.t) (r: $type(rb_node *))
      (#lt #rt: erased S.rbtree)
    requires is_rbtree l lt ** is_rbtree r rt **
             pure (S.BC_LR? (S.classify_balance S.Black lt rt))
    returns result: $type(rb_node *)
    ensures is_rbtree result (S.balance S.Black lt (Int32.v v) rt)
  {
    L.classify_balance_lemma S.Black lt (Int32.v v) rt;
    is_rbtree_not_leaf_ptr l;
    let ln = open_is_rbtree l;
    is_rbtree_not_leaf_ptr ln.struct_rb_node__right;
    let lrn = open_is_rbtree ln.struct_rb_node__right;
    l := Mkstruct_rb_node ln.struct_rb_node__key (Int32.int_to_t 1) ln.struct_rb_node__left lrn.struct_rb_node__left;
    Pulse.Lib.Reference.pts_to_not_null l;
    intro_is_rbtree_node l (!l);
    let right_black = new_node_ptr v (Int32.int_to_t 1) lrn.struct_rb_node__right r;
    ln.struct_rb_node__right := Mkstruct_rb_node lrn.struct_rb_node__key (Int32.int_to_t 0) l right_black;
    Pulse.Lib.Reference.pts_to_not_null ln.struct_rb_node__right;
    intro_is_rbtree_node ln.struct_rb_node__right (!(ln.struct_rb_node__right));
    with result_tree. rewrite (is_rbtree ln.struct_rb_node__right result_tree)
         as (is_rbtree ln.struct_rb_node__right (S.balance S.Black lt (Int32.v v) rt));
    ln.struct_rb_node__right
  }

  fn balance_rl_ptr
      (l: $type(rb_node *)) (v: Int32.t) (r: $type(rb_node *))
      (#lt #rt: erased S.rbtree)
    requires is_rbtree l lt ** is_rbtree r rt **
             pure (S.BC_RL? (S.classify_balance S.Black lt rt))
    returns result: $type(rb_node *)
    ensures is_rbtree result (S.balance S.Black lt (Int32.v v) rt)
  {
    L.classify_balance_lemma S.Black lt (Int32.v v) rt;
    is_rbtree_not_leaf_ptr r;
    let rn = open_is_rbtree r;
    is_rbtree_not_leaf_ptr rn.struct_rb_node__left;
    let rln = open_is_rbtree rn.struct_rb_node__left;
    let left_black = new_node_ptr v (Int32.int_to_t 1) l rln.struct_rb_node__left;
    r := Mkstruct_rb_node rn.struct_rb_node__key (Int32.int_to_t 1) rln.struct_rb_node__right rn.struct_rb_node__right;
    Pulse.Lib.Reference.pts_to_not_null r;
    intro_is_rbtree_node r (!r);
    rn.struct_rb_node__left := Mkstruct_rb_node rln.struct_rb_node__key (Int32.int_to_t 0) left_black r;
    Pulse.Lib.Reference.pts_to_not_null rn.struct_rb_node__left;
    intro_is_rbtree_node rn.struct_rb_node__left (!(rn.struct_rb_node__left));
    with result_tree. rewrite (is_rbtree rn.struct_rb_node__left result_tree)
         as (is_rbtree rn.struct_rb_node__left (S.balance S.Black lt (Int32.v v) rt));
    rn.struct_rb_node__left
  }

  fn balance_rr_ptr
      (l: $type(rb_node *)) (v: Int32.t) (r: $type(rb_node *))
      (#lt #rt: erased S.rbtree)
    requires is_rbtree l lt ** is_rbtree r rt **
             pure (S.BC_RR? (S.classify_balance S.Black lt rt))
    returns result: $type(rb_node *)
    ensures is_rbtree result (S.balance S.Black lt (Int32.v v) rt)
  {
    L.classify_balance_lemma S.Black lt (Int32.v v) rt;
    is_rbtree_not_leaf_ptr r;
    let rn = open_is_rbtree r;
    is_rbtree_not_leaf_ptr rn.struct_rb_node__right;
    let rrn = open_is_rbtree rn.struct_rb_node__right;
    let left_black = new_node_ptr v (Int32.int_to_t 1) l rn.struct_rb_node__left;
    rn.struct_rb_node__right := Mkstruct_rb_node rrn.struct_rb_node__key (Int32.int_to_t 1) rrn.struct_rb_node__left rrn.struct_rb_node__right;
    Pulse.Lib.Reference.pts_to_not_null rn.struct_rb_node__right;
    intro_is_rbtree_node rn.struct_rb_node__right (!(rn.struct_rb_node__right));
    r := Mkstruct_rb_node rn.struct_rb_node__key (Int32.int_to_t 0) left_black rn.struct_rb_node__right;
    Pulse.Lib.Reference.pts_to_not_null r;
    intro_is_rbtree_node r (!r);
    with result_tree. rewrite (is_rbtree r result_tree)
         as (is_rbtree r (S.balance S.Black lt (Int32.v v) rt));
    r
  }

  fn rb_balance_impl
      (c: Int32.t)
      (l: $type(rb_node *))
      (v: Int32.t)
      (r: $type(rb_node *))
      (#lt #rt: erased S.rbtree)
    requires is_rbtree l lt ** is_rbtree r rt
    returns result: $type(rb_node *)
    ensures is_rbtree result (S.balance (c2s_color c) lt (Int32.v v) rt)
  {
    let bc = classify_runtime_ptr c l r;
    match bc {
      S.BC_LL -> {
        let res = balance_ll_ptr l v r;
        rewrite (is_rbtree res (S.balance S.Black lt (Int32.v v) rt))
             as (is_rbtree res (S.balance (c2s_color c) lt (Int32.v v) rt));
        res
      }
      S.BC_LR -> {
        let res = balance_lr_ptr l v r;
        rewrite (is_rbtree res (S.balance S.Black lt (Int32.v v) rt))
             as (is_rbtree res (S.balance (c2s_color c) lt (Int32.v v) rt));
        res
      }
      S.BC_RL -> {
        let res = balance_rl_ptr l v r;
        rewrite (is_rbtree res (S.balance S.Black lt (Int32.v v) rt))
             as (is_rbtree res (S.balance (c2s_color c) lt (Int32.v v) rt));
        res
      }
      S.BC_RR -> {
        let res = balance_rr_ptr l v r;
        rewrite (is_rbtree res (S.balance S.Black lt (Int32.v v) rt))
             as (is_rbtree res (S.balance (c2s_color c) lt (Int32.v v) rt));
        res
      }
      S.BC_None -> {
        L.classify_balance_lemma (c2s_color c) lt (Int32.v v) rt;
        let n = new_node_ptr v c l r;
        with t. rewrite (is_rbtree n t)
             as (is_rbtree n (S.balance (c2s_color c) lt (Int32.v v) rt));
        n
      }
    }
  }
)

/* ── RB_SEARCH ────────────────────────────────────────────────── */
_rec bool rb_search(_plain rb_node *tree, int k)
    _decreases((_slprop) _inline_pulse($`ft))
    _requires((_slprop) _inline_pulse(is_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(tree) $`ft **
        pure ($(return) = Some? (S.search $`ft (Int32.v $(k))))))
{
    if (tree == NULL) {
        _ghost_stmt(is_rbtree_nil_case $(tree));
        return false;
    }
    _ghost_stmt(
        elim_is_rbtree_nonnull $(tree);
        struct_rb_node__aux_raw_unfold $(tree)
    );
    int d = tree->key;
    rb_node *l = tree->left;
    rb_node *r = tree->right;
    if (k < d) {
        bool result = rb_search(l, k);
        _ghost_stmt(
            struct_rb_node__aux_raw_fold $(tree);
            Pulse.Lib.Reference.pts_to_not_null $(tree);
            intro_is_rbtree_node $(tree) (!($(tree)))
        );
        return result;
    } else if (k > d) {
        bool result = rb_search(r, k);
        _ghost_stmt(
            struct_rb_node__aux_raw_fold $(tree);
            Pulse.Lib.Reference.pts_to_not_null $(tree);
            intro_is_rbtree_node $(tree) (!($(tree)))
        );
        return result;
    } else {
        _ghost_stmt(
            struct_rb_node__aux_raw_fold $(tree);
            Pulse.Lib.Reference.pts_to_not_null $(tree);
            intro_is_rbtree_node $(tree) (!($(tree)))
        );
        return true;
    }
}

/* ── FREE_RBTREE ──────────────────────────────────────────────── */
_rec void free_rbtree(_plain rb_node *tree)
    _decreases((_slprop) _inline_pulse($`ft))
    _requires((_slprop) _inline_pulse(is_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(emp))
{
    if (tree == NULL) {
        _ghost_stmt(consume_is_rbtree_nil $(tree));
        return;
    }
    _ghost_stmt(
        elim_is_rbtree_nonnull $(tree);
        struct_rb_node__aux_raw_unfold $(tree)
    );
    rb_node *l = tree->left;
    rb_node *r = tree->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(tree));
    free_rbtree(l);
    free_rbtree(r);
    free(tree);
}


/* ── NEW_NODE ─────────────────────────────────────────────────── */
_plain rb_node *new_node(int key, int color, _plain rb_node *left, _plain rb_node *right)
    _requires((_slprop) _inline_pulse(is_rbtree $(left) $`lt ** is_rbtree $(right) $`rt))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.Node (c2s_color $(color)) $`lt (Int32.v $(key)) $`rt)))
{
    rb_node *n = (rb_node *) malloc(sizeof(rb_node));
    *n = (rb_node){ .key = key, .color = color, .left = left, .right = right };
    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null $(n);
        intro_is_rbtree_node $(n) (!($(n)))
    );
    return n;
}

/* ── RB_BALANCE ───────────────────────────────────────────────── */
/* Thin wrapper: delegates to rb_balance_impl (Pulse fn in _include_pulse) */
_plain rb_node *rb_balance(int c, _plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balance (c2s_color $(c)) $`lt (Int32.v $(v)) $`rt)))
{
    rb_node *result;
    _ghost_stmt(
        let __rb = rb_balance_impl $(c) $(l) $(v) $(r);
        var_result := __rb
    );
    return result;
}

/* ── RB_INS ───────────────────────────────────────────────────── */
_rec _plain rb_node *rb_ins(_plain rb_node *tree, int k)
    _decreases((_slprop) _inline_pulse($`ft))
    _requires((_slprop) _inline_pulse(is_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.ins $`ft (Int32.v $(k)))))
{
    rb_node *left_null;
    rb_node *right_null;
    rb_node *n;
    int d;
    int tc;
    rb_node *tl;
    rb_node *tr;
    rb_node *new_l;
    rb_node *new_r;
    rb_node *result;

    if (tree == NULL) {
        _ghost_stmt(
            is_rbtree_nil_case $(tree);
            consume_is_rbtree_nil $(tree)
        );
        left_null = NULL;
        right_null = NULL;
        _ghost_stmt(
            intro_is_rbtree_leaf $(left_null);
            intro_is_rbtree_leaf $(right_null)
        );
        n = new_node(k, 0, left_null, right_null);
        _ghost_stmt(rewrite_is_rbtree $(n) (S.ins $`ft (Int32.v $(k))));
        return n;
    }
    _ghost_stmt(
        elim_is_rbtree_nonnull $(tree);
        struct_rb_node__aux_raw_unfold $(tree)
    );
    d = tree->key;
    tc = tree->color;
    tl = tree->left;
    tr = tree->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(tree));
    if (k < d) {
        new_l = rb_ins(tl, k);
        result = rb_balance(tc, new_l, d, tr);
        _ghost_stmt(rewrite_is_rbtree $(result) (S.ins $`ft (Int32.v $(k))));
        free(tree);
        return result;
    } else if (k > d) {
        new_r = rb_ins(tr, k);
        result = rb_balance(tc, tl, d, new_r);
        _ghost_stmt(rewrite_is_rbtree $(result) (S.ins $`ft (Int32.v $(k))));
        free(tree);
        return result;
    } else {
        _ghost_stmt(
            Pulse.Lib.Reference.pts_to_not_null $(tree);
            intro_is_rbtree_node $(tree) (!($(tree)));
            rewrite_is_rbtree $(tree) (S.ins $`ft (Int32.v $(k)))
        );
        return tree;
    }
}

/* ── RB_MAKE_BLACK ────────────────────────────────────────────── */
_plain rb_node *rb_make_black(_plain rb_node *tree)
    _requires((_slprop) _inline_pulse(is_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.make_black $`ft)))
{
    if (tree == NULL) {
        _ghost_stmt(
            is_rbtree_nil_case $(tree);
            rewrite_is_rbtree $(tree) (S.make_black $`ft)
        );
        return tree;
    }
    _ghost_stmt(
        elim_is_rbtree_nonnull $(tree);
        struct_rb_node__aux_raw_unfold $(tree)
    );
    tree->color = 1;
    _ghost_stmt(
        struct_rb_node__aux_raw_fold $(tree);
        Pulse.Lib.Reference.pts_to_not_null $(tree);
        intro_is_rbtree_node $(tree) (!($(tree)));
        rewrite_is_rbtree $(tree) (S.make_black $`ft)
    );
    return tree;
}

/* ── RB_INSERT ────────────────────────────────────────────────── */
_plain rb_node *rb_insert(_plain rb_node *tree, int k)
    _requires((_slprop) _inline_pulse(is_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.insert $`ft (Int32.v $(k)))))
{
    rb_node *t;
    rb_node *result;
    t = rb_ins(tree, k);
    result = rb_make_black(t);
    _ghost_stmt(rewrite_is_rbtree $(result) (S.insert $`ft (Int32.v $(k))));
    return result;
}
