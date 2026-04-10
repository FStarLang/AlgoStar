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

  fn free_node (ct: $type(rb_node *)) (#nd: erased $type(rb_node))
    requires pts_to ct nd ** freeable ct
    ensures emp
  {
    Pulse.Lib.Reference.forget_init ct;
    Pulse.Lib.C.Ref.free_ref ct
  }

  fn is_color_ptr (tree: $type(rb_node *)) (c: Int32.t)
      (#ft: erased S.rbtree)
    preserves is_rbtree tree ft
    returns b: bool
    ensures pure (b == (S.Node? ft && S.Node?.c ft = c2s_color c))
  {
    if (is_null tree) {
      is_rbtree_nil_case tree;
      false
    } else {
      let nd = open_is_rbtree tree;
      let nd_is_red = (nd.struct_rb_node__color = (Int32.int_to_t 0));
      let c_is_red = (c = (Int32.int_to_t 0));
      let res = (nd_is_red = c_is_red);
      tree := nd;
      Pulse.Lib.Reference.pts_to_not_null tree;
      intro_is_rbtree_node tree (!tree);
      with t. rewrite (is_rbtree tree t) as (is_rbtree tree ft);
      res
    }
  }

  fn rb_redden_ptr (tree: $type(rb_node *))
      (#ft: erased S.rbtree)
    requires is_rbtree tree ft
    returns y: $type(rb_node *)
    ensures is_rbtree y (S.redden ft)
  {
    if (is_null tree) {
      is_rbtree_nil_case tree;
      rewrite_is_rbtree tree (S.redden ft);
      tree
    } else {
      let nd = open_is_rbtree tree;
      tree := Mkstruct_rb_node nd.struct_rb_node__key (Int32.int_to_t 0) nd.struct_rb_node__left nd.struct_rb_node__right;
      Pulse.Lib.Reference.pts_to_not_null tree;
      intro_is_rbtree_node tree (!tree);
      with t. rewrite (is_rbtree tree t) as (is_rbtree tree (S.redden ft));
      tree
    }
  }

  fn rb_balL_ptr (l: $type(rb_node *)) (v: Int32.t) (r: $type(rb_node *))
      (#lt #rt: erased S.rbtree)
    requires is_rbtree l lt ** is_rbtree r rt
    returns y: $type(rb_node *)
    ensures is_rbtree y (S.balL lt (Int32.v v) rt)
  {
    let l_red = is_color_ptr l (Int32.int_to_t 0);
    if l_red {
      is_rbtree_not_leaf_ptr l;
      let ln = open_is_rbtree l;
      l := Mkstruct_rb_node ln.struct_rb_node__key (Int32.int_to_t 1) ln.struct_rb_node__left ln.struct_rb_node__right;
      Pulse.Lib.Reference.pts_to_not_null l;
      intro_is_rbtree_node l (!l);
      let y = new_node_ptr v (Int32.int_to_t 0) l r;
      with t. rewrite (is_rbtree y t) as (is_rbtree y (S.balL lt (Int32.v v) rt));
      y
    } else {
      let r_black = is_color_ptr r (Int32.int_to_t 1);
      if r_black {
        is_rbtree_not_leaf_ptr r;
        let rn = open_is_rbtree r;
        r := Mkstruct_rb_node rn.struct_rb_node__key (Int32.int_to_t 0) rn.struct_rb_node__left rn.struct_rb_node__right;
        Pulse.Lib.Reference.pts_to_not_null r;
        intro_is_rbtree_node r (!r);
        let y = rb_balance_impl (Int32.int_to_t 1) l v r;
        with t. rewrite (is_rbtree y t) as (is_rbtree y (S.balL lt (Int32.v v) rt));
        y
      } else {
        let r_red = is_color_ptr r (Int32.int_to_t 0);
        if r_red {
          is_rbtree_not_leaf_ptr r;
          let rn = open_is_rbtree r;
          let rl_black = is_color_ptr rn.struct_rb_node__left (Int32.int_to_t 1);
          if rl_black {
            is_rbtree_not_leaf_ptr rn.struct_rb_node__left;
            let rln = open_is_rbtree rn.struct_rb_node__left;
            let rd = rb_redden_ptr rn.struct_rb_node__right;
            let right_balanced = rb_balance_impl (Int32.int_to_t 1) rln.struct_rb_node__right rn.struct_rb_node__key rd;
            let left_black = new_node_ptr v (Int32.int_to_t 1) l rln.struct_rb_node__left;
            free_node r;
            rn.struct_rb_node__left := Mkstruct_rb_node rln.struct_rb_node__key (Int32.int_to_t 0) left_black right_balanced;
            Pulse.Lib.Reference.pts_to_not_null rn.struct_rb_node__left;
            intro_is_rbtree_node rn.struct_rb_node__left (!(rn.struct_rb_node__left));
            with t. rewrite (is_rbtree rn.struct_rb_node__left t) as (is_rbtree rn.struct_rb_node__left (S.balL lt (Int32.v v) rt));
            rn.struct_rb_node__left
          } else {
            r := rn;
            Pulse.Lib.Reference.pts_to_not_null r;
            intro_is_rbtree_node r (!r);
            with t. rewrite (is_rbtree r t) as (is_rbtree r rt);
            let y = new_node_ptr v (Int32.int_to_t 1) l r;
            with t. rewrite (is_rbtree y t) as (is_rbtree y (S.balL lt (Int32.v v) rt));
            y
          }
        } else {
          let y = new_node_ptr v (Int32.int_to_t 1) l r;
          with t. rewrite (is_rbtree y t) as (is_rbtree y (S.balL lt (Int32.v v) rt));
          y
        }
      }
    }
  }

  fn rb_balR_ptr (l: $type(rb_node *)) (v: Int32.t) (r: $type(rb_node *))
      (#lt #rt: erased S.rbtree)
    requires is_rbtree l lt ** is_rbtree r rt
    returns y: $type(rb_node *)
    ensures is_rbtree y (S.balR lt (Int32.v v) rt)
  {
    let r_red = is_color_ptr r (Int32.int_to_t 0);
    if r_red {
      is_rbtree_not_leaf_ptr r;
      let rn = open_is_rbtree r;
      r := Mkstruct_rb_node rn.struct_rb_node__key (Int32.int_to_t 1) rn.struct_rb_node__left rn.struct_rb_node__right;
      Pulse.Lib.Reference.pts_to_not_null r;
      intro_is_rbtree_node r (!r);
      let y = new_node_ptr v (Int32.int_to_t 0) l r;
      with t. rewrite (is_rbtree y t) as (is_rbtree y (S.balR lt (Int32.v v) rt));
      y
    } else {
      let l_black = is_color_ptr l (Int32.int_to_t 1);
      if l_black {
        is_rbtree_not_leaf_ptr l;
        let ln = open_is_rbtree l;
        l := Mkstruct_rb_node ln.struct_rb_node__key (Int32.int_to_t 0) ln.struct_rb_node__left ln.struct_rb_node__right;
        Pulse.Lib.Reference.pts_to_not_null l;
        intro_is_rbtree_node l (!l);
        let y = rb_balance_impl (Int32.int_to_t 1) l v r;
        with t. rewrite (is_rbtree y t) as (is_rbtree y (S.balR lt (Int32.v v) rt));
        y
      } else {
        let l_red = is_color_ptr l (Int32.int_to_t 0);
        if l_red {
          is_rbtree_not_leaf_ptr l;
          let ln = open_is_rbtree l;
          let lr_black = is_color_ptr ln.struct_rb_node__right (Int32.int_to_t 1);
          if lr_black {
            is_rbtree_not_leaf_ptr ln.struct_rb_node__right;
            let lrn = open_is_rbtree ln.struct_rb_node__right;
            let la = rb_redden_ptr ln.struct_rb_node__left;
            let left_balanced = rb_balance_impl (Int32.int_to_t 1) la ln.struct_rb_node__key lrn.struct_rb_node__left;
            let right_black = new_node_ptr v (Int32.int_to_t 1) lrn.struct_rb_node__right r;
            free_node l;
            ln.struct_rb_node__right := Mkstruct_rb_node lrn.struct_rb_node__key (Int32.int_to_t 0) left_balanced right_black;
            Pulse.Lib.Reference.pts_to_not_null ln.struct_rb_node__right;
            intro_is_rbtree_node ln.struct_rb_node__right (!(ln.struct_rb_node__right));
            with t. rewrite (is_rbtree ln.struct_rb_node__right t) as (is_rbtree ln.struct_rb_node__right (S.balR lt (Int32.v v) rt));
            ln.struct_rb_node__right
          } else {
            l := ln;
            Pulse.Lib.Reference.pts_to_not_null l;
            intro_is_rbtree_node l (!l);
            with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
            let y = new_node_ptr v (Int32.int_to_t 1) l r;
            with t. rewrite (is_rbtree y t) as (is_rbtree y (S.balR lt (Int32.v v) rt));
            y
          }
        } else {
          let y = new_node_ptr v (Int32.int_to_t 1) l r;
          with t. rewrite (is_rbtree y t) as (is_rbtree y (S.balR lt (Int32.v v) rt));
          y
        }
      }
    }
  }

  fn rec rb_fuse_ptr (l: $type(rb_node *)) (r: $type(rb_node *))
      (#lt #rt: erased S.rbtree)
    requires is_rbtree l lt ** is_rbtree r rt
    returns y: $type(rb_node *)
    ensures is_rbtree y (S.fuse lt rt)
    decreases (S.node_count lt + S.node_count rt)
  {
    if (is_null l) {
      is_rbtree_nil_case l;
      consume_is_rbtree_nil l;
      with t. rewrite (is_rbtree r t) as (is_rbtree r (S.fuse lt rt));
      r
    } else if (is_null r) {
      is_rbtree_nil_case r;
      consume_is_rbtree_nil r;
      with t. rewrite (is_rbtree l t) as (is_rbtree l (S.fuse lt rt));
      l
    } else {
      let ln = open_is_rbtree l;
      let rn = open_is_rbtree r;
      let l_is_red = (ln.struct_rb_node__color = (Int32.int_to_t 0));
      let r_is_red = (rn.struct_rb_node__color = (Int32.int_to_t 0));
      if (l_is_red && r_is_red) {
        let s = rb_fuse_ptr ln.struct_rb_node__right rn.struct_rb_node__left;
        let s_red = is_color_ptr s (Int32.int_to_t 0);
        if s_red {
          is_rbtree_not_leaf_ptr s;
          let sn = open_is_rbtree s;
          l := Mkstruct_rb_node ln.struct_rb_node__key (Int32.int_to_t 0) ln.struct_rb_node__left sn.struct_rb_node__left;
          Pulse.Lib.Reference.pts_to_not_null l;
          intro_is_rbtree_node l (!l);
          r := Mkstruct_rb_node rn.struct_rb_node__key (Int32.int_to_t 0) sn.struct_rb_node__right rn.struct_rb_node__right;
          Pulse.Lib.Reference.pts_to_not_null r;
          intro_is_rbtree_node r (!r);
          s := Mkstruct_rb_node sn.struct_rb_node__key (Int32.int_to_t 0) l r;
          Pulse.Lib.Reference.pts_to_not_null s;
          intro_is_rbtree_node s (!s);
          with t. rewrite (is_rbtree s t) as (is_rbtree s (S.fuse lt rt));
          s
        } else {
          r := Mkstruct_rb_node rn.struct_rb_node__key (Int32.int_to_t 0) s rn.struct_rb_node__right;
          Pulse.Lib.Reference.pts_to_not_null r;
          intro_is_rbtree_node r (!r);
          l := Mkstruct_rb_node ln.struct_rb_node__key (Int32.int_to_t 0) ln.struct_rb_node__left r;
          Pulse.Lib.Reference.pts_to_not_null l;
          intro_is_rbtree_node l (!l);
          with t. rewrite (is_rbtree l t) as (is_rbtree l (S.fuse lt rt));
          l
        }
      } else if (not l_is_red && not r_is_red) {
        let s = rb_fuse_ptr ln.struct_rb_node__right rn.struct_rb_node__left;
        let s_red = is_color_ptr s (Int32.int_to_t 0);
        if s_red {
          is_rbtree_not_leaf_ptr s;
          let sn = open_is_rbtree s;
          l := Mkstruct_rb_node ln.struct_rb_node__key (Int32.int_to_t 1) ln.struct_rb_node__left sn.struct_rb_node__left;
          Pulse.Lib.Reference.pts_to_not_null l;
          intro_is_rbtree_node l (!l);
          r := Mkstruct_rb_node rn.struct_rb_node__key (Int32.int_to_t 1) sn.struct_rb_node__right rn.struct_rb_node__right;
          Pulse.Lib.Reference.pts_to_not_null r;
          intro_is_rbtree_node r (!r);
          s := Mkstruct_rb_node sn.struct_rb_node__key (Int32.int_to_t 0) l r;
          Pulse.Lib.Reference.pts_to_not_null s;
          intro_is_rbtree_node s (!s);
          with t. rewrite (is_rbtree s t) as (is_rbtree s (S.fuse lt rt));
          s
        } else {
          r := Mkstruct_rb_node rn.struct_rb_node__key (Int32.int_to_t 1) s rn.struct_rb_node__right;
          Pulse.Lib.Reference.pts_to_not_null r;
          intro_is_rbtree_node r (!r);
          free_node l;
          let y = rb_balL_ptr ln.struct_rb_node__left ln.struct_rb_node__key r;
          with t. rewrite (is_rbtree y t) as (is_rbtree y (S.fuse lt rt));
          y
        }
      } else if l_is_red {
        r := rn;
        Pulse.Lib.Reference.pts_to_not_null r;
        intro_is_rbtree_node r (!r);
        with t. rewrite (is_rbtree r t) as (is_rbtree r rt);
        let fused = rb_fuse_ptr ln.struct_rb_node__right r;
        l := Mkstruct_rb_node ln.struct_rb_node__key (Int32.int_to_t 0) ln.struct_rb_node__left fused;
        Pulse.Lib.Reference.pts_to_not_null l;
        intro_is_rbtree_node l (!l);
        with t. rewrite (is_rbtree l t) as (is_rbtree l (S.fuse lt rt));
        l
      } else {
        l := ln;
        Pulse.Lib.Reference.pts_to_not_null l;
        intro_is_rbtree_node l (!l);
        with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
        let fused = rb_fuse_ptr l rn.struct_rb_node__left;
        r := Mkstruct_rb_node rn.struct_rb_node__key (Int32.int_to_t 0) fused rn.struct_rb_node__right;
        Pulse.Lib.Reference.pts_to_not_null r;
        intro_is_rbtree_node r (!r);
        with t. rewrite (is_rbtree r t) as (is_rbtree r (S.fuse lt rt));
        r
      }
    }
  }

  fn rec rb_del_ptr (tree: $type(rb_node *)) (k: Int32.t)
      (#ft: erased S.rbtree)
    requires is_rbtree tree ft
    returns y: $type(rb_node *)
    ensures is_rbtree y (S.del ft (Int32.v k))
    decreases ft
  {
    if (is_null tree) {
      is_rbtree_nil_case tree;
      rewrite_is_rbtree tree (S.del ft (Int32.v k));
      tree
    } else {
      let nd = open_is_rbtree tree;
      if (k `FStar.Int32.lt` nd.struct_rb_node__key) {
        let l_was_black = is_color_ptr nd.struct_rb_node__left (Int32.int_to_t 1);
        let new_left = rb_del_ptr nd.struct_rb_node__left k;
        if l_was_black {
          free_node tree;
          let y = rb_balL_ptr new_left nd.struct_rb_node__key nd.struct_rb_node__right;
          with t. rewrite (is_rbtree y t) as (is_rbtree y (S.del ft (Int32.v k)));
          y
        } else {
          free_node tree;
          let y = new_node_ptr nd.struct_rb_node__key (Int32.int_to_t 0) new_left nd.struct_rb_node__right;
          with t. rewrite (is_rbtree y t) as (is_rbtree y (S.del ft (Int32.v k)));
          y
        }
      } else if (nd.struct_rb_node__key `FStar.Int32.lt` k) {
        let r_was_black = is_color_ptr nd.struct_rb_node__right (Int32.int_to_t 1);
        let new_right = rb_del_ptr nd.struct_rb_node__right k;
        if r_was_black {
          free_node tree;
          let y = rb_balR_ptr nd.struct_rb_node__left nd.struct_rb_node__key new_right;
          with t. rewrite (is_rbtree y t) as (is_rbtree y (S.del ft (Int32.v k)));
          y
        } else {
          free_node tree;
          let y = new_node_ptr nd.struct_rb_node__key (Int32.int_to_t 0) nd.struct_rb_node__left new_right;
          with t. rewrite (is_rbtree y t) as (is_rbtree y (S.del ft (Int32.v k)));
          y
        }
      } else {
        free_node tree;
        let y = rb_fuse_ptr nd.struct_rb_node__left nd.struct_rb_node__right;
        with t. rewrite (is_rbtree y t) as (is_rbtree y (S.del ft (Int32.v k)));
        y
      }
    }
  }

  fn rb_make_black_ptr (tree: $type(rb_node *))
      (#ft: erased S.rbtree)
    requires is_rbtree tree ft
    returns y: $type(rb_node *)
    ensures is_rbtree y (S.make_black ft)
  {
    if (is_null tree) {
      is_rbtree_nil_case tree;
      rewrite_is_rbtree tree (S.make_black ft);
      tree
    } else {
      let nd = open_is_rbtree tree;
      tree := Mkstruct_rb_node nd.struct_rb_node__key (Int32.int_to_t 1) nd.struct_rb_node__left nd.struct_rb_node__right;
      Pulse.Lib.Reference.pts_to_not_null tree;
      intro_is_rbtree_node tree (!tree);
      with t. rewrite (is_rbtree tree t) as (is_rbtree tree (S.make_black ft));
      tree
    }
  }

  fn rb_delete_ptr (tree: $type(rb_node *)) (k: Int32.t)
      (#ft: erased S.rbtree)
    requires is_rbtree tree ft
    returns y: $type(rb_node *)
    ensures is_rbtree y (S.delete ft (Int32.v k))
  {
    let t = rb_del_ptr tree k;
    let y = rb_make_black_ptr t;
    with t2. rewrite (is_rbtree y t2) as (is_rbtree y (S.delete ft (Int32.v k)));
    y
  }

  // ========== Validated API ==========

  let valid_rbtree (ct: $type(rb_node *)) (ft: S.rbtree) : slprop =
    is_rbtree ct ft ** pure (S.is_rbtree ft /\ S.is_bst ft)

  ghost fn elim_valid_rbtree (ct: $type(rb_node *)) (#ft: erased S.rbtree)
    requires valid_rbtree ct ft
    ensures is_rbtree ct ft ** pure (S.is_rbtree ft /\ S.is_bst ft)
  {
    unfold valid_rbtree
  }

  ghost fn intro_valid_rbtree (ct: $type(rb_node *)) (#ft: erased S.rbtree)
    requires is_rbtree ct ft ** pure (S.is_rbtree ft /\ S.is_bst ft)
    ensures valid_rbtree ct ft
  {
    fold (valid_rbtree ct ft)
  }

  fn rb_new_ptr ()
    requires emp
    returns y: $type(rb_node *)
    ensures valid_rbtree y S.Leaf
  {
    let y : $type(rb_node *) = Pulse.Lib.Reference.null #ty_rb_node;
    intro_is_rbtree_leaf y;
    fold (valid_rbtree y S.Leaf);
    y
  }

  ghost fn free_valid_elim (tree: $type(rb_node *)) (#ft: erased S.rbtree)
    requires valid_rbtree tree ft
    ensures is_rbtree tree ft
  {
    unfold valid_rbtree
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

/* ── RB_DELETE ────────────────────────────────────────────────── */
_plain rb_node *rb_delete(_plain rb_node *tree, int k)
    _requires((_slprop) _inline_pulse(is_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.delete $`ft (Int32.v $(k)))))
{
    rb_node *result;
    _ghost_stmt(
        let __rd = rb_delete_ptr $(tree) $(k);
        var_result := __rd
    );
    return result;
}

/* ── VALIDATED API ───────────────────────────────────────────── */
_plain rb_node *rb_new(void)
    _requires((_slprop) _inline_pulse(emp))
    _ensures((_slprop) _inline_pulse(valid_rbtree $(return) S.Leaf))
{
    rb_node *result;
    _ghost_stmt(
        let __r = rb_new_ptr ();
        var_result := __r
    );
    return result;
}

_plain bool rb_search_v(_plain rb_node *tree, int k)
    _requires((_slprop) _inline_pulse(valid_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(
        valid_rbtree $(tree) $`ft **
        pure ($(return) == S.mem (Int32.v $(k)) $`ft)))
{
    bool result;
    _ghost_stmt(unfold valid_rbtree; L.search_correct $`ft (Int32.v $(k)));
    result = rb_search(tree, k);
    _ghost_stmt(fold (valid_rbtree $(tree) $`ft));
    return result;
}

_plain rb_node *rb_insert_v(_plain rb_node *tree, int k)
    _requires((_slprop) _inline_pulse(valid_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(
        valid_rbtree $(return) (S.insert $`ft (Int32.v $(k))) **
        pure (b2t (S.mem (Int32.v $(k)) (S.insert $`ft (Int32.v $(k)))))))
{
    rb_node *result;
    _ghost_stmt(
        unfold valid_rbtree;
        L.insert_preserves_bst $`ft (Int32.v $(k));
        L.insert_is_rbtree $`ft (Int32.v $(k));
        L.insert_mem $`ft (Int32.v $(k)) (Int32.v $(k))
    );
    result = rb_insert(tree, k);
    _ghost_stmt(fold (valid_rbtree $(result) (S.insert $`ft (Int32.v $(k)))));
    return result;
}

_plain rb_node *rb_delete_v(_plain rb_node *tree, int k)
    _requires((_slprop) _inline_pulse(valid_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(
        valid_rbtree $(return) (S.delete $`ft (Int32.v $(k))) **
        pure (not (S.mem (Int32.v $(k)) (S.delete $`ft (Int32.v $(k)))))))
{
    rb_node *result;
    _ghost_stmt(
        unfold valid_rbtree;
        L.delete_preserves_bst $`ft (Int32.v $(k));
        L.delete_is_rbtree $`ft (Int32.v $(k));
        L.delete_mem $`ft (Int32.v $(k)) (Int32.v $(k))
    );
    result = rb_delete(tree, k);
    _ghost_stmt(fold (valid_rbtree $(result) (S.delete $`ft (Int32.v $(k)))));
    return result;
}

void free_valid_rbtree(_plain rb_node *tree)
    _requires((_slprop) _inline_pulse(valid_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(emp))
{
    _ghost_stmt(free_valid_elim $(tree));
    free_rbtree(tree);
}
