/*
 * Test: is_right_child_red / is_left_child_red helpers
 * These functions inspect a node's child color while keeping the
 * node folded as is_rbtree, using their own clean Z3 solver.
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

  ghost fn is_rbtree_nil_case (ct: $type(rb_node *)) (#ft: S.rbtree)
    requires is_rbtree ct ft ** pure (is_null ct)
    ensures is_rbtree ct ft ** pure (ft == S.Leaf)
  {
    match ft {
      S.Leaf -> { () }
      S.Node c l v r -> { unfold (is_rbtree ct (S.Node c l v r)); unreachable () }
    }
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

  let is_child_red_r (ft: S.rbtree) : bool =
    S.Node? ft && (let S.Node _ _ _ r = ft in
      S.Node? r && S.Node?.c r = c2s_color (Int32.int_to_t 0))

  let is_child_red_l (ft: S.rbtree) : bool =
    S.Node? ft && (let S.Node _ l _ _ = ft in
      S.Node? l && S.Node?.c l = c2s_color (Int32.int_to_t 0))

  let is_child_black_l (ft: S.rbtree) : bool =
    S.Node? ft && (let S.Node _ l _ _ = ft in
      S.Node? l && S.Node?.c l = c2s_color (Int32.int_to_t 1))

  let is_child_black_r (ft: S.rbtree) : bool =
    S.Node? ft && (let S.Node _ _ _ r = ft in
      S.Node? r && S.Node?.c r = c2s_color (Int32.int_to_t 1))

  let is_red_with_black_left (ft: S.rbtree) : bool =
    S.Node? ft
    && S.Node?.c ft = c2s_color (Int32.int_to_t 0)
    && is_child_black_l ft

  let is_red_with_black_right (ft: S.rbtree) : bool =
    S.Node? ft
    && S.Node?.c ft = c2s_color (Int32.int_to_t 0)
    && is_child_black_r ft

  ghost fn assert_bc_rr_v2
    (lt rt: S.rbtree)
    requires pure (
      S.Node? rt /\ S.Node?.c rt = c2s_color (Int32.int_to_t 0)
      /\ is_child_red_r rt
      /\ not (is_child_red_l rt)
      /\ ~(S.Node? lt
        /\ S.Node?.c lt = c2s_color (Int32.int_to_t 0)
        /\ is_child_red_l lt)
      /\ ~(S.Node? lt
        /\ S.Node?.c lt = c2s_color (Int32.int_to_t 0)
        /\ is_child_red_r lt))
    ensures pure (S.BC_RR? (S.classify_balance S.Black lt rt))
  { () }

  ghost fn assert_bc_none_rr_v2
    (lt rt: S.rbtree) (v: int)
    requires pure (
      S.Node? rt /\ S.Node?.c rt = c2s_color (Int32.int_to_t 0)
      /\ not (is_child_red_r rt)
      /\ not (is_child_red_l rt)
      /\ ~(S.Node? lt
        /\ S.Node?.c lt = c2s_color (Int32.int_to_t 0)
        /\ is_child_red_l lt)
      /\ ~(S.Node? lt
        /\ S.Node?.c lt = c2s_color (Int32.int_to_t 0)
        /\ is_child_red_r lt))
    ensures pure (S.balance S.Black lt v rt = S.Node S.Black lt v rt)
  { () }

  ghost fn assert_bc_rl_v2
    (lt rt: S.rbtree)
    requires pure (
      S.Node? rt /\ S.Node?.c rt = c2s_color (Int32.int_to_t 0)
      /\ is_child_red_l rt
      /\ ~(S.Node? lt
        /\ S.Node?.c lt = c2s_color (Int32.int_to_t 0)
        /\ is_child_red_l lt)
      /\ ~(S.Node? lt
        /\ S.Node?.c lt = c2s_color (Int32.int_to_t 0)
        /\ is_child_red_r lt))
    ensures pure (S.BC_RL? (S.classify_balance S.Black lt rt))
  { () }

  ghost fn assert_bc_ll_v2
    (lt rt: S.rbtree)
    requires pure (
      S.Node? lt /\ S.Node?.c lt = c2s_color (Int32.int_to_t 0)
      /\ is_child_red_l lt)
    ensures pure (S.BC_LL? (S.classify_balance S.Black lt rt))
  { () }

  ghost fn assert_bc_lr_v2
    (lt rt: S.rbtree)
    requires pure (
      S.Node? lt /\ S.Node?.c lt = c2s_color (Int32.int_to_t 0)
      /\ not (is_child_red_l lt)
      /\ is_child_red_r lt)
    ensures pure (S.BC_LR? (S.classify_balance S.Black lt rt))
  { () }

  ghost fn assert_balance_none_r_not_red_v2
    (lt rt: S.rbtree) (v: int)
    requires pure (
      ~(S.Node? rt /\ S.Node?.c rt = c2s_color (Int32.int_to_t 0))
      /\ ~(S.Node? lt
        /\ S.Node?.c lt = c2s_color (Int32.int_to_t 0)
        /\ is_child_red_l lt)
      /\ ~(S.Node? lt
        /\ S.Node?.c lt = c2s_color (Int32.int_to_t 0)
        /\ is_child_red_r lt))
    ensures pure (S.balance S.Black lt v rt = S.Node S.Black lt v rt)
  { () }

  ghost fn assert_balance_none_l_red_no_match_v2
    (lt rt: S.rbtree) (v: int)
    requires pure (
      S.Node? lt /\ S.Node?.c lt = c2s_color (Int32.int_to_t 0)
      /\ not (is_child_red_l lt)
      /\ not (is_child_red_r lt)
      /\ ~(S.Node? rt /\ S.Node?.c rt = c2s_color (Int32.int_to_t 0)))
    ensures pure (S.balance S.Black lt v rt = S.Node S.Black lt v rt)
  { () }

  ghost fn assert_balance_red
    (lt rt: S.rbtree) (v: int)
    requires emp
    ensures pure (S.balance S.Red lt v rt = S.Node S.Red lt v rt)
  { () }

  ghost fn intro_is_rbtree_leaf (ct: $type(rb_node *))
    requires pure (is_null ct)
    ensures is_rbtree ct S.Leaf
  { fold (is_rbtree ct S.Leaf) }

  ghost fn consume_is_rbtree_nil (ct: $type(rb_node *)) (#ft: S.rbtree)
    requires is_rbtree ct ft ** pure (is_null ct)
    ensures emp
  {
    match ft {
      S.Leaf -> { unfold (is_rbtree ct S.Leaf) }
      S.Node c l v r -> { unfold (is_rbtree ct (S.Node c l v r)); unreachable () }
    }
  }

  ghost fn rewrite_is_rbtree (ct: $type(rb_node *)) (#t1: S.rbtree) (t2: S.rbtree)
    requires is_rbtree ct t1 ** pure (t1 == t2)
    ensures is_rbtree ct t2
  {
    rewrite (is_rbtree ct t1) as (is_rbtree ct t2)
  }

  let valid_rbtree (ct: $type(rb_node *)) (ft: S.rbtree) : slprop =
    is_rbtree ct ft ** pure (S.is_rbtree ft /\ S.is_bst ft)

  ghost fn valid_rbtree_intro (ct: $type(rb_node *)) (#ft: S.rbtree)
    requires is_rbtree ct ft ** pure (S.is_rbtree ft /\ S.is_bst ft)
    ensures valid_rbtree ct ft
  { fold valid_rbtree }

  ghost fn valid_rbtree_elim (ct: $type(rb_node *)) (#ft: S.rbtree)
    requires valid_rbtree ct ft
    ensures is_rbtree ct ft ** pure (S.is_rbtree ft /\ S.is_bst ft)
  { unfold valid_rbtree }

  (* Fuse case lemmas *)
  let fuse_rr_s_red_lemma (a:S.rbtree) (x:int) (b:S.rbtree)
                           (c:S.rbtree) (y:int) (d:S.rbtree)
                           (s:S.rbtree) (b':S.rbtree) (z:int) (c':S.rbtree)
    : Lemma (requires s == S.fuse b c /\ s == S.Node S.Red b' z c')
            (ensures S.fuse (S.Node S.Red a x b) (S.Node S.Red c y d) ==
                     S.Node S.Red (S.Node S.Red a x b') z (S.Node S.Red c' y d))
    = ()

  let fuse_rr_s_not_red_lemma (a:S.rbtree) (x:int) (b:S.rbtree)
                               (c:S.rbtree) (y:int) (d:S.rbtree)
                               (s:S.rbtree)
    : Lemma (requires s == S.fuse b c /\ ~(S.Node? s /\ S.Node?.c s == S.Red))
            (ensures S.fuse (S.Node S.Red a x b) (S.Node S.Red c y d) ==
                     S.Node S.Red a x (S.Node S.Red s y d))
    = ()

  let fuse_bb_s_red_lemma (a:S.rbtree) (x:int) (b:S.rbtree)
                           (c:S.rbtree) (y:int) (d:S.rbtree)
                           (s:S.rbtree) (b':S.rbtree) (z:int) (c':S.rbtree)
    : Lemma (requires s == S.fuse b c /\ s == S.Node S.Red b' z c')
            (ensures S.fuse (S.Node S.Black a x b) (S.Node S.Black c y d) ==
                     S.Node S.Red (S.Node S.Black a x b') z (S.Node S.Black c' y d))
    = ()

  let fuse_bb_s_not_red_lemma (a:S.rbtree) (x:int) (b:S.rbtree)
                               (c:S.rbtree) (y:int) (d:S.rbtree)
                               (s:S.rbtree)
    : Lemma (requires s == S.fuse b c /\ ~(S.Node? s /\ S.Node?.c s == S.Red))
            (ensures S.fuse (S.Node S.Black a x b) (S.Node S.Black c y d) ==
                     S.balL a x (S.Node S.Black s y d))
    = ()

  let fuse_l_red_r_not_red_lemma (a:S.rbtree) (x:int) (b:S.rbtree) (rt:S.rbtree)
    : Lemma (requires ~(S.Node? rt /\ S.Node?.c rt == S.Red))
            (ensures S.fuse (S.Node S.Red a x b) rt == S.Node S.Red a x (S.fuse b rt))
    = ()

  let fuse_r_red_l_not_red_lemma (lt:S.rbtree) (c:S.rbtree) (y:int) (d:S.rbtree)
    : Lemma (requires ~(S.Node? lt /\ S.Node?.c lt == S.Red))
            (ensures S.fuse lt (S.Node S.Red c y d) == S.Node S.Red (S.fuse lt c) y d)
    = ()

  (* Total helper: result tree for fuse_rr when s is Red *)
  let fuse_rr_s_red_result (ll:S.rbtree) (lv:int) (st:S.rbtree) (rv:int) (rr:S.rbtree) : S.rbtree =
    match st with
    | S.Node _ sl sv sr -> S.Node S.Red (S.Node S.Red ll lv sl) sv (S.Node S.Red sr rv rr)
    | _ -> S.Leaf

  (* Total helper: result tree for fuse_bb when s is Red *)
  let fuse_bb_s_red_result (ll:S.rbtree) (lv:int) (st:S.rbtree) (rv:int) (rr:S.rbtree) : S.rbtree =
    match st with
    | S.Node _ sl sv sr -> S.Node S.Red (S.Node S.Black ll lv sl) sv (S.Node S.Black sr rv rr)
    | _ -> S.Leaf
)

/* ── NEW_NODE ─────────────────────────────────────────────────── */

_plain rb_node *new_node(int v, int c, _plain rb_node *left, _plain rb_node *right)
    _requires((_slprop) _inline_pulse(is_rbtree $(left) $`lt ** is_rbtree $(right) $`rt))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.Node (c2s_color $(c)) $`lt (Int32.v $(v)) $`rt)))
{
    rb_node *nd = NULL;
    nd = (rb_node *)malloc(sizeof(rb_node));
    *nd = (rb_node){ .key = v, .color = c, .left = left, .right = right };
    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null $(nd);
        intro_is_rbtree_node $(nd) (!($(nd)));
        with t. rewrite (is_rbtree $(nd) t)
            as (is_rbtree $(nd) (S.Node (c2s_color $(c)) $`lt (Int32.v $(v)) $`rt))
    );
    return nd;
}

/* ── IS_COLOR ─────────────────────────────────────────────────── */
bool is_color(_plain rb_node *tree, int c)
    _requires((_slprop) _inline_pulse(is_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(tree) $`ft **
        pure ($(return) == (S.Node? $`ft && S.Node?.c $`ft = c2s_color $(c)))))
{
    if (tree == NULL) {
        _ghost_stmt(is_rbtree_nil_case $(tree));
        return false;
    }
    _ghost_stmt(
        elim_is_rbtree_nonnull $(tree);
        struct_rb_node__aux_raw_unfold $(tree)
    );
    int tc = tree->color;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(tree));
    bool nd_is_red = (tc == 0);
    bool c_is_red = (c == 0);
    bool result = (nd_is_red == c_is_red);
    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null $(tree);
        intro_is_rbtree_node $(tree) (!($(tree)));
        with t. rewrite (is_rbtree $(tree) t) as (is_rbtree $(tree) $`ft)
    );
    return result;
}

/* ── IS_RIGHT_CHILD_RED ─────────────────────────────────────────
 *  Checks if tree->right is red, keeping tree folded as is_rbtree.
 *  Precondition: tree is a non-leaf node.
 *  Postcondition: tree stays folded, result relates to right subtree.
 * ─────────────────────────────────────────────────────────────── */
bool is_right_child_red(_plain rb_node *tree)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(tree) $`ft **
        pure (S.Node? $`ft)))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(tree) $`ft **
        pure ($(return) == is_child_red_r $`ft)))
{
    rb_node *p_right = NULL;
    bool result = false;

    _ghost_stmt(
        is_rbtree_not_leaf_ptr $(tree);
        elim_is_rbtree_nonnull $(tree);
        struct_rb_node__aux_raw_unfold $(tree)
    );
    p_right = tree->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(tree));

    result = is_color(p_right, 0);

    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null $(tree);
        intro_is_rbtree_node $(tree) (!($(tree)));
        with t. rewrite (is_rbtree $(tree) t) as (is_rbtree $(tree) $`ft)
    );
    return result;
}

/* ── IS_LEFT_CHILD_RED ──────────────────────────────────────────
 *  Checks if tree->left is red, keeping tree folded as is_rbtree.
 *  Precondition: tree is a non-leaf node.
 * ─────────────────────────────────────────────────────────────── */
bool is_left_child_red(_plain rb_node *tree)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(tree) $`ft **
        pure (S.Node? $`ft)))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(tree) $`ft **
        pure ($(return) == is_child_red_l $`ft)))
{
    rb_node *p_left = NULL;
    bool result = false;

    _ghost_stmt(
        is_rbtree_not_leaf_ptr $(tree);
        elim_is_rbtree_nonnull $(tree);
        struct_rb_node__aux_raw_unfold $(tree)
    );
    p_left = tree->left;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(tree));

    result = is_color(p_left, 0);

    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null $(tree);
        intro_is_rbtree_node $(tree) (!($(tree)));
        with t. rewrite (is_rbtree $(tree) t) as (is_rbtree $(tree) $`ft)
    );
    return result;
}

bool is_left_child_black(_plain rb_node *tree)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(tree) $`ft **
        pure (S.Node? $`ft)))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(tree) $`ft **
        pure ($(return) == is_child_black_l $`ft)))
{
    rb_node *p_left = NULL;
    bool result = false;

    _ghost_stmt(
        is_rbtree_not_leaf_ptr $(tree);
        elim_is_rbtree_nonnull $(tree);
        struct_rb_node__aux_raw_unfold $(tree)
    );
    p_left = tree->left;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(tree));

    result = is_color(p_left, 1);

    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null $(tree);
        intro_is_rbtree_node $(tree) (!($(tree)));
        with t. rewrite (is_rbtree $(tree) t) as (is_rbtree $(tree) $`ft)
    );
    return result;
}

bool is_right_child_black(_plain rb_node *tree)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(tree) $`ft **
        pure (S.Node? $`ft)))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(tree) $`ft **
        pure ($(return) == is_child_black_r $`ft)))
{
    rb_node *p_right = NULL;
    bool result = false;

    _ghost_stmt(
        is_rbtree_not_leaf_ptr $(tree);
        elim_is_rbtree_nonnull $(tree);
        struct_rb_node__aux_raw_unfold $(tree)
    );
    p_right = tree->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(tree));

    result = is_color(p_right, 1);

    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null $(tree);
        intro_is_rbtree_node $(tree) (!($(tree)));
        with t. rewrite (is_rbtree $(tree) t) as (is_rbtree $(tree) $`ft)
    );
    return result;
}

bool check_red_with_black_left(_plain rb_node *tree)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(tree) $`ft **
        pure ($(return) == is_red_with_black_left $`ft)))
{
    bool red = false;

    red = is_color(tree, 0);
    if (!red) {
        return false;
    }
    return is_left_child_black(tree);
}

bool check_red_with_black_right(_plain rb_node *tree)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(tree) $`ft **
        pure ($(return) == is_red_with_black_right $`ft)))
{
    bool red = false;

    red = is_color(tree, 0);
    if (!red) {
        return false;
    }
    return is_right_child_black(tree);
}

/* ══════════════════════════════════════════════════════════════════
 *  BALANCE ROTATION HELPERS
 * ══════════════════════════════════════════════════════════════════ */

_plain rb_node *balance_ll(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (S.BC_LL? (S.classify_balance S.Black $`lt $`rt))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balance S.Black $`lt (Int32.v $(v)) $`rt)))
{
    int p_key = 0;
    rb_node *p_left = NULL;
    rb_node *p_right = NULL;
    int gc_key = 0;
    rb_node *gc_left = NULL;
    rb_node *gc_right = NULL;
    rb_node *new_child = NULL;

    _ghost_stmt(L.classify_balance_lemma S.Black $`lt (Int32.v $(v)) $`rt);
    _ghost_stmt(is_rbtree_not_leaf_ptr $(l); elim_is_rbtree_nonnull $(l); struct_rb_node__aux_raw_unfold $(l));
    p_key = l->key; p_left = l->left; p_right = l->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(l));
    _ghost_stmt(is_rbtree_not_leaf_ptr $(p_left); elim_is_rbtree_nonnull $(p_left); struct_rb_node__aux_raw_unfold $(p_left));
    gc_key = p_left->key; gc_left = p_left->left; gc_right = p_left->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(p_left));

    *p_left = (rb_node){ .key = gc_key, .color = 1, .left = gc_left, .right = gc_right };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(p_left); intro_is_rbtree_node $(p_left) (!($(p_left))));
    new_child = new_node(v, 1, p_right, r);
    *l = (rb_node){ .key = p_key, .color = 0, .left = p_left, .right = new_child };
    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null $(l);
        intro_is_rbtree_node $(l) (!($(l)));
        with t. rewrite (is_rbtree $(l) t)
             as (is_rbtree $(l) (S.balance S.Black $`lt (Int32.v $(v)) $`rt))
    );
    return l;
}

_plain rb_node *balance_lr(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (S.BC_LR? (S.classify_balance S.Black $`lt $`rt))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balance S.Black $`lt (Int32.v $(v)) $`rt)))
{
    int p_key = 0;
    rb_node *p_left = NULL;
    rb_node *p_right = NULL;
    int gc_key = 0;
    rb_node *gc_left = NULL;
    rb_node *gc_right = NULL;
    rb_node *new_child = NULL;

    _ghost_stmt(L.classify_balance_lemma S.Black $`lt (Int32.v $(v)) $`rt);
    _ghost_stmt(is_rbtree_not_leaf_ptr $(l); elim_is_rbtree_nonnull $(l); struct_rb_node__aux_raw_unfold $(l));
    p_key = l->key; p_left = l->left; p_right = l->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(l));
    _ghost_stmt(is_rbtree_not_leaf_ptr $(p_right); elim_is_rbtree_nonnull $(p_right); struct_rb_node__aux_raw_unfold $(p_right));
    gc_key = p_right->key; gc_left = p_right->left; gc_right = p_right->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(p_right));

    *l = (rb_node){ .key = p_key, .color = 1, .left = p_left, .right = gc_left };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(l); intro_is_rbtree_node $(l) (!($(l))));
    new_child = new_node(v, 1, gc_right, r);
    *p_right = (rb_node){ .key = gc_key, .color = 0, .left = l, .right = new_child };
    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null $(p_right);
        intro_is_rbtree_node $(p_right) (!($(p_right)));
        with t. rewrite (is_rbtree $(p_right) t)
             as (is_rbtree $(p_right) (S.balance S.Black $`lt (Int32.v $(v)) $`rt))
    );
    return p_right;
}

_plain rb_node *balance_rl(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (S.BC_RL? (S.classify_balance S.Black $`lt $`rt))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balance S.Black $`lt (Int32.v $(v)) $`rt)))
{
    int p_key = 0;
    rb_node *p_left = NULL;
    rb_node *p_right = NULL;
    int gc_key = 0;
    rb_node *gc_left = NULL;
    rb_node *gc_right = NULL;
    rb_node *new_child = NULL;

    _ghost_stmt(L.classify_balance_lemma S.Black $`lt (Int32.v $(v)) $`rt);
    _ghost_stmt(is_rbtree_not_leaf_ptr $(r); elim_is_rbtree_nonnull $(r); struct_rb_node__aux_raw_unfold $(r));
    p_key = r->key; p_left = r->left; p_right = r->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(r));
    _ghost_stmt(is_rbtree_not_leaf_ptr $(p_left); elim_is_rbtree_nonnull $(p_left); struct_rb_node__aux_raw_unfold $(p_left));
    gc_key = p_left->key; gc_left = p_left->left; gc_right = p_left->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(p_left));

    new_child = new_node(v, 1, l, gc_left);
    *r = (rb_node){ .key = p_key, .color = 1, .left = gc_right, .right = p_right };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(r); intro_is_rbtree_node $(r) (!($(r))));
    *p_left = (rb_node){ .key = gc_key, .color = 0, .left = new_child, .right = r };
    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null $(p_left);
        intro_is_rbtree_node $(p_left) (!($(p_left)));
        with t. rewrite (is_rbtree $(p_left) t)
             as (is_rbtree $(p_left) (S.balance S.Black $`lt (Int32.v $(v)) $`rt))
    );
    return p_left;
}

_plain rb_node *balance_rr(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (S.BC_RR? (S.classify_balance S.Black $`lt $`rt))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balance S.Black $`lt (Int32.v $(v)) $`rt)))
{
    int p_key = 0;
    rb_node *p_left = NULL;
    rb_node *p_right = NULL;
    int gc_key = 0;
    rb_node *gc_left = NULL;
    rb_node *gc_right = NULL;
    rb_node *new_child = NULL;

    _ghost_stmt(L.classify_balance_lemma S.Black $`lt (Int32.v $(v)) $`rt);
    _ghost_stmt(is_rbtree_not_leaf_ptr $(r); elim_is_rbtree_nonnull $(r); struct_rb_node__aux_raw_unfold $(r));
    p_key = r->key; p_left = r->left; p_right = r->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(r));
    _ghost_stmt(is_rbtree_not_leaf_ptr $(p_right); elim_is_rbtree_nonnull $(p_right); struct_rb_node__aux_raw_unfold $(p_right));
    gc_key = p_right->key; gc_left = p_right->left; gc_right = p_right->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(p_right));

    new_child = new_node(v, 1, l, p_left);
    *p_right = (rb_node){ .key = gc_key, .color = 1, .left = gc_left, .right = gc_right };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(p_right); intro_is_rbtree_node $(p_right) (!($(p_right))));
    *r = (rb_node){ .key = p_key, .color = 0, .left = new_child, .right = p_right };
    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null $(r);
        intro_is_rbtree_node $(r) (!($(r)));
        with t. rewrite (is_rbtree $(r) t)
             as (is_rbtree $(r) (S.balance S.Black $`lt (Int32.v $(v)) $`rt))
    );
    return r;
}

/* ══════════════════════════════════════════════════════════════════
 *  BALANCE DISPATCHER FUNCTIONS
 * ══════════════════════════════════════════════════════════════════ */

_plain rb_node *check_rr_or_none(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (S.Node? $`rt
              /\ S.Node?.c $`rt = c2s_color (Int32.int_to_t 0)
              /\ not (is_child_red_l $`rt)
              /\ ~(S.Node? $`lt
                /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0)
                /\ is_child_red_l $`lt)
              /\ ~(S.Node? $`lt
                /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0)
                /\ is_child_red_r $`lt))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balance S.Black $`lt (Int32.v $(v)) $`rt)))
{
    bool gc_red = false;
    rb_node *result = NULL;

    gc_red = is_right_child_red(r);
    if (!gc_red) {
        _ghost_stmt(assert_bc_none_rr_v2 $`lt $`rt (Int32.v $(v)));
        result = new_node(v, 1, l, r);
        _ghost_stmt(
            with t. rewrite (is_rbtree $(result) t)
                 as (is_rbtree $(result) (S.balance S.Black $`lt (Int32.v $(v)) $`rt))
        );
        return result;
    }

    _ghost_stmt(assert_bc_rr_v2 $`lt $`rt);
    result = balance_rr(l, v, r);
    return result;
}

_plain rb_node *check_rl_rr_or_none(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (S.Node? $`rt
              /\ S.Node?.c $`rt = c2s_color (Int32.int_to_t 0)
              /\ ~(S.Node? $`lt
                /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0)
                /\ is_child_red_l $`lt)
              /\ ~(S.Node? $`lt
                /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0)
                /\ is_child_red_r $`lt))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balance S.Black $`lt (Int32.v $(v)) $`rt)))
{
    bool gc_red = false;
    rb_node *result = NULL;

    gc_red = is_left_child_red(r);
    if (!gc_red) {
        result = check_rr_or_none(l, v, r);
        return result;
    }

    _ghost_stmt(assert_bc_rl_v2 $`lt $`rt);
    result = balance_rl(l, v, r);
    return result;
}

_plain rb_node *check_r_and_balance(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (~(S.Node? $`lt
                /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0)
                /\ is_child_red_l $`lt)
              /\ ~(S.Node? $`lt
                /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0)
                /\ is_child_red_r $`lt))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balance S.Black $`lt (Int32.v $(v)) $`rt)))
{
    bool gc_red = false;
    rb_node *result = NULL;

    gc_red = is_color(r, 0);
    if (!gc_red) {
        _ghost_stmt(assert_balance_none_r_not_red_v2 $`lt $`rt (Int32.v $(v)));
        result = new_node(v, 1, l, r);
        _ghost_stmt(
            with t. rewrite (is_rbtree $(result) t)
                 as (is_rbtree $(result) (S.balance S.Black $`lt (Int32.v $(v)) $`rt))
        );
        return result;
    }

    result = check_rl_rr_or_none(l, v, r);
    return result;
}

_plain rb_node *check_l_no_ll_lr(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (S.Node? $`lt
              /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0)
              /\ not (is_child_red_l $`lt)
              /\ not (is_child_red_r $`lt))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balance S.Black $`lt (Int32.v $(v)) $`rt)))
{
    bool gc_red = false;
    rb_node *result = NULL;

    gc_red = is_color(r, 0);
    if (!gc_red) {
        _ghost_stmt(assert_balance_none_l_red_no_match_v2 $`lt $`rt (Int32.v $(v)));
        result = new_node(v, 1, l, r);
        _ghost_stmt(
            with t. rewrite (is_rbtree $(result) t)
                 as (is_rbtree $(result) (S.balance S.Black $`lt (Int32.v $(v)) $`rt))
        );
        return result;
    }

    result = check_rl_rr_or_none(l, v, r);
    return result;
}

_plain rb_node *check_l_no_ll(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (S.Node? $`lt
              /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0)
              /\ not (is_child_red_l $`lt))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balance S.Black $`lt (Int32.v $(v)) $`rt)))
{
    bool gc_red = false;
    rb_node *result = NULL;

    gc_red = is_right_child_red(l);
    if (!gc_red) {
        result = check_l_no_ll_lr(l, v, r);
        return result;
    }

    _ghost_stmt(assert_bc_lr_v2 $`lt $`rt);
    result = balance_lr(l, v, r);
    return result;
}

_plain rb_node *check_l_and_balance(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (S.Node? $`lt
              /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balance S.Black $`lt (Int32.v $(v)) $`rt)))
{
    bool gc_red = false;
    rb_node *result = NULL;

    gc_red = is_left_child_red(l);
    if (!gc_red) {
        result = check_l_no_ll(l, v, r);
        return result;
    }

    _ghost_stmt(assert_bc_ll_v2 $`lt $`rt);
    result = balance_ll(l, v, r);
    return result;
}

_plain rb_node *rb_balance_black(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balance S.Black $`lt (Int32.v $(v)) $`rt)))
{
    bool gc_red = false;
    rb_node *result = NULL;

    gc_red = is_color(l, 0);
    if (!gc_red) {
        result = check_r_and_balance(l, v, r);
        return result;
    }

    result = check_l_and_balance(l, v, r);
    return result;
}

_plain rb_node *rb_balance(int c, _plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balance (c2s_color $(c)) $`lt (Int32.v $(v)) $`rt)))
{
    rb_node *result = NULL;

    if (c == 0) {
        _ghost_stmt(assert_balance_red $`lt $`rt (Int32.v $(v)));
        result = new_node(v, c, l, r);
        _ghost_stmt(
            with t. rewrite (is_rbtree $(result) t)
                 as (is_rbtree $(result) (S.balance (c2s_color $(c)) $`lt (Int32.v $(v)) $`rt))
        );
        return result;
    }

    result = rb_balance_black(l, v, r);
    _ghost_stmt(
        with t. rewrite (is_rbtree $(result) t)
             as (is_rbtree $(result) (S.balance (c2s_color $(c)) $`lt (Int32.v $(v)) $`rt))
    );
    return result;
}


/* ══════════════════════════════════════════════════════════════════
 *  RB_SEARCH (recursive)
 * ══════════════════════════════════════════════════════════════════ */

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

/* ══════════════════════════════════════════════════════════════════
 *  FREE_RBTREE (recursive)
 * ══════════════════════════════════════════════════════════════════ */

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

/* ══════════════════════════════════════════════════════════════════
 *  RB_MAKE_BLACK
 * ══════════════════════════════════════════════════════════════════ */

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

/* ══════════════════════════════════════════════════════════════════
 *  RB_REDDEN
 * ══════════════════════════════════════════════════════════════════ */

_plain rb_node *rb_redden(_plain rb_node *tree)
    _requires((_slprop) _inline_pulse(is_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.redden $`ft)))
{
    if (tree == NULL) {
        _ghost_stmt(
            is_rbtree_nil_case $(tree);
            rewrite_is_rbtree $(tree) (S.redden $`ft)
        );
        return tree;
    }
    _ghost_stmt(
        elim_is_rbtree_nonnull $(tree);
        struct_rb_node__aux_raw_unfold $(tree)
    );
    tree->color = 0;
    _ghost_stmt(
        struct_rb_node__aux_raw_fold $(tree);
        Pulse.Lib.Reference.pts_to_not_null $(tree);
        intro_is_rbtree_node $(tree) (!($(tree)));
        rewrite_is_rbtree $(tree) (S.redden $`ft)
    );
    return tree;
}

/* ══════════════════════════════════════════════════════════════════
 *  RB_INS (recursive)
 * ══════════════════════════════════════════════════════════════════ */

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
    rb_node *new_child;
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
        new_child = rb_ins(tl, k);
        result = rb_balance(tc, new_child, d, tr);
        _ghost_stmt(rewrite_is_rbtree $(result) (S.ins $`ft (Int32.v $(k))));
        free(tree);
        return result;
    } else if (k > d) {
        new_child = rb_ins(tr, k);
        result = rb_balance(tc, tl, d, new_child);
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

/* ══════════════════════════════════════════════════════════════════
 *  RB_INSERT
 * ══════════════════════════════════════════════════════════════════ */

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

/* ══════════════════════════════════════════════════════════════════
 *  BALL HELPER FUNCTIONS
 * ══════════════════════════════════════════════════════════════════ */

_plain rb_node *balL_l_red(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (S.Node? $`lt
              /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balL $`lt (Int32.v $(v)) $`rt)))
{
    int l_key = 0;
    rb_node *l_left = NULL;
    rb_node *l_right = NULL;
    rb_node *result = NULL;

    _ghost_stmt(is_rbtree_not_leaf_ptr $(l); elim_is_rbtree_nonnull $(l); struct_rb_node__aux_raw_unfold $(l));
    l_key = l->key; l_left = l->left; l_right = l->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(l));

    *l = (rb_node){ .key = l_key, .color = 1, .left = l_left, .right = l_right };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(l); intro_is_rbtree_node $(l) (!($(l))));
    result = new_node(v, 0, l, r);
    _ghost_stmt(
        with t. rewrite (is_rbtree $(result) t)
             as (is_rbtree $(result) (S.balL $`lt (Int32.v $(v)) $`rt))
    );
    return result;
}

_plain rb_node *balL_r_black(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (~(S.Node? $`lt
              /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0))
              /\ S.Node? $`rt
              /\ S.Node?.c $`rt = c2s_color (Int32.int_to_t 1))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balL $`lt (Int32.v $(v)) $`rt)))
{
    int r_key = 0;
    rb_node *r_left = NULL;
    rb_node *r_right = NULL;
    rb_node *result = NULL;

    _ghost_stmt(is_rbtree_not_leaf_ptr $(r); elim_is_rbtree_nonnull $(r); struct_rb_node__aux_raw_unfold $(r));
    r_key = r->key; r_left = r->left; r_right = r->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(r));

    *r = (rb_node){ .key = r_key, .color = 0, .left = r_left, .right = r_right };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(r); intro_is_rbtree_node $(r) (!($(r))));
    result = rb_balance(1, l, v, r);
    _ghost_stmt(
        with t. rewrite (is_rbtree $(result) t)
             as (is_rbtree $(result) (S.balL $`lt (Int32.v $(v)) $`rt))
    );
    return result;
}

_plain rb_node *balL_r_red_rl_black(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (~(S.Node? $`lt
              /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0))
              /\ is_red_with_black_left $`rt)))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balL $`lt (Int32.v $(v)) $`rt)))
{
    int r_key = 0;
    rb_node *r_left = NULL;
    rb_node *r_right = NULL;
    int rl_key = 0;
    rb_node *rl_left = NULL;
    rb_node *rl_right = NULL;
    rb_node *redden_d = NULL;
    rb_node *right_balanced = NULL;
    rb_node *left_black = NULL;

    _ghost_stmt(is_rbtree_not_leaf_ptr $(r); elim_is_rbtree_nonnull $(r); struct_rb_node__aux_raw_unfold $(r));
    r_key = r->key; r_left = r->left; r_right = r->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(r));

    _ghost_stmt(is_rbtree_not_leaf_ptr $(r_left); elim_is_rbtree_nonnull $(r_left); struct_rb_node__aux_raw_unfold $(r_left));
    rl_key = r_left->key; rl_left = r_left->left; rl_right = r_left->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(r_left));

    redden_d = rb_redden(r_right);
    right_balanced = rb_balance(1, rl_right, r_key, redden_d);
    left_black = new_node(v, 1, l, rl_left);
    free(r);
    *r_left = (rb_node){ .key = rl_key, .color = 0, .left = left_black, .right = right_balanced };
    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null $(r_left);
        intro_is_rbtree_node $(r_left) (!($(r_left)));
        with t. rewrite (is_rbtree $(r_left) t)
             as (is_rbtree $(r_left) (S.balL $`lt (Int32.v $(v)) $`rt))
    );
    return r_left;
}

_plain rb_node *balL_default(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (~(S.Node? $`lt
              /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0))
              /\ ~(is_red_with_black_left $`rt)
              /\ ~(S.Node? $`rt
                   /\ S.Node?.c $`rt = c2s_color (Int32.int_to_t 1)))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balL $`lt (Int32.v $(v)) $`rt)))
{
    rb_node *result = NULL;
    result = new_node(v, 1, l, r);
    _ghost_stmt(
        with t. rewrite (is_rbtree $(result) t)
             as (is_rbtree $(result) (S.balL $`lt (Int32.v $(v)) $`rt))
    );
    return result;
}

_plain rb_node *balL_r_red_or_default(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (~(S.Node? $`lt
              /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0))
              /\ ~(S.Node? $`rt
                   /\ S.Node?.c $`rt = c2s_color (Int32.int_to_t 1)))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balL $`lt (Int32.v $(v)) $`rt)))
{
    bool gc_red = false;
    rb_node *result = NULL;

    gc_red = check_red_with_black_left(r);
    if (!gc_red) {
        result = balL_default(l, v, r);
        return result;
    }
    else {};
    result = balL_r_red_rl_black(l, v, r);
    return result;
}

_plain rb_node *balL_l_not_red(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (~(S.Node? $`lt
              /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 0)))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balL $`lt (Int32.v $(v)) $`rt)))
{
    bool gc_red = false;
    rb_node *result = NULL;

    gc_red = is_color(r, 1);
    if (!gc_red) {
        result = balL_r_red_or_default(l, v, r);
        return result;
    }
    else {};

    result = balL_r_black(l, v, r);
    return result;
}

_plain rb_node *rb_balL(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balL $`lt (Int32.v $(v)) $`rt)))
{
    bool gc_red = false;
    rb_node *result = NULL;

    gc_red = is_color(l, 0);
    if (!gc_red) {
        result = balL_l_not_red(l, v, r);
        return result;
    }
    else {};

    result = balL_l_red(l, v, r);
    return result;
}

/* ══════════════════════════════════════════════════════════════════
 *  BALR HELPER FUNCTIONS (symmetric to balL)
 * ══════════════════════════════════════════════════════════════════ */

_plain rb_node *balR_r_red(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (S.Node? $`rt
              /\ S.Node?.c $`rt = c2s_color (Int32.int_to_t 0))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balR $`lt (Int32.v $(v)) $`rt)))
{
    int r_key = 0;
    rb_node *r_left = NULL;
    rb_node *r_right = NULL;
    rb_node *result = NULL;

    _ghost_stmt(is_rbtree_not_leaf_ptr $(r); elim_is_rbtree_nonnull $(r); struct_rb_node__aux_raw_unfold $(r));
    r_key = r->key; r_left = r->left; r_right = r->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(r));

    *r = (rb_node){ .key = r_key, .color = 1, .left = r_left, .right = r_right };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(r); intro_is_rbtree_node $(r) (!($(r))));
    result = new_node(v, 0, l, r);
    _ghost_stmt(
        with t. rewrite (is_rbtree $(result) t)
             as (is_rbtree $(result) (S.balR $`lt (Int32.v $(v)) $`rt))
    );
    return result;
}

_plain rb_node *balR_l_black(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (~(S.Node? $`rt
              /\ S.Node?.c $`rt = c2s_color (Int32.int_to_t 0))
              /\ S.Node? $`lt
              /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 1))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balR $`lt (Int32.v $(v)) $`rt)))
{
    int l_key = 0;
    rb_node *l_left = NULL;
    rb_node *l_right = NULL;
    rb_node *result = NULL;

    _ghost_stmt(is_rbtree_not_leaf_ptr $(l); elim_is_rbtree_nonnull $(l); struct_rb_node__aux_raw_unfold $(l));
    l_key = l->key; l_left = l->left; l_right = l->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(l));

    *l = (rb_node){ .key = l_key, .color = 0, .left = l_left, .right = l_right };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(l); intro_is_rbtree_node $(l) (!($(l))));
    result = rb_balance(1, l, v, r);
    _ghost_stmt(
        with t. rewrite (is_rbtree $(result) t)
             as (is_rbtree $(result) (S.balR $`lt (Int32.v $(v)) $`rt))
    );
    return result;
}

_plain rb_node *balR_l_red_lr_black(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (~(S.Node? $`rt
              /\ S.Node?.c $`rt = c2s_color (Int32.int_to_t 0))
              /\ is_red_with_black_right $`lt)))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balR $`lt (Int32.v $(v)) $`rt)))
{
    int l_key = 0;
    rb_node *l_left = NULL;
    rb_node *l_right = NULL;
    int lr_key = 0;
    rb_node *lr_left = NULL;
    rb_node *lr_right = NULL;
    rb_node *redden_a = NULL;
    rb_node *left_balanced = NULL;
    rb_node *right_black = NULL;

    _ghost_stmt(is_rbtree_not_leaf_ptr $(l); elim_is_rbtree_nonnull $(l); struct_rb_node__aux_raw_unfold $(l));
    l_key = l->key; l_left = l->left; l_right = l->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(l));

    _ghost_stmt(is_rbtree_not_leaf_ptr $(l_right); elim_is_rbtree_nonnull $(l_right); struct_rb_node__aux_raw_unfold $(l_right));
    lr_key = l_right->key; lr_left = l_right->left; lr_right = l_right->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(l_right));

    redden_a = rb_redden(l_left);
    left_balanced = rb_balance(1, redden_a, l_key, lr_left);
    right_black = new_node(v, 1, lr_right, r);
    free(l);
    *l_right = (rb_node){ .key = lr_key, .color = 0, .left = left_balanced, .right = right_black };
    _ghost_stmt(
        Pulse.Lib.Reference.pts_to_not_null $(l_right);
        intro_is_rbtree_node $(l_right) (!($(l_right)));
        with t. rewrite (is_rbtree $(l_right) t)
             as (is_rbtree $(l_right) (S.balR $`lt (Int32.v $(v)) $`rt))
    );
    return l_right;
}

_plain rb_node *balR_default(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (~(S.Node? $`rt
              /\ S.Node?.c $`rt = c2s_color (Int32.int_to_t 0))
              /\ ~(is_red_with_black_right $`lt)
              /\ ~(S.Node? $`lt
                   /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 1)))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balR $`lt (Int32.v $(v)) $`rt)))
{
    rb_node *result = NULL;
    result = new_node(v, 1, l, r);
    _ghost_stmt(
        with t. rewrite (is_rbtree $(result) t)
             as (is_rbtree $(result) (S.balR $`lt (Int32.v $(v)) $`rt))
    );
    return result;
}

_plain rb_node *balR_l_red_or_default(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (~(S.Node? $`rt
              /\ S.Node?.c $`rt = c2s_color (Int32.int_to_t 0))
              /\ ~(S.Node? $`lt
                   /\ S.Node?.c $`lt = c2s_color (Int32.int_to_t 1)))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balR $`lt (Int32.v $(v)) $`rt)))
{
    bool gc_red = false;
    rb_node *result = NULL;

    gc_red = check_red_with_black_right(l);
    if (!gc_red) {
        result = balR_default(l, v, r);
        return result;
    }
    else {};
    result = balR_l_red_lr_black(l, v, r);
    return result;
}

_plain rb_node *balR_r_not_red(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt **
        pure (~(S.Node? $`rt
              /\ S.Node?.c $`rt = c2s_color (Int32.int_to_t 0)))))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balR $`lt (Int32.v $(v)) $`rt)))
{
    bool gc_red = false;
    rb_node *result = NULL;

    gc_red = is_color(l, 1);
    if (!gc_red) {
        result = balR_l_red_or_default(l, v, r);
        return result;
    }
    else {};

    result = balR_l_black(l, v, r);
    return result;
}

_plain rb_node *rb_balR(_plain rb_node *l, int v, _plain rb_node *r)
    _requires((_slprop) _inline_pulse(is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.balR $`lt (Int32.v $(v)) $`rt)))
{
    bool gc_red = false;
    rb_node *result = NULL;

    gc_red = is_color(r, 0);
    if (!gc_red) {
        result = balR_r_not_red(l, v, r);
        return result;
    }
    else {};

    result = balR_r_red(l, v, r);
    return result;
}

/* ══════════════════════════════════════════════════════════════════
 *  RB_FUSE (recursive) — assembly helpers + recursive function
 *
 *  Assembly helpers are defined first (no rb_fuse calls).
 *  rb_fuse handles opening, recursion, and dispatches to assembly.
 * ══════════════════════════════════════════════════════════════════ */

_plain rb_node *fuse_rr_s_red(
    _plain rb_node *l, int l_key, _plain rb_node *l_left,
    _plain rb_node *r, int r_key, _plain rb_node *r_right,
    _plain rb_node *s)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l_left) $`ll **
        is_rbtree $(r_right) $`rr **
        pts_to $(l) $`lnd ** freeable $(l) **
        pts_to $(r) $`rnd ** freeable $(r) **
        is_rbtree $(s) $`st **
        pure (S.Node? $`st /\ S.Node?.c $`st = S.Red)))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return)
          (fuse_rr_s_red_result $`ll (Int32.v $(l_key)) $`st (Int32.v $(r_key)) $`rr)))
{
    int s_key = 0;
    rb_node *s_left = NULL;
    rb_node *s_right = NULL;

    _ghost_stmt(
        is_rbtree_not_leaf_ptr $(s);
        elim_is_rbtree_nonnull $(s);
        struct_rb_node__aux_raw_unfold $(s)
    );
    s_key = s->key; s_left = s->left; s_right = s->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(s));

    *l = (rb_node){ .key = l_key, .color = 0, .left = l_left, .right = s_left };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(l); intro_is_rbtree_node $(l) (!($(l))));
    *r = (rb_node){ .key = r_key, .color = 0, .left = s_right, .right = r_right };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(r); intro_is_rbtree_node $(r) (!($(r))));
    *s = (rb_node){ .key = s_key, .color = 0, .left = l, .right = r };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(s); intro_is_rbtree_node $(s) (!($(s))));
    return s;
}

_plain rb_node *fuse_rr_s_not_red(
    _plain rb_node *l, int l_key, _plain rb_node *l_left,
    _plain rb_node *r, int r_key, _plain rb_node *r_right,
    _plain rb_node *s)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l_left) $`ll **
        is_rbtree $(r_right) $`rr **
        pts_to $(l) $`lnd ** freeable $(l) **
        pts_to $(r) $`rnd ** freeable $(r) **
        is_rbtree $(s) $`st))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return)
          (S.Node S.Red $`ll (Int32.v $(l_key)) (S.Node S.Red $`st (Int32.v $(r_key)) $`rr))))
{
    *r = (rb_node){ .key = r_key, .color = 0, .left = s, .right = r_right };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(r); intro_is_rbtree_node $(r) (!($(r))));
    *l = (rb_node){ .key = l_key, .color = 0, .left = l_left, .right = r };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(l); intro_is_rbtree_node $(l) (!($(l))));
    return l;
}

_plain rb_node *fuse_bb_s_red(
    _plain rb_node *l, int l_key, _plain rb_node *l_left,
    _plain rb_node *r, int r_key, _plain rb_node *r_right,
    _plain rb_node *s)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l_left) $`ll **
        is_rbtree $(r_right) $`rr **
        pts_to $(l) $`lnd ** freeable $(l) **
        pts_to $(r) $`rnd ** freeable $(r) **
        is_rbtree $(s) $`st **
        pure (S.Node? $`st /\ S.Node?.c $`st = S.Red)))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return)
          (fuse_bb_s_red_result $`ll (Int32.v $(l_key)) $`st (Int32.v $(r_key)) $`rr)))
{
    int s_key = 0;
    rb_node *s_left = NULL;
    rb_node *s_right = NULL;

    _ghost_stmt(
        is_rbtree_not_leaf_ptr $(s);
        elim_is_rbtree_nonnull $(s);
        struct_rb_node__aux_raw_unfold $(s)
    );
    s_key = s->key; s_left = s->left; s_right = s->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(s));

    *l = (rb_node){ .key = l_key, .color = 1, .left = l_left, .right = s_left };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(l); intro_is_rbtree_node $(l) (!($(l))));
    *r = (rb_node){ .key = r_key, .color = 1, .left = s_right, .right = r_right };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(r); intro_is_rbtree_node $(r) (!($(r))));
    *s = (rb_node){ .key = s_key, .color = 0, .left = l, .right = r };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(s); intro_is_rbtree_node $(s) (!($(s))));
    return s;
}

_plain rb_node *fuse_bb_s_not_red(
    _plain rb_node *l, int l_key, _plain rb_node *l_left,
    _plain rb_node *r, int r_key, _plain rb_node *r_right,
    _plain rb_node *s)
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l_left) $`ll **
        is_rbtree $(r_right) $`rr **
        pts_to $(l) $`lnd ** freeable $(l) **
        pts_to $(r) $`rnd ** freeable $(r) **
        is_rbtree $(s) $`st))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return)
          (S.balL $`ll (Int32.v $(l_key)) (S.Node S.Black $`st (Int32.v $(r_key)) $`rr))))
{
    rb_node *result = NULL;
    *r = (rb_node){ .key = r_key, .color = 1, .left = s, .right = r_right };
    _ghost_stmt(Pulse.Lib.Reference.pts_to_not_null $(r); intro_is_rbtree_node $(r) (!($(r))));
    free(l);
    result = rb_balL(l_left, l_key, r);
    return result;
}

_rec _plain rb_node *rb_fuse(_plain rb_node *l, _plain rb_node *r)
    _decreases((_slprop) _inline_pulse(S.node_count $`lt + S.node_count $`rt))
    _requires((_slprop) _inline_pulse(
        is_rbtree $(l) $`lt ** is_rbtree $(r) $`rt))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.fuse $`lt $`rt)))
{
    bool l_red = false;
    bool r_red = false;
    int l_key = 0;
    rb_node *l_left = NULL;
    rb_node *l_right = NULL;
    int r_key = 0;
    rb_node *r_left = NULL;
    rb_node *r_right = NULL;
    rb_node *s = NULL;
    bool s_red = false;
    rb_node *result = NULL;

    if (l == NULL) {
        _ghost_stmt(is_rbtree_nil_case $(l); consume_is_rbtree_nil $(l));
        _ghost_stmt(with t. rewrite (is_rbtree $(r) t) as (is_rbtree $(r) (S.fuse $`lt $`rt)));
        return r;
    }
    if (r == NULL) {
        _ghost_stmt(is_rbtree_nil_case $(r); consume_is_rbtree_nil $(r));
        _ghost_stmt(with t. rewrite (is_rbtree $(l) t) as (is_rbtree $(l) (S.fuse $`lt $`rt)));
        return l;
    }

    l_red = is_color(l, 0);
    r_red = is_color(r, 0);

    if (l_red) {
        _ghost_stmt(is_rbtree_not_leaf_ptr $(l); elim_is_rbtree_nonnull $(l); struct_rb_node__aux_raw_unfold $(l));
        l_key = l->key;
        l_left = l->left;
        l_right = l->right;
        _ghost_stmt(struct_rb_node__aux_raw_fold $(l));

        if (r_red) {
            _ghost_stmt(is_rbtree_not_leaf_ptr $(r); elim_is_rbtree_nonnull $(r); struct_rb_node__aux_raw_unfold $(r));
            r_key = r->key;
            r_left = r->left;
            r_right = r->right;
            _ghost_stmt(struct_rb_node__aux_raw_fold $(r));

            s = rb_fuse(l_right, r_left);
            s_red = is_color(s, 0);
            if (s_red) {
                /* both Red, s Red: call assembly helper */
                result = fuse_rr_s_red(l, l_key, l_left, r, r_key, r_right, s);
                _ghost_stmt(with t. rewrite (is_rbtree $(result) t) as (is_rbtree $(result) (S.fuse $`lt $`rt)));
                return result;
            } else {
                /* both Red, s not Red: call assembly helper */
                result = fuse_rr_s_not_red(l, l_key, l_left, r, r_key, r_right, s);
                _ghost_stmt(with t. rewrite (is_rbtree $(result) t) as (is_rbtree $(result) (S.fuse $`lt $`rt)));
                return result;
            }
        } else {
            /* l Red, r not Red */
            result = rb_fuse(l_right, r);
            *l = (rb_node){ .key = l_key, .color = 0, .left = l_left, .right = result };
            _ghost_stmt(
                Pulse.Lib.Reference.pts_to_not_null $(l);
                intro_is_rbtree_node $(l) (!($(l)));
                with t. rewrite (is_rbtree $(l) t) as (is_rbtree $(l) (S.fuse $`lt $`rt))
            );
            return l;
        }
    } else if (r_red) {
        /* l not Red, r Red */
        _ghost_stmt(elim_is_rbtree_nonnull $(r); struct_rb_node__aux_raw_unfold $(r));
        r_key = r->key;
        r_left = r->left;
        r_right = r->right;
        _ghost_stmt(struct_rb_node__aux_raw_fold $(r));
        result = rb_fuse(l, r_left);
        *r = (rb_node){ .key = r_key, .color = 0, .left = result, .right = r_right };
        _ghost_stmt(
            Pulse.Lib.Reference.pts_to_not_null $(r);
            intro_is_rbtree_node $(r) (!($(r)));
            with t. rewrite (is_rbtree $(r) t) as (is_rbtree $(r) (S.fuse $`lt $`rt))
        );
        return r;
    } else {
        /* both Black */
        _ghost_stmt(elim_is_rbtree_nonnull $(l); struct_rb_node__aux_raw_unfold $(l));
        l_key = l->key;
        l_left = l->left;
        l_right = l->right;
        _ghost_stmt(struct_rb_node__aux_raw_fold $(l));

        _ghost_stmt(elim_is_rbtree_nonnull $(r); struct_rb_node__aux_raw_unfold $(r));
        r_key = r->key;
        r_left = r->left;
        r_right = r->right;
        _ghost_stmt(struct_rb_node__aux_raw_fold $(r));

        s = rb_fuse(l_right, r_left);
        s_red = is_color(s, 0);
        if (s_red) {
            /* both Black, s Red: call assembly helper */
            result = fuse_bb_s_red(l, l_key, l_left, r, r_key, r_right, s);
            _ghost_stmt(with t. rewrite (is_rbtree $(result) t) as (is_rbtree $(result) (S.fuse $`lt $`rt)));
            return result;
        } else {
            /* both Black, s not Red: call assembly helper */
            result = fuse_bb_s_not_red(l, l_key, l_left, r, r_key, r_right, s);
            _ghost_stmt(with t. rewrite (is_rbtree $(result) t) as (is_rbtree $(result) (S.fuse $`lt $`rt)));
            return result;
        }
    }
}

/* ══════════════════════════════════════════════════════════════════
 *  RB_DEL (recursive)
 * ══════════════════════════════════════════════════════════════════ */

_rec _plain rb_node *rb_del(_plain rb_node *tree, int k)
    _decreases((_slprop) _inline_pulse($`ft))
    _requires((_slprop) _inline_pulse(is_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.del $`ft (Int32.v $(k)))))
{
    int d = 0;
    rb_node *tl = NULL;
    rb_node *tr = NULL;
    rb_node *result = NULL;
    bool child_was_black = false;
    rb_node *new_child = NULL;

    if (tree == NULL) {
        _ghost_stmt(is_rbtree_nil_case $(tree); rewrite_is_rbtree $(tree) (S.del $`ft (Int32.v $(k))));
        return tree;
    }
    _ghost_stmt(
        elim_is_rbtree_nonnull $(tree);
        struct_rb_node__aux_raw_unfold $(tree)
    );
    d = tree->key;
    tl = tree->left;
    tr = tree->right;
    _ghost_stmt(struct_rb_node__aux_raw_fold $(tree));

    if (k < d) {
        child_was_black = is_color(tl, 1);
        new_child = rb_del(tl, k);
        free(tree);
        if (child_was_black) {
            result = rb_balL(new_child, d, tr);
            _ghost_stmt(
                with t. rewrite (is_rbtree $(result) t)
                     as (is_rbtree $(result) (S.del $`ft (Int32.v $(k))))
            );
            return result;
        } else {
            result = new_node(d, 0, new_child, tr);
            _ghost_stmt(
                with t. rewrite (is_rbtree $(result) t)
                     as (is_rbtree $(result) (S.del $`ft (Int32.v $(k))))
            );
            return result;
        }
    } else if (k > d) {
        child_was_black = is_color(tr, 1);
        new_child = rb_del(tr, k);
        free(tree);
        if (child_was_black) {
            result = rb_balR(tl, d, new_child);
            _ghost_stmt(
                with t. rewrite (is_rbtree $(result) t)
                     as (is_rbtree $(result) (S.del $`ft (Int32.v $(k))))
            );
            return result;
        } else {
            result = new_node(d, 0, tl, new_child);
            _ghost_stmt(
                with t. rewrite (is_rbtree $(result) t)
                     as (is_rbtree $(result) (S.del $`ft (Int32.v $(k))))
            );
            return result;
        }
    } else {
        free(tree);
        result = rb_fuse(tl, tr);
        _ghost_stmt(
            with t. rewrite (is_rbtree $(result) t)
                 as (is_rbtree $(result) (S.del $`ft (Int32.v $(k))))
        );
        return result;
    }
}

/* ══════════════════════════════════════════════════════════════════
 *  RB_DELETE
 * ══════════════════════════════════════════════════════════════════ */

_plain rb_node *rb_delete(_plain rb_node *tree, int k)
    _requires((_slprop) _inline_pulse(is_rbtree $(tree) $`ft))
    _ensures((_slprop) _inline_pulse(
        is_rbtree $(return) (S.delete $`ft (Int32.v $(k)))))
{
    rb_node *t;
    rb_node *result;
    t = rb_del(tree, k);
    result = rb_make_black(t);
    _ghost_stmt(rewrite_is_rbtree $(result) (S.delete $`ft (Int32.v $(k))));
    return result;
}

/* ══════════════════════════════════════════════════════════════════
 *  RB_NEW
 * ══════════════════════════════════════════════════════════════════ */

_plain rb_node *rb_new(void)
    _requires((_slprop) _inline_pulse(emp))
    _ensures((_slprop) _inline_pulse(valid_rbtree $(return) S.Leaf))
{
    rb_node *result = NULL;
    _ghost_stmt(
        intro_is_rbtree_leaf $(result);
        valid_rbtree_intro $(result)
    );
    return result;
}
