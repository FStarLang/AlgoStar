(*
   Red-Black Tree — CLRS-faithful imperative implementation in Pulse

   CLRS Chapter 13: Red-Black Trees with parent pointers.
   Uses Pulse.Lib.Box heap-allocated nodes with nullable option pointers.

   Implements:
   - TREE-SEARCH (§12.2): recursive BST search, O(h)
   - TREE-MINIMUM / TREE-MAXIMUM (§12.2): walk left/right to min/max
   - RB-INSERT with Okasaki-style balance fixup (§13.3)
   - RB-DELETE with Kahrs-style balL/balR/fuse fixup (§13.4)
   - TREE-FREE: recursive deallocation of all nodes

   Each operation's postcondition links to the pure spec in
   CLRS.Ch13.RBTree.Spec — full functional correctness, no admits.

   Node type: { key, color, left, right, p } with parent pointer.
   Pointer type: option (box rb_node) for nullable pointers.
   Separation logic predicate: rbtree_subtree ct ft parent.

   The parent pointer design follows CLRS.Ch12.BST (ch12-bst):
   each node stores its parent as a value in the `p` field,
   but ownership flows downward through left/right only.
*)

module CLRS.Ch13.Imp.RBTree
#lang-pulse
open Pulse.Lib.Pervasives

module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }

module S = CLRS.Ch13.RBTree.Spec
module G = FStar.Ghost

// ============================================================
// §12.1 Node type
// ============================================================

noeq
type rb_node = {
  key:   int;
  color: S.color;
  left:  rb_ptr;
  right: rb_ptr;
  p:     rb_ptr;     // parent pointer (CLRS §12.1)
}

and rb_node_ptr = box rb_node

and rb_ptr = option rb_node_ptr

// ============================================================
// Separation logic predicate: rbtree_subtree
// ============================================================

let rec rbtree_subtree (ct: rb_ptr) (ft: S.rbtree) (parent: rb_ptr)
  : Tot slprop (decreases ft)
  = match ft with
    | S.Leaf -> pure (ct == None)
    | S.Node c l v r ->
      exists* (bp: rb_node_ptr) (node: rb_node).
        pure (ct == Some bp) **
        (bp |-> node) **
        pure (node.key == v /\ node.color == c /\ node.p == parent) **
        rbtree_subtree node.left l (Some bp) **
        rbtree_subtree node.right r (Some bp)

// ============================================================
// Ghost fold/unfold helpers
// ============================================================

ghost fn elim_rbtree_leaf (x: rb_ptr) (#parent: rb_ptr)
  requires rbtree_subtree x S.Leaf parent
  ensures pure (x == None)
{
  unfold (rbtree_subtree x S.Leaf parent)
}

ghost fn intro_rbtree_leaf (x: rb_ptr) (parent: rb_ptr)
  requires pure (x == None)
  ensures rbtree_subtree x S.Leaf parent
{
  fold (rbtree_subtree x S.Leaf parent)
}

ghost fn intro_rbtree_node (ct: rb_ptr) (bp: rb_node_ptr)
  (#node: rb_node) (#lt #rt: S.rbtree)
  requires
    (bp |-> node) **
    rbtree_subtree node.left lt (Some bp) **
    rbtree_subtree node.right rt (Some bp) **
    pure (ct == Some bp)
  ensures
    rbtree_subtree ct (S.Node node.color lt node.key rt) node.p
{
  fold (rbtree_subtree ct (S.Node node.color lt node.key rt) node.p)
}

// Case analysis predicate
[@@no_mkeys]
let rbtree_cases (x: rb_ptr) (ft: S.rbtree) (parent: rb_ptr)
  = match x with
    | None -> pure (ft == S.Leaf)
    | Some bp ->
      exists* (node: rb_node) (lt rt: S.rbtree).
        (bp |-> node) **
        pure (ft == S.Node node.color lt node.key rt /\ node.p == parent) **
        rbtree_subtree node.left lt (Some bp) **
        rbtree_subtree node.right rt (Some bp)

ghost fn cases_of_rbtree (x: rb_ptr) (ft: S.rbtree) (parent: rb_ptr)
  requires rbtree_subtree x ft parent
  ensures rbtree_cases x ft parent
{
  match ft {
    S.Leaf -> {
      unfold (rbtree_subtree x S.Leaf parent);
      fold (rbtree_cases (None #rb_node_ptr) ft parent);
      rewrite rbtree_cases (None #rb_node_ptr) ft parent
           as rbtree_cases x ft parent;
    }
    S.Node c l k r -> {
      unfold (rbtree_subtree x (S.Node c l k r) parent);
      with bp node. _;
      fold (rbtree_cases (Some bp) ft parent);
      rewrite (rbtree_cases (Some bp) ft parent)
           as rbtree_cases x ft parent;
    }
  }
}

ghost fn rbtree_case_none (x: rb_ptr) (#ft: S.rbtree) (#parent: rb_ptr)
  preserves rbtree_subtree x ft parent
  requires pure (x == None)
  ensures pure (ft == S.Leaf)
{
  rewrite each x as (None #rb_node_ptr);
  cases_of_rbtree (None #rb_node_ptr) ft parent;
  unfold rbtree_cases;
  intro_rbtree_leaf (None #rb_node_ptr) parent;
  rewrite rbtree_subtree (None #rb_node_ptr) S.Leaf parent
       as rbtree_subtree x ft parent;
  ()
}

ghost fn rbtree_case_some (x: rb_ptr) (bp: rb_node_ptr)
  (#ft: S.rbtree) (#parent: rb_ptr)
  requires rbtree_subtree x ft parent ** pure (x == Some bp)
  ensures exists* (node: rb_node) (lt rt: S.rbtree).
    (bp |-> node) **
    rbtree_subtree node.left lt (Some bp) **
    rbtree_subtree node.right rt (Some bp) **
    pure (ft == S.Node node.color lt node.key rt /\ node.p == parent)
{
  rewrite each x as (Some bp);
  cases_of_rbtree (Some bp) ft parent;
  unfold rbtree_cases;
}

// Learn that Node? ft implies Some? ct
ghost fn rbtree_not_leaf (x: rb_ptr) (#ft: S.rbtree) (#parent: rb_ptr)
  preserves rbtree_subtree x ft parent
  requires pure (S.Node? ft)
  ensures pure (Some? x)
{
  let S.Node c lt v rt = ft;
  unfold (rbtree_subtree x (S.Node c lt v rt) parent);
  with bp node. _;
  fold (rbtree_subtree x (S.Node c lt v rt) parent);
  rewrite rbtree_subtree x (S.Node c lt v rt) parent
       as rbtree_subtree x ft parent;
  ()
}

// Consume a Leaf subtree (null pointer)
ghost fn consume_rbtree_leaf (x: rb_ptr) (#ft: S.rbtree) (#parent: rb_ptr)
  requires rbtree_subtree x ft parent ** pure (x == None)
  ensures pure (ft == S.Leaf)
{
  rewrite each x as (None #rb_node_ptr);
  cases_of_rbtree (None #rb_node_ptr) ft parent;
  unfold rbtree_cases;
}

// ============================================================
// Helper: set_parent_ptr — update a subtree root's parent
// ============================================================

fn set_parent_ptr (child: rb_ptr) (new_parent: rb_ptr)
  requires rbtree_subtree child 'ft 'old_parent
  ensures rbtree_subtree child 'ft new_parent
{
  match child {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) 'ft 'old_parent
           as rbtree_subtree (None #rb_node_ptr) S.Leaf 'old_parent;
      elim_rbtree_leaf (None #rb_node_ptr);
      intro_rbtree_leaf (None #rb_node_ptr) new_parent;
      rewrite rbtree_subtree (None #rb_node_ptr) S.Leaf new_parent
           as rbtree_subtree child 'ft new_parent;
    }
    Some bp -> {
      rbtree_case_some (Some bp) bp;
      let nd = !bp;
      bp := { nd with p = new_parent };
      intro_rbtree_node (Some bp) bp;
      with t p. rewrite (rbtree_subtree (Some bp) t p)
                     as rbtree_subtree child 'ft new_parent;
    }
  }
}

// ============================================================
// Helper: new node
// ============================================================

fn new_node (k: int) (c: S.color) (l: rb_ptr) (r: rb_ptr) (parent: rb_ptr)
  (#lt #rt: G.erased S.rbtree) (#lp #rp: G.erased rb_ptr)
  requires rbtree_subtree l lt lp ** rbtree_subtree r rt rp
  returns y: rb_ptr
  ensures rbtree_subtree y (S.Node c lt k rt) parent ** pure (Some? y)
{
  let bp = Box.alloc ({ key = k; color = c; left = l; right = r; p = parent } <: rb_node);
  set_parent_ptr l (Some bp);
  set_parent_ptr r (Some bp);
  intro_rbtree_node (Some bp) bp;
  with t pp. rewrite (rbtree_subtree (Some bp) t pp)
       as (rbtree_subtree (Some bp) (S.Node c lt k rt) parent);
  Some bp
}

// ============================================================
// TREE-SEARCH (§12.2) — recursive, read-only
// ============================================================

fn rec rb_search (tree: rb_ptr) (k: int)
  preserves rbtree_subtree tree 'ft 'parent
  returns result: option int
  ensures pure (result == S.search 'ft k)
{
  match tree {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) 'ft 'parent
           as rbtree_subtree tree 'ft 'parent;
      None #int
    }
    Some bp -> {
      rbtree_case_some (Some bp) bp;
      let node = !bp;
      if (k < node.key) {
        let res = rb_search node.left k;
        intro_rbtree_node (Some bp) bp;
        with t p. rewrite (rbtree_subtree (Some bp) t p)
                       as (rbtree_subtree tree 'ft 'parent);
        res
      } else if (k > node.key) {
        let res = rb_search node.right k;
        intro_rbtree_node (Some bp) bp;
        with t p. rewrite (rbtree_subtree (Some bp) t p)
                       as (rbtree_subtree tree 'ft 'parent);
        res
      } else {
        intro_rbtree_node (Some bp) bp;
        with t p. rewrite (rbtree_subtree (Some bp) t p)
                       as (rbtree_subtree tree 'ft 'parent);
        Some node.key
      }
    }
  }
}

// ============================================================
// TREE-MINIMUM (§12.2)
// ============================================================

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
fn rec rb_minimum (tree: rb_ptr) (bp: rb_node_ptr)
  preserves rbtree_subtree tree 'ft 'parent
  requires pure (tree == Some bp)
  returns result: int
  ensures pure (S.Node? 'ft /\ result == S.minimum 'ft)
{
  rewrite each tree as (Some bp);
  rbtree_case_some (Some bp) bp;
  let nd = !bp;
  match nd.left {
    None -> {
      rbtree_case_none nd.left;
      intro_rbtree_node (Some bp) bp;
      with t p. rewrite (rbtree_subtree (Some bp) t p)
                     as rbtree_subtree tree 'ft 'parent;
      nd.key
    }
    Some lbp -> {
      let result = rb_minimum nd.left lbp;
      intro_rbtree_node (Some bp) bp;
      with t p. rewrite (rbtree_subtree (Some bp) t p)
                     as rbtree_subtree tree 'ft 'parent;
      result
    }
  }
}
#pop-options

// ============================================================
// Balance — runtime classification
// ============================================================

// Read-only: check if tree root has a specific color
fn is_color (tree: rb_ptr) (c: S.color)
  (#ft: G.erased S.rbtree) (#parent: G.erased rb_ptr)
  preserves rbtree_subtree tree ft parent
  returns b: bool
  ensures pure (b == (S.Node? ft && S.Node?.c ft = c))
{
  match tree {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) ft parent
           as rbtree_subtree tree ft parent;
      false
    }
    Some bp -> {
      rewrite each (Some bp) as tree;
      rbtree_case_some tree bp;
      let node = !bp;
      let res = (node.color = c);
      intro_rbtree_node tree bp;
      with t p. rewrite (rbtree_subtree tree t p)
                     as (rbtree_subtree tree ft parent);
      res
    }
  }
}

// Check left subtree for LL or LR balance case
// Opens the node, reads child colors with is_color (no nested opening),
// folds back, then classifies from pure values
fn check_left_balance (l: rb_ptr)
  (#lt: G.erased S.rbtree) (#lp: G.erased rb_ptr)
  preserves rbtree_subtree l lt lp
  returns bc: S.balance_case
  ensures pure (bc == (match lt with
    | S.Node S.Red (S.Node S.Red _ _ _) _ _ -> S.BC_LL
    | S.Node S.Red _ _ (S.Node S.Red _ _ _) -> S.BC_LR
    | _ -> S.BC_None))
{
  match l {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) lt lp
           as rbtree_subtree l lt lp;
      S.BC_None
    }
    Some lvl -> {
      rewrite each (Some lvl) as l;
      rbtree_case_some l lvl;
      let ln = !lvl;
      let ll_red = is_color ln.left S.Red;
      let lr_red = is_color ln.right S.Red;
      intro_rbtree_node l lvl;
      with t p. rewrite (rbtree_subtree l t p) as (rbtree_subtree l lt lp);
      if (S.Red? ln.color && ll_red) {
        S.BC_LL
      } else if (S.Red? ln.color && lr_red) {
        S.BC_LR
      } else {
        S.BC_None
      }
    }
  }
}

// Check right subtree for RL or RR balance case
fn check_right_balance (r: rb_ptr)
  (#rt: G.erased S.rbtree) (#rp: G.erased rb_ptr)
  preserves rbtree_subtree r rt rp
  returns bc: S.balance_case
  ensures pure (bc == (match rt with
    | S.Node S.Red (S.Node S.Red _ _ _) _ _ -> S.BC_RL
    | S.Node S.Red _ _ (S.Node S.Red _ _ _) -> S.BC_RR
    | _ -> S.BC_None))
{
  match r {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) rt rp
           as rbtree_subtree r rt rp;
      S.BC_None
    }
    Some rvl -> {
      rewrite each (Some rvl) as r;
      rbtree_case_some r rvl;
      let rn = !rvl;
      let rl_red = is_color rn.left S.Red;
      let rr_red = is_color rn.right S.Red;
      intro_rbtree_node r rvl;
      with t p. rewrite (rbtree_subtree r t p) as (rbtree_subtree r rt rp);
      if (S.Red? rn.color && rl_red) {
        S.BC_RL
      } else if (S.Red? rn.color && rr_red) {
        S.BC_RR
      } else {
        S.BC_None
      }
    }
  }
}

// Runtime classification matching S.classify_balance
fn classify_runtime (c: S.color) (l: rb_ptr) (r: rb_ptr)
  (#lt #rt: G.erased S.rbtree) (#lp #rp: G.erased rb_ptr)
  preserves rbtree_subtree l lt lp ** rbtree_subtree r rt rp
  returns bc: S.balance_case
  ensures pure (bc == S.classify_balance c lt rt)
{
  if (S.Red? c) {
    S.BC_None
  } else {
    let lbc = check_left_balance l;
    if (not (S.BC_None? lbc)) {
      lbc
    } else {
      check_right_balance r
    }
  }
}

// ============================================================
// Balance cases
// ============================================================

fn balance_ll (l: rb_ptr) (v: int) (r: rb_ptr) (parent: rb_ptr)
  (#lt #rt: G.erased S.rbtree) (#lp #rp: G.erased rb_ptr)
  requires rbtree_subtree l lt lp ** rbtree_subtree r rt rp **
           pure (S.BC_LL? (S.classify_balance S.Black lt rt))
  returns y: rb_ptr
  ensures rbtree_subtree y (S.balance S.Black lt v rt) parent
{
  S.classify_balance_lemma S.Black lt v rt;
  rbtree_not_leaf l;
  let lvl = Some?.v l;
  rbtree_case_some l lvl;
  let ln = !lvl;
  rbtree_not_leaf ln.left;
  let llvl = Some?.v ln.left;
  rewrite each (Some llvl) as ln.left;
  rbtree_case_some ln.left llvl;
  let lln = !llvl;
  // Reuse llvl for Node Black a x b
  llvl := { lln with color = S.Black };
  intro_rbtree_node ln.left llvl;
  // New node for Node Black c_ v r
  let right_black = new_node v S.Black ln.right r parent;
  // Reuse lvl for Node Red root
  Box.free lvl;
  let result = new_node ln.key S.Red ln.left right_black parent;
  with t. rewrite (rbtree_subtree result t parent)
       as (rbtree_subtree result (S.balance S.Black lt v rt) parent);
  result
}

fn balance_lr (l: rb_ptr) (v: int) (r: rb_ptr) (parent: rb_ptr)
  (#lt #rt: G.erased S.rbtree) (#lp #rp: G.erased rb_ptr)
  requires rbtree_subtree l lt lp ** rbtree_subtree r rt rp **
           pure (S.BC_LR? (S.classify_balance S.Black lt rt))
  returns y: rb_ptr
  ensures rbtree_subtree y (S.balance S.Black lt v rt) parent
{
  S.classify_balance_lemma S.Black lt v rt;
  rbtree_not_leaf l;
  let lvl = Some?.v l;
  rbtree_case_some l lvl;
  let ln = !lvl;
  rbtree_not_leaf ln.right;
  let lrvl = Some?.v ln.right;
  rewrite each (Some lrvl) as ln.right;
  rbtree_case_some ln.right lrvl;
  let lrn = !lrvl;
  // Reuse lvl for Node Black a x b
  lvl := { key = ln.key; color = S.Black; left = ln.left; right = lrn.left; p = parent };
  set_parent_ptr lrn.left (Some lvl);
  intro_rbtree_node l lvl;
  // New node for Node Black c_ v r
  let right_black = new_node v S.Black lrn.right r parent;
  // Reuse lrvl for Node Red root
  Box.free lrvl;
  let result = new_node lrn.key S.Red l right_black parent;
  with t. rewrite (rbtree_subtree result t parent)
       as (rbtree_subtree result (S.balance S.Black lt v rt) parent);
  result
}

fn balance_rl (l: rb_ptr) (v: int) (r: rb_ptr) (parent: rb_ptr)
  (#lt #rt: G.erased S.rbtree) (#lp #rp: G.erased rb_ptr)
  requires rbtree_subtree l lt lp ** rbtree_subtree r rt rp **
           pure (S.BC_RL? (S.classify_balance S.Black lt rt))
  returns y: rb_ptr
  ensures rbtree_subtree y (S.balance S.Black lt v rt) parent
{
  S.classify_balance_lemma S.Black lt v rt;
  rbtree_not_leaf r;
  let rvl = Some?.v r;
  rbtree_case_some r rvl;
  let rn = !rvl;
  rbtree_not_leaf rn.left;
  let rlvl = Some?.v rn.left;
  rewrite each (Some rlvl) as rn.left;
  rbtree_case_some rn.left rlvl;
  let rln = !rlvl;
  // New node for Node Black l v b
  let left_black = new_node v S.Black l rln.left parent;
  // Reuse rvl for Node Black c_ z d
  rvl := { key = rn.key; color = S.Black; left = rln.right; right = rn.right; p = parent };
  set_parent_ptr rln.right (Some rvl);
  intro_rbtree_node r rvl;
  // Reuse rlvl for Node Red root
  Box.free rlvl;
  let result = new_node rln.key S.Red left_black r parent;
  with t. rewrite (rbtree_subtree result t parent)
       as (rbtree_subtree result (S.balance S.Black lt v rt) parent);
  result
}

fn balance_rr (l: rb_ptr) (v: int) (r: rb_ptr) (parent: rb_ptr)
  (#lt #rt: G.erased S.rbtree) (#lp #rp: G.erased rb_ptr)
  requires rbtree_subtree l lt lp ** rbtree_subtree r rt rp **
           pure (S.BC_RR? (S.classify_balance S.Black lt rt))
  returns y: rb_ptr
  ensures rbtree_subtree y (S.balance S.Black lt v rt) parent
{
  S.classify_balance_lemma S.Black lt v rt;
  rbtree_not_leaf r;
  let rvl = Some?.v r;
  rbtree_case_some r rvl;
  let rn = !rvl;
  rbtree_not_leaf rn.right;
  let rrvl = Some?.v rn.right;
  rewrite each (Some rrvl) as rn.right;
  rbtree_case_some rn.right rrvl;
  let rrn = !rrvl;
  // New node for Node Black l v b
  let left_black = new_node v S.Black l rn.left parent;
  // Reuse rrvl for Node Black c_ z d
  rrvl := { rrn with color = S.Black };
  intro_rbtree_node rn.right rrvl;
  // Reuse rvl for Node Red root
  Box.free rvl;
  let result = new_node rn.key S.Red left_black rn.right parent;
  with t. rewrite (rbtree_subtree result t parent)
       as (rbtree_subtree result (S.balance S.Black lt v rt) parent);
  result
}

fn rb_balance (c: S.color) (l: rb_ptr) (v: int) (r: rb_ptr) (parent: rb_ptr)
  (#lt #rt: G.erased S.rbtree) (#lp #rp: G.erased rb_ptr)
  requires rbtree_subtree l lt lp ** rbtree_subtree r rt rp
  returns y: rb_ptr
  ensures rbtree_subtree y (S.balance c lt v rt) parent
{
  let bc = classify_runtime c l r;
  match bc {
    S.BC_LL -> {
      let y = balance_ll l v r parent;
      with t. rewrite (rbtree_subtree y t parent)
           as (rbtree_subtree y (S.balance c lt v rt) parent);
      y
    }
    S.BC_LR -> {
      let y = balance_lr l v r parent;
      with t. rewrite (rbtree_subtree y t parent)
           as (rbtree_subtree y (S.balance c lt v rt) parent);
      y
    }
    S.BC_RL -> {
      let y = balance_rl l v r parent;
      with t. rewrite (rbtree_subtree y t parent)
           as (rbtree_subtree y (S.balance c lt v rt) parent);
      y
    }
    S.BC_RR -> {
      let y = balance_rr l v r parent;
      with t. rewrite (rbtree_subtree y t parent)
           as (rbtree_subtree y (S.balance c lt v rt) parent);
      y
    }
    S.BC_None -> {
      S.classify_balance_lemma c lt v rt;
      let y = new_node v c l r parent;
      with t. rewrite (rbtree_subtree y t parent)
           as (rbtree_subtree y (S.balance c lt v rt) parent);
      y
    }
  }
}

// ============================================================
// Insert
// ============================================================

fn rec rb_ins (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft parent
  returns y: rb_ptr
  ensures rbtree_subtree y (S.ins 'ft k) parent
{
  match tree {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) 'ft parent
           as rbtree_subtree (None #rb_node_ptr) S.Leaf parent;
      elim_rbtree_leaf (None #rb_node_ptr);
      let left_leaf : rb_ptr = None #rb_node_ptr;
      intro_rbtree_leaf left_leaf (None #rb_node_ptr);
      let right_leaf : rb_ptr = None #rb_node_ptr;
      intro_rbtree_leaf right_leaf (None #rb_node_ptr);
      let y = new_node k S.Red left_leaf right_leaf parent;
      with t. rewrite (rbtree_subtree y t parent)
           as (rbtree_subtree y (S.ins 'ft k) parent);
      y
    }
    Some vl -> {
      rbtree_case_some (Some vl) vl;
      let node = !vl;
      if (k < node.key) {
        let new_left = rb_ins node.left k (Some vl);
        Box.free vl;
        let y = rb_balance node.color new_left node.key node.right parent;
        with t. rewrite (rbtree_subtree y t parent)
             as (rbtree_subtree y (S.ins 'ft k) parent);
        y
      } else if (k > node.key) {
        let new_right = rb_ins node.right k (Some vl);
        Box.free vl;
        let y = rb_balance node.color node.left node.key new_right parent;
        with t. rewrite (rbtree_subtree y t parent)
             as (rbtree_subtree y (S.ins 'ft k) parent);
        y
      } else {
        // Duplicate key
        vl := { node with p = parent };
        intro_rbtree_node (Some vl) vl;
        with t p. rewrite (rbtree_subtree (Some vl) t p)
             as (rbtree_subtree tree (S.ins 'ft k) parent);
        tree
      }
    }
  }
}

fn rb_make_black (tree: rb_ptr) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft 'old_parent
  returns y: rb_ptr
  ensures rbtree_subtree y (S.make_black 'ft) parent
{
  match tree {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) 'ft 'old_parent
           as rbtree_subtree (None #rb_node_ptr) S.Leaf 'old_parent;
      elim_rbtree_leaf (None #rb_node_ptr);
      intro_rbtree_leaf (None #rb_node_ptr) parent;
      rewrite rbtree_subtree (None #rb_node_ptr) S.Leaf parent
           as rbtree_subtree tree (S.make_black 'ft) parent;
      tree
    }
    Some vl -> {
      rbtree_case_some (Some vl) vl;
      let node = !vl;
      vl := { node with color = S.Black; p = parent };
      intro_rbtree_node (Some vl) vl;
      with t p. rewrite (rbtree_subtree (Some vl) t p)
           as (rbtree_subtree tree (S.make_black 'ft) parent);
      tree
    }
  }
}

fn rb_insert (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft parent
  returns y: rb_ptr
  ensures rbtree_subtree y (S.insert 'ft k) parent
{
  let t = rb_ins tree k parent;
  rb_make_black t parent
}

// ============================================================
// Delete — Kahrs-style
// ============================================================

fn rb_redden (tree: rb_ptr)
  requires rbtree_subtree tree 'ft 'parent
  returns y: rb_ptr
  ensures rbtree_subtree y (S.redden 'ft) 'parent
{
  match tree {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) 'ft 'parent
           as rbtree_subtree tree (S.redden 'ft) 'parent;
      tree
    }
    Some p -> {
      rbtree_case_some (Some p) p;
      let node = !p;
      if (S.Black? node.color) {
        p := { node with color = S.Red };
        intro_rbtree_node (Some p) p;
        with t pp. rewrite (rbtree_subtree (Some p) t pp)
             as (rbtree_subtree tree (S.redden 'ft) 'parent);
        tree
      } else {
        p := node;
        intro_rbtree_node (Some p) p;
        with t pp. rewrite (rbtree_subtree (Some p) t pp)
             as (rbtree_subtree tree (S.redden 'ft) 'parent);
        tree
      }
    }
  }
}

fn rb_balL (l: rb_ptr) (v: int) (r: rb_ptr) (parent: rb_ptr)
  (#lt #rt: G.erased S.rbtree) (#lp #rp: G.erased rb_ptr)
  requires rbtree_subtree l lt lp ** rbtree_subtree r rt rp
  returns y: rb_ptr
  ensures rbtree_subtree y (S.balL lt v rt) parent
{
  let l_red = is_color l S.Red;
  if l_red {
    // Case 1: Node Red a x b
    rbtree_not_leaf l;
    let lvl = Some?.v l;
    rbtree_case_some l lvl;
    let ln = !lvl;
    lvl := { ln with color = S.Black };
    intro_rbtree_node l lvl;
    let y = new_node v S.Red l r parent;
    with t. rewrite (rbtree_subtree y t parent)
         as (rbtree_subtree y (S.balL lt v rt) parent);
    y
  } else {
    let r_black = is_color r S.Black;
    if r_black {
      // Case 2: ..., Node Black a y b
      rbtree_not_leaf r;
      let rvl = Some?.v r;
      rbtree_case_some r rvl;
      let rn = !rvl;
      rvl := { rn with color = S.Red };
      intro_rbtree_node r rvl;
      let y = rb_balance S.Black l v r parent;
      with t. rewrite (rbtree_subtree y t parent)
           as (rbtree_subtree y (S.balL lt v rt) parent);
      y
    } else {
      let r_red = is_color r S.Red;
      if r_red {
        // Case 3: ..., Node Red (Node Black ...) y c
        rbtree_not_leaf r;
        let rvl = Some?.v r;
        rbtree_case_some r rvl;
        let rn = !rvl;
        let rl_black = is_color rn.left S.Black;
        if rl_black {
          rbtree_not_leaf rn.left;
          let rlvl = Some?.v rn.left;
          rewrite each (Some rlvl) as rn.left;
          rbtree_case_some rn.left rlvl;
          let rln = !rlvl;
          let rd = rb_redden rn.right;
          let right_balanced = rb_balance S.Black rln.right rn.key rd parent;
          let left_black = new_node v S.Black l rln.left parent;
          Box.free rvl;
          Box.free rlvl;
          let y = new_node rln.key S.Red left_black right_balanced parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (S.balL lt v rt) parent);
          y
        } else {
          // r is Red but r.left is not Black => fallback
          rvl := rn;
          intro_rbtree_node r rvl;
          with t p. rewrite (rbtree_subtree r t p) as (rbtree_subtree r rt rp);
          let y = new_node v S.Black l r parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (S.balL lt v rt) parent);
          y
        }
      } else {
        // Neither red nor black at root => Leaf or something; just make node
        let y = new_node v S.Black l r parent;
        with t. rewrite (rbtree_subtree y t parent)
             as (rbtree_subtree y (S.balL lt v rt) parent);
        y
      }
    }
  }
}

fn rb_balR (l: rb_ptr) (v: int) (r: rb_ptr) (parent: rb_ptr)
  (#lt #rt: G.erased S.rbtree) (#lp #rp: G.erased rb_ptr)
  requires rbtree_subtree l lt lp ** rbtree_subtree r rt rp
  returns y: rb_ptr
  ensures rbtree_subtree y (S.balR lt v rt) parent
{
  let r_red = is_color r S.Red;
  if r_red {
    rbtree_not_leaf r;
    let rvl = Some?.v r;
    rbtree_case_some r rvl;
    let rn = !rvl;
    rvl := { rn with color = S.Black };
    intro_rbtree_node r rvl;
    let y = new_node v S.Red l r parent;
    with t. rewrite (rbtree_subtree y t parent)
         as (rbtree_subtree y (S.balR lt v rt) parent);
    y
  } else {
    let l_black = is_color l S.Black;
    if l_black {
      rbtree_not_leaf l;
      let lvl = Some?.v l;
      rbtree_case_some l lvl;
      let ln = !lvl;
      lvl := { ln with color = S.Red };
      intro_rbtree_node l lvl;
      let y = rb_balance S.Black l v r parent;
      with t. rewrite (rbtree_subtree y t parent)
           as (rbtree_subtree y (S.balR lt v rt) parent);
      y
    } else {
      let l_red = is_color l S.Red;
      if l_red {
        rbtree_not_leaf l;
        let lvl = Some?.v l;
        rbtree_case_some l lvl;
        let ln = !lvl;
        let lr_black = is_color ln.right S.Black;
        if lr_black {
          rbtree_not_leaf ln.right;
          let lrvl = Some?.v ln.right;
          rewrite each (Some lrvl) as ln.right;
          rbtree_case_some ln.right lrvl;
          let lrn = !lrvl;
          let la = rb_redden ln.left;
          let left_balanced = rb_balance S.Black la ln.key lrn.left parent;
          let right_black = new_node v S.Black lrn.right r parent;
          Box.free lvl;
          Box.free lrvl;
          let y = new_node lrn.key S.Red left_balanced right_black parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (S.balR lt v rt) parent);
          y
        } else {
          lvl := ln;
          intro_rbtree_node l lvl;
          with t p. rewrite (rbtree_subtree l t p) as (rbtree_subtree l lt lp);
          let y = new_node v S.Black l r parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (S.balR lt v rt) parent);
          y
        }
      } else {
        let y = new_node v S.Black l r parent;
        with t. rewrite (rbtree_subtree y t parent)
             as (rbtree_subtree y (S.balR lt v rt) parent);
        y
      }
    }
  }
}

// fuse: merge two subtrees at deletion point
fn rec rb_fuse (l: rb_ptr) (r: rb_ptr) (parent: rb_ptr)
  (#lt #rt: G.erased S.rbtree) (#lp #rp: G.erased rb_ptr)
  requires rbtree_subtree l lt lp ** rbtree_subtree r rt rp
  returns y: rb_ptr
  ensures rbtree_subtree y (S.fuse lt rt) parent
  decreases (S.node_count lt + S.node_count rt)
{
  match l {
    None -> {
      consume_rbtree_leaf (None #rb_node_ptr);
      set_parent_ptr r parent;
      with t. rewrite (rbtree_subtree r t parent)
           as (rbtree_subtree r (S.fuse lt rt) parent);
      r
    }
    Some lvl -> {
      rewrite each (Some lvl) as l;
      match r {
        None -> {
          consume_rbtree_leaf (None #rb_node_ptr);
          set_parent_ptr l parent;
          with t. rewrite (rbtree_subtree l t parent)
               as (rbtree_subtree l (S.fuse lt rt) parent);
          l
        }
        Some rvl -> {
          rewrite each (Some rvl) as r;
          rbtree_case_some l lvl;
          rbtree_case_some r rvl;
          let ln = !lvl;
          let rn = !rvl;
          if (S.Red? ln.color && S.Red? rn.color) {
            let s = rb_fuse ln.right rn.left (None #rb_node_ptr);
            let s_red = is_color s S.Red;
            if s_red {
              rbtree_not_leaf s;
              let svl = Some?.v s;
              rbtree_case_some s svl;
              let sn = !svl;
              lvl := { key = ln.key; color = S.Red; left = ln.left; right = sn.left; p = parent };
              set_parent_ptr sn.left (Some lvl);
              intro_rbtree_node l lvl;
              rvl := { key = rn.key; color = S.Red; left = sn.right; right = rn.right; p = parent };
              set_parent_ptr sn.right (Some rvl);
              intro_rbtree_node r rvl;
              svl := { key = sn.key; color = S.Red; left = l; right = r; p = parent };
              set_parent_ptr l (Some svl);
              set_parent_ptr r (Some svl);
              intro_rbtree_node s svl;
              with t pp. rewrite (rbtree_subtree s t pp)
                   as (rbtree_subtree s (S.fuse lt rt) parent);
              s
            } else {
              rvl := { key = rn.key; color = S.Red; left = s; right = rn.right; p = parent };
              set_parent_ptr s (Some rvl);
              intro_rbtree_node r rvl;
              lvl := { key = ln.key; color = S.Red; left = ln.left; right = r; p = parent };
              set_parent_ptr r (Some lvl);
              intro_rbtree_node l lvl;
              with t pp. rewrite (rbtree_subtree l t pp)
                   as (rbtree_subtree l (S.fuse lt rt) parent);
              l
            }
          } else if (S.Black? ln.color && S.Black? rn.color) {
            let s = rb_fuse ln.right rn.left (None #rb_node_ptr);
            let s_red = is_color s S.Red;
            if s_red {
              rbtree_not_leaf s;
              let svl = Some?.v s;
              rbtree_case_some s svl;
              let sn = !svl;
              lvl := { key = ln.key; color = S.Black; left = ln.left; right = sn.left; p = parent };
              set_parent_ptr sn.left (Some lvl);
              intro_rbtree_node l lvl;
              rvl := { key = rn.key; color = S.Black; left = sn.right; right = rn.right; p = parent };
              set_parent_ptr sn.right (Some rvl);
              intro_rbtree_node r rvl;
              svl := { key = sn.key; color = S.Red; left = l; right = r; p = parent };
              set_parent_ptr l (Some svl);
              set_parent_ptr r (Some svl);
              intro_rbtree_node s svl;
              with t pp. rewrite (rbtree_subtree s t pp)
                   as (rbtree_subtree s (S.fuse lt rt) parent);
              s
            } else {
              rvl := { key = rn.key; color = S.Black; left = s; right = rn.right; p = parent };
              set_parent_ptr s (Some rvl);
              intro_rbtree_node r rvl;
              Box.free lvl;
              let y = rb_balL ln.left ln.key r parent;
              with t. rewrite (rbtree_subtree y t parent)
                   as (rbtree_subtree y (S.fuse lt rt) parent);
              y
            }
          } else if (S.Red? ln.color) {
            rvl := rn;
            intro_rbtree_node r rvl;
            with t p. rewrite (rbtree_subtree r t p) as (rbtree_subtree r rt rp);
            let fused = rb_fuse ln.right r (None #rb_node_ptr);
            lvl := { key = ln.key; color = S.Red; left = ln.left; right = fused; p = parent };
            set_parent_ptr fused (Some lvl);
            intro_rbtree_node l lvl;
            with t pp. rewrite (rbtree_subtree l t pp)
                 as (rbtree_subtree l (S.fuse lt rt) parent);
            l
          } else {
            lvl := ln;
            intro_rbtree_node l lvl;
            with t p. rewrite (rbtree_subtree l t p) as (rbtree_subtree l lt lp);
            let fused = rb_fuse l rn.left (None #rb_node_ptr);
            rvl := { key = rn.key; color = S.Red; left = fused; right = rn.right; p = parent };
            set_parent_ptr fused (Some rvl);
            intro_rbtree_node r rvl;
            with t pp. rewrite (rbtree_subtree r t pp)
                 as (rbtree_subtree r (S.fuse lt rt) parent);
            r
          }
        }
      }
    }
  }
}

// del: recursive delete helper
fn rec rb_del (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft 'old_parent
  returns y: rb_ptr
  ensures rbtree_subtree y (S.del 'ft k) parent
  decreases 'ft
{
  match tree {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) 'ft 'old_parent
           as rbtree_subtree (None #rb_node_ptr) S.Leaf 'old_parent;
      elim_rbtree_leaf (None #rb_node_ptr);
      intro_rbtree_leaf (None #rb_node_ptr) parent;
      rewrite rbtree_subtree (None #rb_node_ptr) S.Leaf parent
           as rbtree_subtree tree (S.del 'ft k) parent;
      tree
    }
    Some vl -> {
      rbtree_case_some (Some vl) vl;
      let node = !vl;
      if (k < node.key) {
        let l_was_black = is_color node.left S.Black;
        let new_left = rb_del node.left k (None #rb_node_ptr);
        if l_was_black {
          Box.free vl;
          let y = rb_balL new_left node.key node.right parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (S.del 'ft k) parent);
          y
        } else {
          Box.free vl;
          let y = new_node node.key S.Red new_left node.right parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (S.del 'ft k) parent);
          y
        }
      } else if (k > node.key) {
        let r_was_black = is_color node.right S.Black;
        let new_right = rb_del node.right k (None #rb_node_ptr);
        if r_was_black {
          Box.free vl;
          let y = rb_balR node.left node.key new_right parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (S.del 'ft k) parent);
          y
        } else {
          Box.free vl;
          let y = new_node node.key S.Red node.left new_right parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (S.del 'ft k) parent);
          y
        }
      } else {
        Box.free vl;
        let y = rb_fuse node.left node.right parent;
        with t. rewrite (rbtree_subtree y t parent)
             as (rbtree_subtree y (S.del 'ft k) parent);
        y
      }
    }
  }
}

fn rb_delete (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft 'old_parent
  returns y: rb_ptr
  ensures rbtree_subtree y (S.delete 'ft k) parent
{
  let t = rb_del tree k parent;
  rb_make_black t parent
}

// ============================================================
// Deallocation
// ============================================================

fn rec free_rbtree (tree: rb_ptr)
  requires rbtree_subtree tree 'ft 'parent
  ensures emp
  decreases 'ft
{
  match tree {
    None -> {
      cases_of_rbtree (None #rb_node_ptr) 'ft 'parent;
      unfold rbtree_cases
    }
    Some bp -> {
      rbtree_case_some (Some bp) bp;
      let node = !bp;
      free_rbtree node.left;
      free_rbtree node.right;
      Box.free bp
    }
  }
}

// ============================================================
// Validated API — bundles BST + RB invariants
// ============================================================

let valid_rbtree (ct: rb_ptr) (ft: S.rbtree) (parent: rb_ptr) : slprop =
  rbtree_subtree ct ft parent ** pure (S.is_rbtree ft /\ S.is_bst ft)

ghost fn elim_valid (ct: rb_ptr) (#ft: G.erased S.rbtree) (#parent: G.erased rb_ptr)
  requires valid_rbtree ct ft parent
  ensures rbtree_subtree ct ft parent ** pure (S.is_rbtree ft /\ S.is_bst ft)
{
  unfold valid_rbtree
}

ghost fn intro_valid (ct: rb_ptr) (#ft: G.erased S.rbtree) (#parent: G.erased rb_ptr)
  requires rbtree_subtree ct ft parent ** pure (S.is_rbtree ft /\ S.is_bst ft)
  ensures valid_rbtree ct ft parent
{
  fold (valid_rbtree ct ft parent)
}

fn rb_new ()
  requires emp
  returns y: rb_ptr
  ensures valid_rbtree y S.Leaf (None #rb_node_ptr)
{
  let y : rb_ptr = None #rb_node_ptr;
  intro_rbtree_leaf y (None #rb_node_ptr);
  fold (valid_rbtree y S.Leaf (None #rb_node_ptr));
  y
}

fn rb_search_v (tree: rb_ptr) (k: int)
  (#parent: G.erased rb_ptr)
  preserves valid_rbtree tree 'ft parent
  returns result: option int
  ensures pure (result == S.search 'ft k)
{
  unfold valid_rbtree;
  let result = rb_search tree k;
  fold (valid_rbtree tree 'ft parent);
  result
}

fn rb_insert_v (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires valid_rbtree tree 'ft parent
  returns y: rb_ptr
  ensures valid_rbtree y (S.insert 'ft k) parent **
          pure (S.mem k (S.insert 'ft k) = true)
{
  unfold valid_rbtree;
  S.insert_preserves_bst 'ft k;
  S.insert_is_rbtree 'ft k;
  S.insert_mem 'ft k k;
  let y = rb_insert tree k parent;
  fold (valid_rbtree y (S.insert 'ft k) parent);
  y
}

fn rb_delete_v (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires valid_rbtree tree 'ft parent
  returns y: rb_ptr
  ensures valid_rbtree y (S.delete 'ft k) parent **
          pure (S.mem k (S.delete 'ft k) = false)
{
  unfold valid_rbtree;
  S.delete_preserves_bst 'ft k;
  S.delete_is_rbtree 'ft k;
  S.delete_mem 'ft k k;
  let y = rb_delete tree k parent;
  fold (valid_rbtree y (S.delete 'ft k) parent);
  y
}

fn free_valid_rbtree (tree: rb_ptr)
  requires valid_rbtree tree 'ft 'parent
  ensures emp
{
  unfold valid_rbtree;
  free_rbtree tree
}
