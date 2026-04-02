(*
   Red-Black Tree — CLRS-faithful imperative implementation in Pulse

   CLRS Chapter 13: Red-Black Trees with parent pointers.
   Uses Pulse.Lib.Box heap-allocated nodes with nullable option pointers.

   Implements:
   - TREE-SEARCH (§12.2): recursive BST search, O(h)
   - TREE-MINIMUM / TREE-MAXIMUM (§12.2): walk left/right to min/max
   - RB-INSERT with CLRS INSERT-FIXUP (§13.3)
     Checks uncle color: Red→recolor, Black→rotate
   - RB-DELETE with CLRS DELETE-FIXUP (§13.4)
     Successor-based delete with 4-case rotation fixup
   - TREE-FREE: recursive deallocation of all nodes

   Each operation's postcondition links to the pure spec in
   CLRS.Ch13.RBTree.CLRSSpec — full functional correctness, no admits.

   Node type: { key, color, left, right, p } with parent pointer.
   Pointer type: option (box rb_node) for nullable pointers.
   Separation logic predicate: rbtree_subtree ct ft parent.

   The parent pointer design follows CLRS.Ch12.BST (ch12-bst):
   each node stores its parent as a value in the `p` field,
   but ownership flows downward through left/right only.
*)

module CLRS.Ch13.RBTree.CLRSImpl
#lang-pulse
open Pulse.Lib.Pervasives

module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }

module S = CLRS.Ch13.RBTree.Spec
module CS = CLRS.Ch13.RBTree.CLRSSpec
module G = FStar.Ghost
module L = CLRS.Ch13.RBTree.Lemmas
module C = CLRS.Ch13.RBTree.Complexity
module CC = CLRS.Ch13.RBTree.CLRSComplexity
open FStar.Mul

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

// Learn that Some? ct implies Node? ft (converse of rbtree_not_leaf)
ghost fn rbtree_some_is_node (x: rb_ptr) (bp: rb_node_ptr)
  (#ft: S.rbtree) (#parent: rb_ptr)
  preserves rbtree_subtree x ft parent
  requires pure (x == Some bp)
  ensures pure (S.Node? ft)
{
  rewrite each x as (Some bp);
  cases_of_rbtree (Some bp) ft parent;
  unfold rbtree_cases;
  with node lt rt. _;
  fold (rbtree_subtree (Some bp) (S.Node node.color lt node.key rt) parent);
  rewrite rbtree_subtree (Some bp) (S.Node node.color lt node.key rt) parent
       as rbtree_subtree x ft parent;
  ()
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
  decreases 'ft
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

#push-options "--fuel 1 --ifuel 1 --z3rlimit 5"
fn rec rb_minimum (tree: rb_ptr) (bp: rb_node_ptr)
  preserves rbtree_subtree tree 'ft 'parent
  requires pure (tree == Some bp)
  returns result: int
  ensures pure (S.Node? 'ft /\ result == S.minimum 'ft)
  decreases 'ft
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
// §13.2 — Helper: set node color (in-place)
// ============================================================

fn set_node_color (tree: rb_ptr) (c: S.color)
  requires rbtree_subtree tree 'ft 'parent
  returns y: rb_ptr
  ensures rbtree_subtree y (CS.set_color c 'ft) 'parent ** pure (y == tree)
{
  match tree {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) 'ft 'parent
           as rbtree_subtree tree (CS.set_color c 'ft) 'parent;
      tree
    }
    Some bp -> {
      rbtree_case_some (Some bp) bp;
      let node = !bp;
      bp := { node with color = c };
      intro_rbtree_node (Some bp) bp;
      with t p. rewrite (rbtree_subtree (Some bp) t p)
                     as (rbtree_subtree tree (CS.set_color c 'ft) 'parent);
      tree
    }
  }
}

// ============================================================
// §13.3 — CLRS INSERT-FIXUP
//
//   CLRS-FIXUP-LEFT(c, l, v, r):
//     if c = RED
//       return Node(RED, l, v, r)
//     // c = BLACK: check left child for red-red violation
//     case ← classify l            // LL, LR, or None
//     if case ∈ {LL, LR}
//       if r is RED                // Case 1: uncle Red → recolor
//         l.color ← BLACK
//         r.color ← BLACK
//         return Node(RED, l, v, r)
//       else if case = LL          // Case 3: right-rotate
//         // l = Node Red (Node Red a x b) y c'
//         new_r ← Node(RED, l.right, v, r)
//         l.color ← BLACK
//         l.right ← new_r
//         return l
//       else                       // Case 2→3: left-rotate l, then right-rotate
//         // l = Node Red a y (Node Red b x c')
//         lr ← l.right             // Node Red b x c'
//         l.right ← lr.left        // a y b
//         new_r ← Node(RED, lr.right, v, r)
//         lr.color ← BLACK
//         lr.left ← l; lr.right ← new_r
//         return lr
//     else                         // No violation
//       return Node(BLACK, l, v, r)
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

// Check if left subtree has LL or LR red-red pattern
fn check_left_violation (l: rb_ptr)
  (#lt: G.erased S.rbtree) (#lp: G.erased rb_ptr)
  preserves rbtree_subtree l lt lp
  returns r: (bool & bool)   // (has_violation, is_LL)
  ensures pure (
    (fst r = true /\ snd r = true <==>
       (match lt with S.Node S.Red (S.Node S.Red _ _ _) _ _ -> true | _ -> false)) /\
    (fst r = true /\ snd r = false <==>
       (match lt with S.Node S.Red _ _ (S.Node S.Red _ _ _) -> true | _ -> false) /\
       ~(match lt with S.Node S.Red (S.Node S.Red _ _ _) _ _ -> true | _ -> false)) /\
    (fst r = false ==>
       ~(match lt with S.Node S.Red (S.Node S.Red _ _ _) _ _ -> true | _ -> false) /\
       ~(match lt with S.Node S.Red _ _ (S.Node S.Red _ _ _) -> true | _ -> false)))
{
  match l {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) lt lp
           as rbtree_subtree l lt lp;
      (false, false)
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
        (true, true)   // LL
      } else if (S.Red? ln.color && lr_red) {
        (true, false)  // LR
      } else {
        (false, false) // No violation
      }
    }
  }
}

// Check if right subtree has RL or RR red-red pattern
fn check_right_violation (r: rb_ptr)
  (#rt: G.erased S.rbtree) (#rp: G.erased rb_ptr)
  preserves rbtree_subtree r rt rp
  returns res: (bool & bool)   // (has_violation, is_RL)
  ensures pure (
    (fst res = true /\ snd res = true <==>
       (match rt with S.Node S.Red (S.Node S.Red _ _ _) _ _ -> true | _ -> false)) /\
    (fst res = true /\ snd res = false <==>
       (match rt with S.Node S.Red _ _ (S.Node S.Red _ _ _) -> true | _ -> false) /\
       ~(match rt with S.Node S.Red (S.Node S.Red _ _ _) _ _ -> true | _ -> false)) /\
    (fst res = false ==>
       ~(match rt with S.Node S.Red (S.Node S.Red _ _ _) _ _ -> true | _ -> false) /\
       ~(match rt with S.Node S.Red _ _ (S.Node S.Red _ _ _) -> true | _ -> false)))
{
  match r {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) rt rp
           as rbtree_subtree r rt rp;
      (false, false)
    }
    Some rvl -> {
      rewrite each (Some rvl) as r;
      rbtree_case_some r rvl;
      let rn = !rvl;
      let rl_red = is_color rn.left S.Red;
      let rr_red = is_color rn.right S.Red;
      intro_rbtree_node r rvl;
      with t p. rewrite (rbtree_subtree r t p) as (rbtree_subtree r rt rp);
      // Check RL first to match spec pattern-matching order
      if (S.Red? rn.color && rl_red) {
        (true, true)   // RL
      } else if (S.Red? rn.color && rr_red) {
        (true, false)  // RR
      } else {
        (false, false) // No violation
      }
    }
  }
}

// CLRS INSERT-FIXUP for left insertion
fn rb_clrs_fixup_left (c: S.color) (l: rb_ptr) (v: int) (r: rb_ptr) (parent: rb_ptr)
  (#lt #rt: G.erased S.rbtree) (#lp #rp: G.erased rb_ptr)
  requires rbtree_subtree l lt lp ** rbtree_subtree r rt rp
  returns y: rb_ptr
  ensures rbtree_subtree y (CS.clrs_fixup_left c lt v rt) parent
{
  if (S.Red? c) {
    // Red parent: no fixup, just build Node Red l v r
    let y = new_node v S.Red l r parent;
    with t. rewrite (rbtree_subtree y t parent)
         as (rbtree_subtree y (CS.clrs_fixup_left c lt v rt) parent);
    y
  } else {
    // Black parent: check for red-red violation in l
    let viol = check_left_violation l;
    let has_viol = fst viol;
    let is_ll = snd viol;
    if has_viol {
      // Red-red violation in l; check uncle color
      let uncle_red = is_color r S.Red;
      if uncle_red {
        // Case 1: uncle Red → recolor both children, Red root
        let l' = set_node_color l S.Black;
        let r' = set_node_color r S.Black;
        let y = new_node v S.Red l' r' parent;
        with t. rewrite (rbtree_subtree y t parent)
             as (rbtree_subtree y (CS.clrs_fixup_left c lt v rt) parent);
        y
      } else if is_ll {
        // Case 3 (LL): right-rotate
        // l = Node Red (Node Red a x b) y c'
        // Result: Node Black ll lv (Node Red lr v r)
        rbtree_not_leaf l;
        let lvl = Some?.v l;
        rbtree_case_some l lvl;
        let ln = !lvl;
        // ln.left = ll = Node Red a x b (kept as-is)
        // ln.right = lr = c' (goes into new right child)
        let new_right = new_node v S.Red ln.right r parent;
        lvl := { key = ln.key; color = S.Black; left = ln.left; right = new_right; p = parent };
        set_parent_ptr new_right (Some lvl);
        set_parent_ptr ln.left (Some lvl);
        intro_rbtree_node l lvl;
        with t pp. rewrite (rbtree_subtree l t pp)
             as (rbtree_subtree l (CS.clrs_fixup_left c lt v rt) parent);
        l
      } else {
        // Case 2→3 (LR): left-rotate l, then right-rotate
        // l = Node Red a y (Node Red b x c')
        // Result: Node Black (Node Red a y b) x (Node Red c' v r)
        rbtree_not_leaf l;
        let lvl = Some?.v l;
        rbtree_case_some l lvl;
        let ln = !lvl;
        rbtree_not_leaf ln.right;
        let lrvl = Some?.v ln.right;
        rbtree_case_some ln.right lrvl;
        let lrn = !lrvl;
        // Reuse lvl for Node Red a y b
        lvl := { key = ln.key; color = S.Red; left = ln.left; right = lrn.left; p = parent };
        set_parent_ptr lrn.left (Some lvl);
        intro_rbtree_node l lvl;
        // Create new right: Node Red c' v r
        let new_right = new_node v S.Red lrn.right r parent;
        // Reuse lrvl for root: Node Black (Node Red a y b) x (Node Red c' v r)
        lrvl := { key = lrn.key; color = S.Black; left = l; right = new_right; p = parent };
        set_parent_ptr l (Some lrvl);
        set_parent_ptr new_right (Some lrvl);
        intro_rbtree_node (Some lrvl) lrvl;
        with t pp. rewrite (rbtree_subtree (Some lrvl) t pp)
             as (rbtree_subtree (Some lrvl) (CS.clrs_fixup_left c lt v rt) parent);
        Some lrvl
      }
    } else {
      // No violation: just build Node Black l v r
      let y = new_node v S.Black l r parent;
      with t. rewrite (rbtree_subtree y t parent)
           as (rbtree_subtree y (CS.clrs_fixup_left c lt v rt) parent);
      y
    }
  }
}

// ============================================================
// Symmetric: CLRS INSERT-FIXUP for right insertion
//
//   CLRS-FIXUP-RIGHT(c, l, v, r):
//     Same as FIXUP-LEFT but mirror: check r for violation,
//     l is the uncle. RR→left-rotate, RL→right-rotate then left-rotate.
// ============================================================

fn rb_clrs_fixup_right (c: S.color) (l: rb_ptr) (v: int) (r: rb_ptr) (parent: rb_ptr)
  (#lt #rt: G.erased S.rbtree) (#lp #rp: G.erased rb_ptr)
  requires rbtree_subtree l lt lp ** rbtree_subtree r rt rp
  returns y: rb_ptr
  ensures rbtree_subtree y (CS.clrs_fixup_right c lt v rt) parent
{
  if (S.Red? c) {
    let y = new_node v S.Red l r parent;
    with t. rewrite (rbtree_subtree y t parent)
         as (rbtree_subtree y (CS.clrs_fixup_right c lt v rt) parent);
    y
  } else {
    let viol = check_right_violation r;
    let has_viol = fst viol;
    let is_rl = snd viol;
    if has_viol {
      let uncle_red = is_color l S.Red;
      if uncle_red {
        // Case 1: uncle Red → recolor
        let l' = set_node_color l S.Black;
        let r' = set_node_color r S.Black;
        let y = new_node v S.Red l' r' parent;
        with t. rewrite (rbtree_subtree y t parent)
             as (rbtree_subtree y (CS.clrs_fixup_right c lt v rt) parent);
        y
      } else if is_rl {
        // Case 3→4 (RL): right-rotate r, then left-rotate
        // r = Node Red (Node Red b y c') z d
        // Result: Node Black (Node Red l v b) y (Node Red c' z d)
        rbtree_not_leaf r;
        let rvl = Some?.v r;
        rbtree_case_some r rvl;
        let rn = !rvl;
        rbtree_not_leaf rn.left;
        let rlvl = Some?.v rn.left;
        rbtree_case_some rn.left rlvl;
        let rln = !rlvl;
        // Reuse rvl for Node Red c' z d
        rvl := { key = rn.key; color = S.Red; left = rln.right; right = rn.right; p = parent };
        set_parent_ptr rln.right (Some rvl);
        intro_rbtree_node r rvl;
        // Create new left: Node Red l v b
        let new_left = new_node v S.Red l rln.left parent;
        // Reuse rlvl for root: Node Black (...) y (...)
        rlvl := { key = rln.key; color = S.Black; left = new_left; right = r; p = parent };
        set_parent_ptr new_left (Some rlvl);
        set_parent_ptr r (Some rlvl);
        intro_rbtree_node (Some rlvl) rlvl;
        with t pp. rewrite (rbtree_subtree (Some rlvl) t pp)
             as (rbtree_subtree (Some rlvl) (CS.clrs_fixup_right c lt v rt) parent);
        Some rlvl
      } else {
        // Case 4 (RR): left-rotate
        // r = Node Red b z (Node Red c' y d)
        // Result: Node Black (Node Red l v b) z rr
        rbtree_not_leaf r;
        let rvl = Some?.v r;
        rbtree_case_some r rvl;
        let rn = !rvl;
        let new_left = new_node v S.Red l rn.left parent;
        rvl := { key = rn.key; color = S.Black; left = new_left; right = rn.right; p = parent };
        set_parent_ptr new_left (Some rvl);
        set_parent_ptr rn.right (Some rvl);
        intro_rbtree_node r rvl;
        with t pp. rewrite (rbtree_subtree r t pp)
             as (rbtree_subtree r (CS.clrs_fixup_right c lt v rt) parent);
        r
      }
    } else {
      let y = new_node v S.Black l r parent;
      with t. rewrite (rbtree_subtree y t parent)
           as (rbtree_subtree y (CS.clrs_fixup_right c lt v rt) parent);
      y
    }
  }
}

// ============================================================
// §13.3 — CLRS INSERT
//
//   CLRS-INSERT(T, k):
//     T.root ← CLRS-INS(T.root, k)
//     T.root.color ← BLACK
//
//   CLRS-INS(x, k):
//     if x = NIL
//       return Node(RED, NIL, k, NIL)
//     if k < x.key
//       x.left ← CLRS-INS(x.left, k)
//       return CLRS-FIXUP-LEFT(x.color, x.left, x.key, x.right)
//     else if k > x.key
//       x.right ← CLRS-INS(x.right, k)
//       return CLRS-FIXUP-RIGHT(x.color, x.left, x.key, x.right)
//     else return x   // duplicate
// ============================================================

fn rec rb_clrs_ins (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft parent
  returns y: rb_ptr
  ensures rbtree_subtree y (CS.clrs_ins 'ft k) parent
  decreases 'ft
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
           as (rbtree_subtree y (CS.clrs_ins 'ft k) parent);
      y
    }
    Some vl -> {
      rbtree_case_some (Some vl) vl;
      let node = !vl;
      if (k < node.key) {
        let new_left = rb_clrs_ins node.left k (Some vl);
        Box.free vl;
        let y = rb_clrs_fixup_left node.color new_left node.key node.right parent;
        with t. rewrite (rbtree_subtree y t parent)
             as (rbtree_subtree y (CS.clrs_ins 'ft k) parent);
        y
      } else if (k > node.key) {
        let new_right = rb_clrs_ins node.right k (Some vl);
        Box.free vl;
        let y = rb_clrs_fixup_right node.color node.left node.key new_right parent;
        with t. rewrite (rbtree_subtree y t parent)
             as (rbtree_subtree y (CS.clrs_ins 'ft k) parent);
        y
      } else {
        // Duplicate key
        vl := { node with p = parent };
        intro_rbtree_node (Some vl) vl;
        with t p. rewrite (rbtree_subtree (Some vl) t p)
             as (rbtree_subtree tree (CS.clrs_ins 'ft k) parent);
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

fn rb_clrs_insert (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft parent
  returns y: rb_ptr
  ensures rbtree_subtree y (CS.clrs_insert 'ft k) parent
{
  let t = rb_clrs_ins tree k parent;
  rb_make_black t parent
}

// ============================================================
// §13.4 — CLRS DELETE-FIXUP
//
//   DELETE-FIXUP handles the case where removing a Black node
//   creates a black-height deficit. The deficit is on one side
//   (left or right) and the sibling (w) is on the other side.
//
//   CLRS-DEL-CASES234-LEFT(c, x, v, w):
//     // x has deficit, w is Black sibling (right child)
//     // w = Node Black wl wy wr
//     if not is_red(wl) and not is_red(wr)
//       // Case 2: recolor w Red, propagate deficit if c=Black
//       return (Node c x v (Node Red wl wy wr), c=Black)
//     else if is_red(wr)
//       // Case 4: left-rotate at parent
//       return (Node c (Node Black x v wl) wy (set_color Black wr), false)
//     else
//       // Case 3: wl is Red; right-rotate w, then Case 4
//       wl = Node _ wll wlv wlr
//       return (Node c (Node Black x v wll) wlv (Node Black wlr wy wr), false)
//
//   CLRS-RESOLVE-LEFT(c, x, v, w):
//     if w is Red
//       // Case 1: left-rotate at parent
//       let (inner, deficit) = CASES234(Red, x, v, wl)
//       return (Node Black inner wy wr, deficit)
//     else
//       CASES234(c, x, v, w)
// ============================================================

fn rb_clrs_del_cases234_left
  (c: S.color) (x: rb_ptr) (v: int) (w: rb_ptr) (parent: rb_ptr)
  (#xt #wt: G.erased S.rbtree) (#xp #wp: G.erased rb_ptr)
  requires rbtree_subtree x xt xp ** rbtree_subtree w wt wp
  returns res: (rb_ptr & bool)
  ensures rbtree_subtree (fst res) (fst (CS.clrs_del_cases234_left c xt v wt)) parent **
          pure (snd res == snd (CS.clrs_del_cases234_left c xt v wt))
{
  match w {
    None -> {
      // w is Leaf — shouldn't happen in valid RB, but handle gracefully
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) wt wp
           as rbtree_subtree w wt wp;
      let y = new_node v c x w parent;
      with t. rewrite (rbtree_subtree y t parent)
           as (rbtree_subtree y (fst (CS.clrs_del_cases234_left c xt v wt)) parent);
      (y, true)
    }
    Some wvl -> {
      rewrite each (Some wvl) as w;
      rbtree_case_some w wvl;
      let wn = !wvl;
      if (S.Black? wn.color) {
        // w is Black — Cases 2/3/4
        let wl_red = is_color wn.left S.Red;
        let wr_red = is_color wn.right S.Red;
        if (not wl_red && not wr_red) {
          // Case 2: recolor w Red
          wvl := { wn with color = S.Red; p = parent };
          intro_rbtree_node w wvl;
          let y = new_node v S.Black x w parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (fst (CS.clrs_del_cases234_left c xt v wt)) parent);
          (y, (S.Black? c))
        } else if wr_red {
          // Case 4: left-rotate at parent
          // Result: Node c (Node Black x v wl) wy (set_color Black wr)
          let left_child = new_node v S.Black x wn.left parent;
          let wr' = set_node_color wn.right S.Black;
          Box.free wvl;
          let y = new_node wn.key c left_child wr' parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (fst (CS.clrs_del_cases234_left c xt v wt)) parent);
          (y, false)
        } else {
          // Case 3: wl Red, wr not Red -> right-rotate w then left-rotate
          // wl = Node _ wll wlv wlr
          // Result: Node c (Node Black x v wll) wlv (Node Black wlr wy wr)
          rbtree_not_leaf wn.left;
          let wlvl = Some?.v wn.left;
          rbtree_case_some wn.left wlvl;
          let wln = !wlvl;
          let left_child = new_node v S.Black x wln.left parent;
          // Reuse wvl for Node Black wlr wy wr
          wvl := { key = wn.key; color = S.Black; left = wln.right; right = wn.right; p = parent };
          set_parent_ptr wln.right (Some wvl);
          intro_rbtree_node w wvl;
          Box.free wlvl;
          let y = new_node wln.key c left_child w parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (fst (CS.clrs_del_cases234_left c xt v wt)) parent);
          (y, false)
        }
      } else {
        // w is not Black — fall through (shouldn't happen for cases234)
        intro_rbtree_node w wvl;
        let y = new_node v c x w parent;
        with t. rewrite (rbtree_subtree y t parent)
             as (rbtree_subtree y (fst (CS.clrs_del_cases234_left c xt v wt)) parent);
        (y, true)
      }
    }
  }
}

fn rb_clrs_resolve_left
  (c: S.color) (x: rb_ptr) (v: int) (w: rb_ptr) (parent: rb_ptr)
  (#xt #wt: G.erased S.rbtree) (#xp #wp: G.erased rb_ptr)
  requires rbtree_subtree x xt xp ** rbtree_subtree w wt wp
  returns res: (rb_ptr & bool)
  ensures rbtree_subtree (fst res) (fst (CS.clrs_resolve_left c xt v wt)) parent **
          pure (snd res == snd (CS.clrs_resolve_left c xt v wt))
{
  match w {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) wt wp
           as rbtree_subtree w wt wp;
      let y = new_node v c x w parent;
      with t. rewrite (rbtree_subtree y t parent)
           as (rbtree_subtree y (fst (CS.clrs_resolve_left c xt v wt)) parent);
      (y, true)
    }
    Some wvl -> {
      rewrite each (Some wvl) as w;
      rbtree_case_some w wvl;
      let wn = !wvl;
      if (S.Red? wn.color) {
        // Case 1: w is Red -> left-rotate at parent
        // inner = cases234(Red, x, v, wn.left)
        // result = Node Black inner wy wr
        let inner = rb_clrs_del_cases234_left S.Red x v wn.left parent;
        let y = new_node wn.key S.Black (fst inner) wn.right parent;
        Box.free wvl;
        with t. rewrite (rbtree_subtree y t parent)
             as (rbtree_subtree y (fst (CS.clrs_resolve_left c xt v wt)) parent);
        (y, snd inner)
      } else {
        // w is Black -> direct cases234
        intro_rbtree_node w wvl;
        let res = rb_clrs_del_cases234_left c x v w parent;
        with t. rewrite (rbtree_subtree (fst res) t parent)
             as (rbtree_subtree (fst res) (fst (CS.clrs_resolve_left c xt v wt)) parent);
        res
      }
    }
  }
}

// ============================================================
// Symmetric: CLRS-DEL-CASES234-RIGHT and RESOLVE-RIGHT
//
//   CLRS-DEL-CASES234-RIGHT(c, w, v, x):
//     // x has deficit, w is Black sibling (left child)
//     Same as LEFT but mirrored — left-right swapped
//
//   CLRS-RESOLVE-RIGHT(c, w, v, x):
//     if w is Red
//       // Case 1: right-rotate at parent
//       let (inner, deficit) = CASES234-RIGHT(Red, wr, v, x)
//       return (Node Black wl wy inner, deficit)
//     else
//       CASES234-RIGHT(c, w, v, x)
// ============================================================

fn rb_clrs_del_cases234_right
  (c: S.color) (w: rb_ptr) (v: int) (x: rb_ptr) (parent: rb_ptr)
  (#wt #xt: G.erased S.rbtree) (#wp #xp: G.erased rb_ptr)
  requires rbtree_subtree w wt wp ** rbtree_subtree x xt xp
  returns res: (rb_ptr & bool)
  ensures rbtree_subtree (fst res) (fst (CS.clrs_del_cases234_right c wt v xt)) parent **
          pure (snd res == snd (CS.clrs_del_cases234_right c wt v xt))
{
  match w {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) wt wp
           as rbtree_subtree w wt wp;
      let y = new_node v c w x parent;
      with t. rewrite (rbtree_subtree y t parent)
           as (rbtree_subtree y (fst (CS.clrs_del_cases234_right c wt v xt)) parent);
      (y, true)
    }
    Some wvl -> {
      rewrite each (Some wvl) as w;
      rbtree_case_some w wvl;
      let wn = !wvl;
      if (S.Black? wn.color) {
        let wl_red = is_color wn.left S.Red;
        let wr_red = is_color wn.right S.Red;
        if (not wl_red && not wr_red) {
          // Case 2: recolor w Red
          wvl := { wn with color = S.Red; p = parent };
          intro_rbtree_node w wvl;
          let y = new_node v S.Black w x parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (fst (CS.clrs_del_cases234_right c wt v xt)) parent);
          (y, (S.Black? c))
        } else if wl_red {
          // Case 4 (sym): right-rotate at parent
          // Result: Node c (set_color Black wl) wy (Node Black wr v x)
          let wl' = set_node_color wn.left S.Black;
          let right_child = new_node v S.Black wn.right x parent;
          Box.free wvl;
          let y = new_node wn.key c wl' right_child parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (fst (CS.clrs_del_cases234_right c wt v xt)) parent);
          (y, false)
        } else {
          // Case 3 (sym): wr Red, wl not Red -> left-rotate w then right-rotate
          // wr = Node _ wrl wrv wrr
          // Result: Node c (Node Black wl wy wrl) wrv (Node Black wrr v x)
          rbtree_not_leaf wn.right;
          let wrvl = Some?.v wn.right;
          rbtree_case_some wn.right wrvl;
          let wrn = !wrvl;
          let right_child = new_node v S.Black wrn.right x parent;
          // Reuse wvl for Node Black wl wy wrl
          wvl := { key = wn.key; color = S.Black; left = wn.left; right = wrn.left; p = parent };
          set_parent_ptr wrn.left (Some wvl);
          intro_rbtree_node w wvl;
          Box.free wrvl;
          let y = new_node wrn.key c w right_child parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (fst (CS.clrs_del_cases234_right c wt v xt)) parent);
          (y, false)
        }
      } else {
        intro_rbtree_node w wvl;
        let y = new_node v c w x parent;
        with t. rewrite (rbtree_subtree y t parent)
             as (rbtree_subtree y (fst (CS.clrs_del_cases234_right c wt v xt)) parent);
        (y, true)
      }
    }
  }
}

fn rb_clrs_resolve_right
  (c: S.color) (w: rb_ptr) (v: int) (x: rb_ptr) (parent: rb_ptr)
  (#wt #xt: G.erased S.rbtree) (#wp #xp: G.erased rb_ptr)
  requires rbtree_subtree w wt wp ** rbtree_subtree x xt xp
  returns res: (rb_ptr & bool)
  ensures rbtree_subtree (fst res) (fst (CS.clrs_resolve_right c wt v xt)) parent **
          pure (snd res == snd (CS.clrs_resolve_right c wt v xt))
{
  match w {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) wt wp
           as rbtree_subtree w wt wp;
      let y = new_node v c w x parent;
      with t. rewrite (rbtree_subtree y t parent)
           as (rbtree_subtree y (fst (CS.clrs_resolve_right c wt v xt)) parent);
      (y, true)
    }
    Some wvl -> {
      rewrite each (Some wvl) as w;
      rbtree_case_some w wvl;
      let wn = !wvl;
      if (S.Red? wn.color) {
        // Case 1: w is Red -> right-rotate at parent
        let inner = rb_clrs_del_cases234_right S.Red wn.right v x parent;
        let y = new_node wn.key S.Black wn.left (fst inner) parent;
        Box.free wvl;
        with t. rewrite (rbtree_subtree y t parent)
             as (rbtree_subtree y (fst (CS.clrs_resolve_right c wt v xt)) parent);
        (y, snd inner)
      } else {
        intro_rbtree_node w wvl;
        let res = rb_clrs_del_cases234_right c w v x parent;
        with t. rewrite (rbtree_subtree (fst res) t parent)
             as (rbtree_subtree (fst res) (fst (CS.clrs_resolve_right c wt v xt)) parent);
        res
      }
    }
  }
}

// ============================================================
// §13.4 — CLRS DELETE
//
//   CLRS-DEL(T, k):
//     if T = NIL
//       return (NIL, false)
//     if k < T.key
//       (T.left, deficit) <- CLRS-DEL(T.left, k)
//       if deficit then RESOLVE-LEFT(T.color, T.left, T.key, T.right)
//       else Node(T.color, T.left, T.key, T.right)
//     else if k > T.key
//       (T.right, deficit) <- CLRS-DEL(T.right, k)
//       if deficit then RESOLVE-RIGHT(T.color, T.left, T.key, T.right)
//       else Node(T.color, T.left, T.key, T.right)
//     else   // k = T.key — delete this node
//       case T.left, T.right of
//       | NIL, NIL -> (NIL, T.color = BLACK)
//       | NIL, Node _ rl rv rr -> (Node BLACK rl rv rr, false)
//       | Node _ ll lv lr, NIL -> (Node BLACK ll lv lr, false)
//       | _, _ ->
//         sk <- MINIMUM(T.right)
//         (T.right, deficit) <- CLRS-DEL(T.right, sk)
//         if deficit then RESOLVE-RIGHT(T.color, T.left, sk, T.right)
//         else Node(T.color, T.left, sk, T.right)
//
//   CLRS-DELETE(T, k):
//     T <- CLRS-DEL(T, k).fst
//     T.color <- BLACK
//     return T
// ============================================================

fn rec rb_clrs_del (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft parent
  returns res: (rb_ptr & bool)
  ensures rbtree_subtree (fst res) (fst (CS.clrs_del 'ft k)) parent **
          pure (snd res == snd (CS.clrs_del 'ft k))
  decreases 'ft
{
  match tree {
    None -> {
      rbtree_case_none (None #rb_node_ptr);
      rewrite rbtree_subtree (None #rb_node_ptr) 'ft parent
           as rbtree_subtree (None #rb_node_ptr) S.Leaf parent;
      elim_rbtree_leaf (None #rb_node_ptr);
      intro_rbtree_leaf (None #rb_node_ptr) parent;
      rewrite rbtree_subtree (None #rb_node_ptr) S.Leaf parent
           as rbtree_subtree (None #rb_node_ptr) (fst (CS.clrs_del 'ft k)) parent;
      ((None #rb_node_ptr), false)
    }
    Some vl -> {
      rbtree_case_some (Some vl) vl;
      let node = !vl;
      if (k < node.key) {
        let res = rb_clrs_del node.left k (Some vl);
        Box.free vl;
        if (snd res) {
          let y = rb_clrs_resolve_left node.color (fst res) node.key node.right parent;
          with t. rewrite (rbtree_subtree (fst y) t parent)
               as (rbtree_subtree (fst y) (fst (CS.clrs_del 'ft k)) parent);
          y
        } else {
          let y = new_node node.key node.color (fst res) node.right parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (fst (CS.clrs_del 'ft k)) parent);
          (y, false)
        }
      } else if (k > node.key) {
        let res = rb_clrs_del node.right k (Some vl);
        Box.free vl;
        if (snd res) {
          let y = rb_clrs_resolve_right node.color node.left node.key (fst res) parent;
          with t. rewrite (rbtree_subtree (fst y) t parent)
               as (rbtree_subtree (fst y) (fst (CS.clrs_del 'ft k)) parent);
          y
        } else {
          let y = new_node node.key node.color node.left (fst res) parent;
          with t. rewrite (rbtree_subtree y t parent)
               as (rbtree_subtree y (fst (CS.clrs_del 'ft k)) parent);
          (y, false)
        }
      } else {
        // k = node.key — delete this node
        match node.left {
          None -> {
            consume_rbtree_leaf node.left;
            match node.right {
              None -> {
                // Both children Leaf: delete node, deficit if Black
                consume_rbtree_leaf node.right;
                Box.free vl;
                let leaf : rb_ptr = None #rb_node_ptr;
                intro_rbtree_leaf leaf parent;
                rewrite rbtree_subtree leaf S.Leaf parent
                     as rbtree_subtree leaf (fst (CS.clrs_del 'ft k)) parent;
                (leaf, (S.Black? node.color))
              }
              Some rbp -> {
                // Left is Leaf, Right is Node: replace with Black(right's children)
                rbtree_some_is_node node.right rbp;
                rbtree_case_some node.right rbp;
                let rn = !rbp;
                Box.free vl;
                rbp := { rn with color = S.Black; p = parent };
                intro_rbtree_node (Some rbp) rbp;
                with t p. rewrite (rbtree_subtree (Some rbp) t p)
                     as (rbtree_subtree (Some rbp) (fst (CS.clrs_del 'ft k)) parent);
                ((Some rbp), false)
              }
            }
          }
          Some lbp -> {
            match node.right {
              None -> {
                // Left is Node, Right is Leaf: replace with Black(left's children)
                consume_rbtree_leaf node.right;
                rbtree_some_is_node node.left lbp;
                rbtree_case_some node.left lbp;
                let ln = !lbp;
                Box.free vl;
                lbp := { ln with color = S.Black; p = parent };
                intro_rbtree_node (Some lbp) lbp;
                with t p. rewrite (rbtree_subtree (Some lbp) t p)
                     as (rbtree_subtree (Some lbp) (fst (CS.clrs_del 'ft k)) parent);
                ((Some lbp), false)
              }
              Some rbp -> {
                // Both children are Nodes: successor-based delete
                // Establish Node? lt and Node? rt for the spec's pattern match
                rbtree_some_is_node node.left lbp;
                rbtree_some_is_node node.right rbp;
                let sk = rb_minimum node.right rbp;
                let res = rb_clrs_del node.right sk (Some vl);
                Box.free vl;
                if (snd res) {
                  let y = rb_clrs_resolve_right node.color node.left sk (fst res) parent;
                  with t. rewrite (rbtree_subtree (fst y) t parent)
                       as (rbtree_subtree (fst y) (fst (CS.clrs_del 'ft k)) parent);
                  y
                } else {
                  let y = new_node sk node.color node.left (fst res) parent;
                  with t. rewrite (rbtree_subtree y t parent)
                       as (rbtree_subtree y (fst (CS.clrs_del 'ft k)) parent);
                  (y, false)
                }
              }
            }
          }
        }
      }
    }
  }
}

fn rb_clrs_delete (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires rbtree_subtree tree 'ft 'old_parent
  returns y: rb_ptr
  ensures rbtree_subtree y (CS.clrs_delete 'ft k) parent
{
  set_parent_ptr tree parent;
  let res = rb_clrs_del tree k parent;
  rb_make_black (fst res) parent
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
  ensures valid_rbtree y (CS.clrs_insert 'ft k) parent **
          pure (S.mem k (CS.clrs_insert 'ft k) = true)
{
  unfold valid_rbtree;
  CS.clrs_insert_preserves_bst 'ft k;
  CS.clrs_insert_is_rbtree 'ft k;
  CS.clrs_insert_mem 'ft k k;
  let y = rb_clrs_insert tree k parent;
  fold (valid_rbtree y (CS.clrs_insert 'ft k) parent);
  y
}

fn rb_delete_v (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires valid_rbtree tree 'ft parent
  returns y: rb_ptr
  ensures valid_rbtree y (CS.clrs_delete 'ft k) parent **
          pure (S.mem k (CS.clrs_delete 'ft k) = false)
{
  unfold valid_rbtree;
  CS.clrs_delete_preserves_bst 'ft k;
  CS.clrs_delete_is_rbtree 'ft k;
  CS.clrs_delete_mem 'ft k k;
  let y = rb_clrs_delete tree k parent;
  fold (valid_rbtree y (CS.clrs_delete 'ft k) parent);
  y
}

fn free_valid_rbtree (tree: rb_ptr)
  requires valid_rbtree tree 'ft 'parent
  ensures emp
{
  unfold valid_rbtree;
  free_rbtree tree
}

// ============================================================
// Complexity-aware API
// ============================================================

// Search with complexity bound: O(h) steps
fn rb_search_log (tree: rb_ptr) (k: int)
  (#parent: G.erased rb_ptr)
  preserves valid_rbtree tree 'ft parent
  returns result: option int
  ensures pure (result == S.search 'ft k /\
                C.search_ticks 'ft k <= S.height 'ft + 1)
{
  unfold valid_rbtree;
  C.search_ticks_bounded 'ft k;
  let result = rb_search tree k;
  fold (valid_rbtree tree 'ft parent);
  result
}

// Insert with complexity bound: O(h) steps
fn rb_clrs_insert_log (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires valid_rbtree tree 'ft parent
  returns y: rb_ptr
  ensures valid_rbtree y (CS.clrs_insert 'ft k) parent **
          pure (S.mem k (CS.clrs_insert 'ft k) = true /\
                CC.clrs_insert_ticks 'ft k <= S.height 'ft + 2)
{
  unfold valid_rbtree;
  CS.clrs_insert_preserves_bst 'ft k;
  CS.clrs_insert_is_rbtree 'ft k;
  CS.clrs_insert_mem 'ft k k;
  CC.clrs_insert_ticks_bounded 'ft k;
  let y = rb_clrs_insert tree k parent;
  fold (valid_rbtree y (CS.clrs_insert 'ft k) parent);
  y
}

// Delete with complexity bound: O(h) steps
fn rb_clrs_delete_log (tree: rb_ptr) (k: int) (parent: rb_ptr)
  requires valid_rbtree tree 'ft parent
  returns y: rb_ptr
  ensures valid_rbtree y (CS.clrs_delete 'ft k) parent **
          pure (S.mem k (CS.clrs_delete 'ft k) = false /\
                CC.clrs_delete_ticks 'ft k <= 2 * S.height 'ft + 2)
{
  unfold valid_rbtree;
  CS.clrs_delete_preserves_bst 'ft k;
  CS.clrs_delete_is_rbtree 'ft k;
  CS.clrs_delete_mem 'ft k k;
  CC.clrs_delete_ticks_bounded 'ft k;
  let y = rb_clrs_delete tree k parent;
  fold (valid_rbtree y (CS.clrs_delete 'ft k) parent);
  y
}
