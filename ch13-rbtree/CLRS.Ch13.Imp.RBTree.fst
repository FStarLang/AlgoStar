(*
   Red-Black Tree — CLRS-faithful imperative implementation in Pulse

   CLRS Chapter 13: Red-Black Trees with parent pointers and sentinel.
   Array-backed node pool: index 0 = sentinel T.nil (always Black).

   Implements faithfully:
   - LEFT-ROTATE, RIGHT-ROTATE (§13.2)
   - RB-INSERT with RB-INSERT-FIXUP (§13.3)
   - RB-DELETE with RB-TRANSPLANT and RB-DELETE-FIXUP (§13.4)
   - TREE-SEARCH, TREE-MINIMUM (§12.2)

   Design: Uses an array pool where nodes are stored by index.
   Index 0 is the sentinel (T.nil in CLRS), always Black.
   Bounds-checking is assumed via read_node/write_node helpers;
   a full verification would derive these from a well-formedness
   invariant (all indices in bounds for a valid tree).
*)

module CLRS.Ch13.Imp.RBTree
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
module A  = Pulse.Lib.Array
module R  = Pulse.Lib.Reference
module SZ = FStar.SizeT

// ========== Colors ==========

type color = | Red | Black

// ========== Node data (with parent pointer) ==========

noeq
type node_data = {
  key:   int;
  color: color;
  left:  SZ.t;
  right: SZ.t;
  p:     SZ.t;      // parent pointer
}

let nil_idx : SZ.t = 0sz

let is_nil (x: SZ.t) : bool = x = nil_idx

let nil_node : node_data = {
  key = 0; color = Black; left = nil_idx; right = nil_idx; p = nil_idx
}

// ========== Helpers (encapsulate bounds assumptions) ==========

inline_for_extraction
fn read_node (pool: A.array node_data) (i: SZ.t)
  requires A.pts_to pool 's
  returns nd: node_data
  ensures A.pts_to pool 's
{
  assume_ (pure (SZ.v i < Seq.length 's));
  A.op_Array_Access pool i
}

inline_for_extraction
fn write_node (pool: A.array node_data) (i: SZ.t) (nd: node_data)
  requires A.pts_to pool 's
  ensures exists* s'. A.pts_to pool s'
{
  assume_ (pure (SZ.v i < Seq.length 's));
  A.op_Array_Assignment pool i nd
}

// Set parent of `c` to `new_p`, unless `c` is nil (sentinel).
inline_for_extraction
fn set_parent_if_nonnull
  (pool: A.array node_data) (c: SZ.t) (new_p: SZ.t)
  requires A.pts_to pool 's
  ensures exists* s'. A.pts_to pool s'
{
  if (not (is_nil c)) {
    let cn = read_node pool c;
    write_node pool c ({ cn with p = new_p })
  }
}

// Link `parent`'s child pointer (that pointed to `old_child`) to `new_child`.
// If parent is nil (i.e., old_child was root), update root instead.
inline_for_extraction
fn link_parent
  (pool: A.array node_data) (root: R.ref SZ.t)
  (parent: SZ.t) (old_child: SZ.t) (new_child: SZ.t)
  requires A.pts_to pool 's ** R.pts_to root 'r
  ensures exists* s' r'. A.pts_to pool s' ** R.pts_to root r'
{
  if (is_nil parent) {
    root := new_child
  } else {
    let pn = read_node pool parent;
    if (pn.left = old_child) {
      write_node pool parent ({ pn with left = new_child })
    } else {
      write_node pool parent ({ pn with right = new_child })
    }
  }
}

// ========== LEFT-ROTATE (§13.2) ==========
// Rotates x down-left, making x.right the new subtree root.
//
// CLRS pseudocode:
//   y = x.right
//   x.right = y.left
//   if y.left ≠ T.nil  then  y.left.p = x
//   y.p = x.p
//   if x.p == T.nil then T.root = y
//   elseif x == x.p.left then x.p.left = y
//   else x.p.right = y
//   y.left = x
//   x.p = y

fn left_rotate
  (pool: A.array node_data) (root: R.ref SZ.t) (x: SZ.t)
  requires A.pts_to pool 's ** R.pts_to root 'r
  ensures exists* s' r'. A.pts_to pool s' ** R.pts_to root r'
{
  let xn = read_node pool x;
  let y = xn.right;
  let yn = read_node pool y;
  // x.right = y.left
  write_node pool x ({ xn with right = yn.left });
  // if y.left ≠ T.nil: y.left.p = x
  set_parent_if_nonnull pool yn.left x;
  // y.p = x.p
  let yn2 = read_node pool y;
  write_node pool y ({ yn2 with p = xn.p });
  // Link x's parent to y
  link_parent pool root xn.p x y;
  // y.left = x
  let yn3 = read_node pool y;
  write_node pool y ({ yn3 with left = x });
  // x.p = y
  let xn2 = read_node pool x;
  write_node pool x ({ xn2 with p = y })
}

// ========== RIGHT-ROTATE (symmetric to LEFT-ROTATE) ==========
// Rotates y down-right, making y.left the new subtree root.

fn right_rotate
  (pool: A.array node_data) (root: R.ref SZ.t) (y: SZ.t)
  requires A.pts_to pool 's ** R.pts_to root 'r
  ensures exists* s' r'. A.pts_to pool s' ** R.pts_to root r'
{
  let yn = read_node pool y;
  let x = yn.left;
  let xn = read_node pool x;
  // y.left = x.right
  write_node pool y ({ yn with left = xn.right });
  // if x.right ≠ T.nil: x.right.p = y
  set_parent_if_nonnull pool xn.right y;
  // x.p = y.p
  let xn2 = read_node pool x;
  write_node pool x ({ xn2 with p = yn.p });
  // Link y's parent to x
  link_parent pool root yn.p y x;
  // x.right = y
  let xn3 = read_node pool x;
  write_node pool x ({ xn3 with right = y });
  // y.p = x
  let yn2 = read_node pool y;
  write_node pool y ({ yn2 with p = x })
}

// ========== RB-TRANSPLANT (§13.4) ==========
// Replaces subtree rooted at u with subtree rooted at v.

fn rb_transplant
  (pool: A.array node_data) (root: R.ref SZ.t) (u v: SZ.t)
  requires A.pts_to pool 's ** R.pts_to root 'r
  ensures exists* s' r'. A.pts_to pool s' ** R.pts_to root r'
{
  let un = read_node pool u;
  // Link u's parent to v
  link_parent pool root un.p u v;
  // v.p = u.p
  let vn = read_node pool v;
  write_node pool v ({ vn with p = un.p })
}

// ========== TREE-MINIMUM (§12.2) ==========
// Walk left until left child is nil.

fn tree_minimum
  (pool: A.array node_data) (x0: SZ.t)
  requires A.pts_to pool 's
  returns m: SZ.t
  ensures A.pts_to pool 's
{
  let mut cur = x0;
  let mut cont = (not (is_nil x0));
  while ( !cont )
  invariant exists* cv curv. (
    A.pts_to pool 's ** R.pts_to cur curv ** R.pts_to cont cv
  )
  {
    let c = !cur;
    let cn = read_node pool c;
    if (is_nil cn.left) {
      cont := false
    } else {
      cur := cn.left
    }
  };
  !cur
}

// ========== TREE-SEARCH (§12.2) ==========
// Walk down comparing keys. Returns nil_idx if not found.

fn tree_search
  (pool: A.array node_data) (root: SZ.t) (k: int)
  requires A.pts_to pool 's
  returns x: SZ.t
  ensures A.pts_to pool 's
{
  let mut cur = root;
  let mut cont = (not (is_nil root));
  while ( !cont )
  invariant exists* curv cv. (
    A.pts_to pool 's ** R.pts_to cur curv ** R.pts_to cont cv
  )
  {
    let c = !cur;
    let cn = read_node pool c;
    if (cn.key = k) {
      cont := false
    } else {
      if (k < cn.key) {
        cur := cn.left;
        cont := (not (is_nil cn.left))
      } else {
        cur := cn.right;
        cont := (not (is_nil cn.right))
      }
    }
  };
  !cur
}

// ========== RB-INSERT-FIXUP (§13.3) ==========
// Restores RB properties after inserting a red node.
// 3 cases + 3 symmetric cases.
//
// while z.p.color == RED:
//   if z.p == z.p.p.left:            -- z's parent is left child
//     y = z.p.p.right                -- uncle
//     Case 1: y.color == RED → recolor parent, uncle, grandparent; z = z.p.p
//     Case 2: z == z.p.right → z = z.p; LEFT-ROTATE(T, z)
//     Case 3: recolor parent + grandparent; RIGHT-ROTATE(T, z.p.p)
//   else: (symmetric with left↔right)
// T.root.color = BLACK

// Case 2 helper (left variant): if z is a right child, rotate it up
inline_for_extraction
fn fixup_case2_left
  (pool: A.array node_data) (root: R.ref SZ.t) (z: R.ref SZ.t) (zp: SZ.t)
  requires A.pts_to pool 's ** R.pts_to root 'r ** R.pts_to z 'zv
  ensures exists* s' r' zv'. A.pts_to pool s' ** R.pts_to root r' ** R.pts_to z zv'
{
  let pnd = read_node pool zp;
  let zv = !z;
  if (zv = pnd.right) {
    z := zp;
    left_rotate pool root zp
  }
}

// Case 2 helper (right variant): if z is a left child, rotate it up
inline_for_extraction
fn fixup_case2_right
  (pool: A.array node_data) (root: R.ref SZ.t) (z: R.ref SZ.t) (zp: SZ.t)
  requires A.pts_to pool 's ** R.pts_to root 'r ** R.pts_to z 'zv
  ensures exists* s' r' zv'. A.pts_to pool s' ** R.pts_to root r' ** R.pts_to z zv'
{
  let pnd = read_node pool zp;
  let zv = !z;
  if (zv = pnd.left) {
    z := zp;
    right_rotate pool root zp
  }
}

fn rb_insert_fixup
  (pool: A.array node_data) (root: R.ref SZ.t) (z0: SZ.t)
  requires A.pts_to pool 's ** R.pts_to root 'r
  ensures exists* s' r'. A.pts_to pool s' ** R.pts_to root r'
{
  let mut z = z0;
  let mut cont = true;
  while ( !cont )
  invariant exists* s' r' zv cv. (
    A.pts_to pool s' ** R.pts_to root r' **
    R.pts_to z zv ** R.pts_to cont cv
  )
  {
    let zv = !z;
    let zn = read_node pool zv;
    let pn = read_node pool zn.p;
    if (pn.color = Red) {
      let zp = zn.p;
      let pn_rd = read_node pool zp;
      let zpp = pn_rd.p;
      let ppn = read_node pool zpp;
      if (zp = ppn.left) {
        // z.p is LEFT child of grandparent
        let uncle = ppn.right;
        let un = read_node pool uncle;
        if (un.color = Red) {
          // Case 1: uncle is red → recolor
          let pnd = read_node pool zp;
          write_node pool zp ({ pnd with color = Black });
          write_node pool uncle ({ un with color = Black });
          let ppnd = read_node pool zpp;
          write_node pool zpp ({ ppnd with color = Red });
          z := zpp
        } else {
          // Case 2 → Case 3
          fixup_case2_left pool root z zp;
          // Case 3: recolor + right rotate
          let zv3 = !z;
          let zn3 = read_node pool zv3;
          let zp3 = zn3.p;
          let pnd3 = read_node pool zp3;
          write_node pool zp3 ({ pnd3 with color = Black });
          let zpp3 = pnd3.p;
          let ppnd3 = read_node pool zpp3;
          write_node pool zpp3 ({ ppnd3 with color = Red });
          right_rotate pool root zpp3
        }
      } else {
        // Symmetric: z.p is RIGHT child of grandparent
        let uncle = ppn.left;
        let un = read_node pool uncle;
        if (un.color = Red) {
          // Case 1 symmetric
          let pnd = read_node pool zp;
          write_node pool zp ({ pnd with color = Black });
          write_node pool uncle ({ un with color = Black });
          let ppnd = read_node pool zpp;
          write_node pool zpp ({ ppnd with color = Red });
          z := zpp
        } else {
          // Case 2 → Case 3 (symmetric)
          fixup_case2_right pool root z zp;
          // Case 3 symmetric: recolor + left rotate
          let zv3 = !z;
          let zn3 = read_node pool zv3;
          let zp3 = zn3.p;
          let pnd3 = read_node pool zp3;
          write_node pool zp3 ({ pnd3 with color = Black });
          let zpp3 = pnd3.p;
          let ppnd3 = read_node pool zpp3;
          write_node pool zpp3 ({ ppnd3 with color = Red });
          left_rotate pool root zpp3
        }
      }
    } else {
      // z.p.color is Black → done
      cont := false
    }
  };
  // T.root.color = BLACK
  let r = !root;
  let rn = read_node pool r;
  write_node pool r ({ rn with color = Black })
}

// ========== RB-INSERT (§13.3) ==========
// Walk down to find insertion point, create red node, call fixup.
// `next_id` is the next free slot in the pool (simple bump allocator).

// Attach new node z to parent yy, or set as root if tree was empty.
inline_for_extraction
fn attach_child
  (pool: A.array node_data) (root: R.ref SZ.t) (yv: SZ.t) (z: SZ.t) (k: int)
  requires A.pts_to pool 's ** R.pts_to root 'r
  ensures exists* s' r'. A.pts_to pool s' ** R.pts_to root r'
{
  if (is_nil yv) {
    root := z
  } else {
    let yn = read_node pool yv;
    if (k < yn.key) {
      write_node pool yv ({ yn with left = z })
    } else {
      write_node pool yv ({ yn with right = z })
    }
  }
}

fn rb_insert
  (pool: A.array node_data) (root: R.ref SZ.t) (next_id: R.ref SZ.t) (k: int)
  requires A.pts_to pool 's ** R.pts_to root 'r ** R.pts_to next_id 'n
  ensures exists* s' r' n'. A.pts_to pool s' ** R.pts_to root r' ** R.pts_to next_id n'
{
  let r = !root;
  let mut yy = nil_idx;
  let mut xx = r;
  let mut cont = (not (is_nil r));
  // Walk down: yy tracks parent, xx tracks current
  while ( !cont )
  invariant exists* s' r' n' xv yv cv. (
    A.pts_to pool s' ** R.pts_to root r' ** R.pts_to next_id n' **
    R.pts_to xx xv ** R.pts_to yy yv ** R.pts_to cont cv
  )
  {
    let xv = !xx;
    let xn = read_node pool xv;
    yy := xv;
    if (k < xn.key) {
      xx := xn.left;
      cont := (not (is_nil xn.left))
    } else {
      xx := xn.right;
      cont := (not (is_nil xn.right))
    }
  };
  // z = next_id; next_id++
  let z = !next_id;
  assume_ (pure (SZ.fits (SZ.v z + 1)));
  let next_val = SZ.add z 1sz;
  next_id := next_val;
  // Initialize z: key=k, color=Red, left=nil, right=nil, p=y
  let yv = !yy;
  write_node pool z ({ key = k; color = Red; left = nil_idx; right = nil_idx; p = yv });
  // Attach z to parent
  attach_child pool root yv z k;
  // Fixup
  rb_insert_fixup pool root z
}

// ========== RB-DELETE-FIXUP (§13.4) ==========
// Restores RB properties after delete. 4 cases + 4 symmetric.
//
// while x ≠ T.root and x.color == BLACK:
//   if x == x.p.left:
//     w = x.p.right (sibling)
//     Case 1: w is red → recolor + left-rotate parent
//     Case 2: both w's children black → recolor w, x = x.p
//     Case 3: w.right black → recolor + right-rotate w
//     Case 4: w.right red → recolor + left-rotate parent, x = root
//   else: (symmetric)
// x.color = BLACK

// Case 1 left helper: if sibling w is red, recolor + left rotate + update w
inline_for_extraction
fn fixup_case1_left
  (pool: A.array node_data) (root: R.ref SZ.t) (w: R.ref SZ.t) (xp: SZ.t)
  requires A.pts_to pool 's ** R.pts_to root 'r ** R.pts_to w 'wv
  ensures exists* s' r' wv'. A.pts_to pool s' ** R.pts_to root r' ** R.pts_to w wv'
{
  let wv = !w;
  let wn = read_node pool wv;
  if (wn.color = Red) {
    write_node pool wv ({ wn with color = Black });
    let pnd = read_node pool xp;
    write_node pool xp ({ pnd with color = Red });
    left_rotate pool root xp;
    let pnd2 = read_node pool xp;
    w := pnd2.right
  }
}

// Case 1 right helper (symmetric)
inline_for_extraction
fn fixup_case1_right
  (pool: A.array node_data) (root: R.ref SZ.t) (w: R.ref SZ.t) (xp: SZ.t)
  requires A.pts_to pool 's ** R.pts_to root 'r ** R.pts_to w 'wv
  ensures exists* s' r' wv'. A.pts_to pool s' ** R.pts_to root r' ** R.pts_to w wv'
{
  let wv = !w;
  let wn = read_node pool wv;
  if (wn.color = Red) {
    write_node pool wv ({ wn with color = Black });
    let pnd = read_node pool xp;
    write_node pool xp ({ pnd with color = Red });
    right_rotate pool root xp;
    let pnd2 = read_node pool xp;
    w := pnd2.left
  }
}

// Case 3 left helper: if w.right is black, recolor + right rotate w + update w
inline_for_extraction
fn fixup_case3_left
  (pool: A.array node_data) (root: R.ref SZ.t) (w: R.ref SZ.t) (xp: SZ.t) (wrc: color)
  requires A.pts_to pool 's ** R.pts_to root 'r ** R.pts_to w 'wv
  ensures exists* s' r' wv'. A.pts_to pool s' ** R.pts_to root r' ** R.pts_to w wv'
{
  if (wrc = Black) {
    let wv = !w;
    let wn = read_node pool wv;
    let wln = read_node pool wn.left;
    write_node pool wn.left ({ wln with color = Black });
    write_node pool wv ({ wn with color = Red });
    right_rotate pool root wv;
    let pnd = read_node pool xp;
    w := pnd.right
  }
}

// Case 3 right helper (symmetric)
inline_for_extraction
fn fixup_case3_right
  (pool: A.array node_data) (root: R.ref SZ.t) (w: R.ref SZ.t) (xp: SZ.t) (wlc: color)
  requires A.pts_to pool 's ** R.pts_to root 'r ** R.pts_to w 'wv
  ensures exists* s' r' wv'. A.pts_to pool s' ** R.pts_to root r' ** R.pts_to w wv'
{
  if (wlc = Black) {
    let wv = !w;
    let wn = read_node pool wv;
    let wrn = read_node pool wn.right;
    write_node pool wn.right ({ wrn with color = Black });
    write_node pool wv ({ wn with color = Red });
    left_rotate pool root wv;
    let pnd = read_node pool xp;
    w := pnd.left
  }
}

fn rb_delete_fixup
  (pool: A.array node_data) (root: R.ref SZ.t) (x0: SZ.t)
  requires A.pts_to pool 's ** R.pts_to root 'r
  ensures exists* s' r'. A.pts_to pool s' ** R.pts_to root r'
{
  let mut x = x0;
  let mut cont = true;
  while ( !cont )
  invariant exists* s' r' xv cv. (
    A.pts_to pool s' ** R.pts_to root r' **
    R.pts_to x xv ** R.pts_to cont cv
  )
  {
    let xv = !x;
    let r = !root;
    let xn = read_node pool xv;
    if (xv <> r && xn.color = Black) {
      let xp = xn.p;
      let pn = read_node pool xp;
      if (xv = pn.left) {
        // x is left child
        let mut w = pn.right;
        // Case 1: sibling w is red
        fixup_case1_left pool root w xp;
        let wv = !w;
        let wn = read_node pool wv;
        let wln = read_node pool wn.left;
        let wrn = read_node pool wn.right;
        if (wln.color = Black && wrn.color = Black) {
          // Case 2: both of w's children are black
          write_node pool wv ({ wn with color = Red });
          x := xp
        } else {
          // Case 3: w.right is black → rotate
          fixup_case3_left pool root w xp wrn.color;
          // Case 4: w.right is red → recolor + rotate → done
          let wv2 = !w;
          let wn2 = read_node pool wv2;
          let pnd4 = read_node pool xp;
          write_node pool wv2 ({ wn2 with color = pnd4.color });
          write_node pool xp ({ pnd4 with color = Black });
          let wrn2 = read_node pool wn2.right;
          write_node pool wn2.right ({ wrn2 with color = Black });
          left_rotate pool root xp;
          let r2 = !root;
          x := r2;
          cont := false
        }
      } else {
        // Symmetric: x is right child
        let mut w = pn.left;
        fixup_case1_right pool root w xp;
        let wv = !w;
        let wn = read_node pool wv;
        let wrn = read_node pool wn.right;
        let wln = read_node pool wn.left;
        if (wrn.color = Black && wln.color = Black) {
          write_node pool wv ({ wn with color = Red });
          x := xp
        } else {
          fixup_case3_right pool root w xp wln.color;
          let wv2 = !w;
          let wn2 = read_node pool wv2;
          let pnd4 = read_node pool xp;
          write_node pool wv2 ({ wn2 with color = pnd4.color });
          write_node pool xp ({ pnd4 with color = Black });
          let wln2 = read_node pool wn2.left;
          write_node pool wn2.left ({ wln2 with color = Black });
          right_rotate pool root xp;
          let r2 = !root;
          x := r2;
          cont := false
        }
      }
    } else {
      // x == root or x.color == Red → done
      cont := false
    }
  };
  // x.color = BLACK
  let xv = !x;
  let xn = read_node pool xv;
  write_node pool xv ({ xn with color = Black })
}

// ========== RB-DELETE (§13.4) ==========
// Delete node z. Tracks y-original-color for fixup.
//
// if z.left == T.nil: transplant z with z.right
// elseif z.right == T.nil: transplant z with z.left
// else: find successor y = TREE-MINIMUM(z.right)
//   splice out y, replace z with y, fixup if y was black

// Helper: if successor y is direct child of z, just set x.p = y.
// Otherwise, splice out y and attach z's right subtree.
inline_for_extraction
fn splice_successor
  (pool: A.array node_data) (root: R.ref SZ.t)
  (z: SZ.t) (y: SZ.t) (x: SZ.t) (zn_right: SZ.t) (yn_p: SZ.t)
  requires A.pts_to pool 's ** R.pts_to root 'r
  ensures exists* s' r'. A.pts_to pool s' ** R.pts_to root r'
{
  if (yn_p = z) {
    let xn = read_node pool x;
    write_node pool x ({ xn with p = y })
  } else {
    rb_transplant pool root y x;
    let yn2 = read_node pool y;
    write_node pool y ({ yn2 with right = zn_right });
    let zrn = read_node pool zn_right;
    write_node pool zn_right ({ zrn with p = y })
  }
}

// Helper: conditional fixup after delete
inline_for_extraction
fn maybe_fixup
  (pool: A.array node_data) (root: R.ref SZ.t) (x: SZ.t) (orig_color: color)
  requires A.pts_to pool 's ** R.pts_to root 'r
  ensures exists* s' r'. A.pts_to pool s' ** R.pts_to root r'
{
  if (orig_color = Black) {
    rb_delete_fixup pool root x
  }
}

fn rb_delete
  (pool: A.array node_data) (root: R.ref SZ.t) (z: SZ.t)
  requires A.pts_to pool 's ** R.pts_to root 'r
  ensures exists* s' r'. A.pts_to pool s' ** R.pts_to root r'
{
  let zn = read_node pool z;
  if (is_nil zn.left) {
    // No left child: transplant right
    rb_transplant pool root z zn.right;
    maybe_fixup pool root zn.right zn.color
  } else {
    if (is_nil zn.right) {
      // No right child: transplant left
      rb_transplant pool root z zn.left;
      maybe_fixup pool root zn.left zn.color
    } else {
      // Two children: find successor y = TREE-MINIMUM(z.right)
      let y = tree_minimum pool zn.right;
      let yn = read_node pool y;
      let y_orig_color = yn.color;
      let x = yn.right;
      splice_successor pool root z y x zn.right yn.p;
      // Replace z with y
      rb_transplant pool root z y;
      let yn3 = read_node pool y;
      write_node pool y ({ yn3 with left = zn.left; color = zn.color });
      let zln = read_node pool zn.left;
      write_node pool zn.left ({ zln with p = y });
      maybe_fixup pool root x y_orig_color
    }
  }
}
