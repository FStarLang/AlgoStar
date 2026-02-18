(*
   Red-Black Tree — Pointer-based verified implementation in Pulse

   CLRS Chapter 13: Red-Black Trees with Okasaki-style balance.

   This implementation uses heap-allocated nodes (box) with mutable
   fields, connected via nullable pointers (option (box rb_node)).
   A recursive separation-logic predicate `is_rbtree` ties the
   concrete pointer structure to the pure functional `rbtree` from
   CLRS.Ch13.RBTree.Spec.

   Operations:
   - rb_search:  recursive BST search, O(h)
   - rb_ins:     recursive insert with Okasaki balance, O(h)
   - rb_insert:  ins + make_black
   - rb_balance: pointer-level implementation of the four rotation cases

   Each operation's postcondition links to the pure spec: after
   `rb_insert`, the pointer tree represents `S.insert old_tree key`.

   NO admits. NO assumes.
*)

module CLRS.Ch13.RBTree
#lang-pulse
open Pulse.Lib.Pervasives

module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }

module S = CLRS.Ch13.RBTree.Spec
module G = FStar.Ghost

// ========== Node type and pointers ==========

//SNIPPET_START: rb_node_type
noeq
type rb_node = {
  key:   int;
  color: S.color;
  left:  rb_ptr;
  right: rb_ptr;
}

and rb_node_ptr = box rb_node

// Nullable pointer to a node
and rb_ptr = option rb_node_ptr
//SNIPPET_END: rb_node_type

// ========== Recursive separation logic predicate ==========

//SNIPPET_START: is_rbtree
let rec is_rbtree (ct: rb_ptr) (ft: S.rbtree)
  : Tot slprop (decreases ft)
  = match ft with
    | S.Leaf -> pure (ct == None)
    | S.Node c l v r ->
      exists* (p: rb_node_ptr) (lct: rb_ptr) (rct: rb_ptr).
        pure (ct == Some p) **
        (p |-> { key = v; color = c; left = lct; right = rct }) **
        is_rbtree lct l **
        is_rbtree rct r
//SNIPPET_END: is_rbtree

// ========== Ghost fold/unfold helpers ==========

ghost fn elim_is_rbtree_leaf (x: rb_ptr)
  requires is_rbtree x S.Leaf
  ensures pure (x == None)
{
  unfold (is_rbtree x S.Leaf)
}

ghost fn intro_is_rbtree_leaf (x: rb_ptr)
  requires pure (x == None)
  ensures is_rbtree x S.Leaf
{
  fold (is_rbtree x S.Leaf)
}

ghost fn intro_is_rbtree_node (ct: rb_ptr) (p: rb_node_ptr)
  (#node: rb_node) (#lt #rt: S.rbtree)
  requires
    (p |-> node) **
    is_rbtree node.left lt **
    is_rbtree node.right rt **
    pure (ct == Some p)
  ensures
    is_rbtree ct (S.Node node.color lt node.key rt)
{
  fold (is_rbtree ct (S.Node node.color lt node.key rt))
}

// ========== Non-recursive cases predicate ==========

[@@no_mkeys]
let is_rbtree_cases (x: rb_ptr) (ft: S.rbtree)
  = match x with
    | None -> pure (ft == S.Leaf)
    | Some v ->
      exists* (n: rb_node) (lt rt: S.rbtree).
        (v |-> n) **
        pure (ft == S.Node n.color lt n.key rt) **
        is_rbtree n.left lt **
        is_rbtree n.right rt

ghost fn cases_of_is_rbtree (x: rb_ptr) (ft: S.rbtree)
  requires is_rbtree x ft
  ensures is_rbtree_cases x ft
{
  match ft {
    S.Leaf -> {
      unfold (is_rbtree x S.Leaf);
      fold (is_rbtree_cases None ft);
      rewrite is_rbtree_cases None ft as is_rbtree_cases x ft;
    }
    S.Node c lt v rt -> {
      unfold (is_rbtree x (S.Node c lt v rt));
      with p lct rct. _;
      with n. assert p |-> n;
      with l'. rewrite is_rbtree lct l' as is_rbtree n.left l';
      with r'. rewrite is_rbtree rct r' as is_rbtree n.right r';
      fold (is_rbtree_cases (Some p) ft);
      rewrite (is_rbtree_cases (Some p) ft) as is_rbtree_cases x ft;
    }
  }
}

ghost fn is_rbtree_case_none (x: rb_ptr) (#ft: S.rbtree)
  preserves is_rbtree x ft
  requires pure (x == None)
  ensures pure (ft == S.Leaf)
{
  rewrite each x as None;
  cases_of_is_rbtree None ft;
  unfold is_rbtree_cases;
  intro_is_rbtree_leaf (None #rb_node_ptr);
  rewrite is_rbtree (None #rb_node_ptr) S.Leaf as is_rbtree x ft;
  ()
}

ghost fn is_rbtree_case_some (x: rb_ptr) (v: rb_node_ptr) (#ft: S.rbtree)
  requires is_rbtree x ft ** pure (x == Some v)
  ensures exists* (node: rb_node) (lt rt: S.rbtree).
    (v |-> node) **
    is_rbtree node.left lt **
    is_rbtree node.right rt **
    pure (ft == S.Node node.color lt node.key rt)
{
  rewrite each x as Some v;
  cases_of_is_rbtree (Some v) ft;
  unfold is_rbtree_cases;
}

// Learn that a non-Leaf ghost tree implies Some? pointer
ghost fn is_rbtree_not_leaf (x: rb_ptr) (#ft: S.rbtree)
  preserves is_rbtree x ft
  requires pure (S.Node? ft)
  ensures pure (Some? x)
{
  let S.Node c lt v rt = ft;
  unfold (is_rbtree x (S.Node c lt v rt));
  with p lct rct. _;
  // x == Some p, so Some? x
  fold (is_rbtree x (S.Node c lt v rt));
  rewrite is_rbtree x (S.Node c lt v rt) as is_rbtree x ft;
  ()
}

// ========== Helper: new node ==========

fn new_node (k: int) (c: S.color) (l: rb_ptr) (r: rb_ptr)
  (#lt #rt: G.erased S.rbtree)
  requires is_rbtree l lt ** is_rbtree r rt
  returns y: rb_ptr
  ensures is_rbtree y (S.Node c lt k rt) ** pure (Some? y)
{
  let p = Box.alloc { key = k; color = c; left = l; right = r };
  intro_is_rbtree_node (Some p) p;
  Some p
}

// ========== Balance — using pure classifier ==========

// Helper: open a non-null pointer to read its node
// (just a convenience wrapper around is_rbtree_case_some + deref)

//SNIPPET_START: rb_balance

// Check if right subtree matches RL or RR pattern.
// Preserves the slprop — read-only traversal.
fn check_right_balance (r: rb_ptr)
  (#rt: G.erased S.rbtree)
  preserves is_rbtree r rt
  returns bc: S.balance_case
  ensures pure (bc == (match rt with
    | S.Node S.Red (S.Node S.Red _ _ _) _ _ -> S.BC_RL
    | S.Node S.Red _ _ (S.Node S.Red _ _ _) -> S.BC_RR
    | _ -> S.BC_None))
{
  match r {
    None -> {
      is_rbtree_case_none (None #rb_node_ptr);
      rewrite is_rbtree (None #rb_node_ptr) rt as is_rbtree r rt;
      S.BC_None
    }
    Some rp -> {
      rewrite each (Some rp) as r;
      is_rbtree_case_some r rp;
      let rn = !rp;
      if (S.Red? rn.color) {
        // Check RL
        match rn.left {
          None -> {
            is_rbtree_case_none rn.left;
            // Check RR
            match rn.right {
              None -> {
                is_rbtree_case_none rn.right;
                intro_is_rbtree_node r rp;
                with t. rewrite (is_rbtree r t) as (is_rbtree r rt);
                S.BC_None
              }
              Some rrp -> {
                rewrite each (Some rrp) as rn.right;
                is_rbtree_case_some rn.right rrp;
                let rrn = !rrp;
                let res = (if (S.Red? rrn.color) then S.BC_RR else S.BC_None);
                intro_is_rbtree_node rn.right rrp;
                intro_is_rbtree_node r rp;
                with t. rewrite (is_rbtree r t) as (is_rbtree r rt);
                res
              }
            }
          }
          Some rlp -> {
            rewrite each (Some rlp) as rn.left;
            is_rbtree_case_some rn.left rlp;
            let rln = !rlp;
            if (S.Red? rln.color) {
              intro_is_rbtree_node rn.left rlp;
              intro_is_rbtree_node r rp;
              with t. rewrite (is_rbtree r t) as (is_rbtree r rt);
              S.BC_RL
            } else {
              intro_is_rbtree_node rn.left rlp;
              // Check RR
              match rn.right {
                None -> {
                  is_rbtree_case_none rn.right;
                  intro_is_rbtree_node r rp;
                  with t. rewrite (is_rbtree r t) as (is_rbtree r rt);
                  S.BC_None
                }
                Some rrp -> {
                  rewrite each (Some rrp) as rn.right;
                  is_rbtree_case_some rn.right rrp;
                  let rrn = !rrp;
                  let res = (if (S.Red? rrn.color) then S.BC_RR else S.BC_None);
                  intro_is_rbtree_node rn.right rrp;
                  intro_is_rbtree_node r rp;
                  with t. rewrite (is_rbtree r t) as (is_rbtree r rt);
                  res
                }
              }
            }
          }
        }
      } else {
        intro_is_rbtree_node r rp;
        with t. rewrite (is_rbtree r t) as (is_rbtree r rt);
        S.BC_None
      }
    }
  }
}

// Runtime classification: check left first for LL/LR, then right for RL/RR.
fn classify_runtime (c: S.color) (l: rb_ptr) (r: rb_ptr)
  (#lt #rt: G.erased S.rbtree)
  preserves is_rbtree l lt ** is_rbtree r rt
  returns bc: S.balance_case
  ensures pure (bc == S.classify_balance c lt rt)
{
  if (S.Red? c) {
    S.BC_None
  } else {
    match l {
      None -> {
        is_rbtree_case_none (None #rb_node_ptr);
        rewrite is_rbtree (None #rb_node_ptr) lt as is_rbtree l lt;
        check_right_balance r
      }
      Some lp -> {
        rewrite each (Some lp) as l;
        is_rbtree_case_some l lp;
        let ln = !lp;
        if (S.Red? ln.color) {
          // Check LL
          match ln.left {
            None -> {
              is_rbtree_case_none ln.left;
              // Check LR
              match ln.right {
                None -> {
                  is_rbtree_case_none ln.right;
                  intro_is_rbtree_node l lp;
                  with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
                  check_right_balance r
                }
                Some lrp -> {
                  rewrite each (Some lrp) as ln.right;
                  is_rbtree_case_some ln.right lrp;
                  let lrn = !lrp;
                  if (S.Red? lrn.color) {
                    intro_is_rbtree_node ln.right lrp;
                    intro_is_rbtree_node l lp;
                    with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
                    S.BC_LR
                  } else {
                    intro_is_rbtree_node ln.right lrp;
                    intro_is_rbtree_node l lp;
                    with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
                    check_right_balance r
                  }
                }
              }
            }
            Some llp -> {
              rewrite each (Some llp) as ln.left;
              is_rbtree_case_some ln.left llp;
              let lln = !llp;
              if (S.Red? lln.color) {
                intro_is_rbtree_node ln.left llp;
                intro_is_rbtree_node l lp;
                with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
                S.BC_LL
              } else {
                intro_is_rbtree_node ln.left llp;
                // Check LR
                match ln.right {
                  None -> {
                    is_rbtree_case_none ln.right;
                    intro_is_rbtree_node l lp;
                    with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
                    check_right_balance r
                  }
                  Some lrp -> {
                    rewrite each (Some lrp) as ln.right;
                    is_rbtree_case_some ln.right lrp;
                    let lrn = !lrp;
                    if (S.Red? lrn.color) {
                      intro_is_rbtree_node ln.right lrp;
                      intro_is_rbtree_node l lp;
                      with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
                      S.BC_LR
                    } else {
                      intro_is_rbtree_node ln.right lrp;
                      intro_is_rbtree_node l lp;
                      with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
                      check_right_balance r
                    }
                  }
                }
              }
            }
          }
        } else {
          intro_is_rbtree_node l lp;
          with t. rewrite (is_rbtree l t) as (is_rbtree l lt);
          check_right_balance r
        }
      }
    }
  }
}

// LL case: balance Black (Node Red (Node Red a x b) y c_) v r
//   = Node Red (Node Black a x b) y (Node Black c_ v r)
// Precondition: l points to Node Red (Node Red a x b) y c_
// We open l, open l.left, restructure
fn balance_ll (l: rb_ptr) (v: int) (r: rb_ptr)
  (#lt #rt: G.erased S.rbtree)
  requires is_rbtree l lt ** is_rbtree r rt **
           pure (S.BC_LL? (S.classify_balance S.Black lt rt))
  returns y: rb_ptr
  ensures is_rbtree y (S.balance S.Black lt v rt)
{
  S.classify_balance_lemma S.Black lt v rt;
  // BC_LL implies lt is a Node
  is_rbtree_not_leaf l;
  let lp = Some?.v l;
  rewrite each (Some lp) as l;
  is_rbtree_case_some l lp;
  let ln = !lp;
  // ln.left must be Some (the red grandchild)
  // BC_LL means lt = Node Red (Node Red a x b) y c_
  // so ln.left's ghost tree is Node Red a x b, i.e., a Node
  is_rbtree_not_leaf ln.left;
  let llp = Some?.v ln.left;
  rewrite each (Some llp) as ln.left;
  is_rbtree_case_some ln.left llp;
  let lln = !llp;
  // Now we have:
  //   lln.left -> a, lln.right -> b, lln.key = x
  //   ln.right -> c_, ln.key = y
  //   r -> rt, v = v
  // Build: Node Red (Node Black a x b) y (Node Black c_ v r)

  // Reuse llp for Node Black a x b
  llp := { key = lln.key; color = S.Black; left = lln.left; right = lln.right };
  intro_is_rbtree_node ln.left llp;

  // New node for Node Black c_ v r
  let right_black = new_node v S.Black ln.right r;

  // Reuse lp for Node Red (Node Black a x b) y (Node Black c_ v r)
  lp := { key = ln.key; color = S.Red; left = ln.left; right = right_black };
  intro_is_rbtree_node l lp;

  // The result matches S.balance S.Black lt v rt by classify_balance_lemma
  with result_tree. rewrite (is_rbtree l result_tree)
       as (is_rbtree l (S.balance S.Black lt v rt));
  l
}

// LR case: balance Black (Node Red a x (Node Red b y c_)) v r
//   = Node Red (Node Black a x b) y (Node Black c_ v r)
fn balance_lr (l: rb_ptr) (v: int) (r: rb_ptr)
  (#lt #rt: G.erased S.rbtree)
  requires is_rbtree l lt ** is_rbtree r rt **
           pure (S.BC_LR? (S.classify_balance S.Black lt rt))
  returns y: rb_ptr
  ensures is_rbtree y (S.balance S.Black lt v rt)
{
  S.classify_balance_lemma S.Black lt v rt;
  is_rbtree_not_leaf l;
  let lp = Some?.v l;
  rewrite each (Some lp) as l;
  is_rbtree_case_some l lp;
  let ln = !lp;
  // ln.right must be Some (the red grandchild)
  is_rbtree_not_leaf ln.right;
  let lrp = Some?.v ln.right;
  rewrite each (Some lrp) as ln.right;
  is_rbtree_case_some ln.right lrp;
  let lrn = !lrp;
  // Build: Node Red (Node Black a x b) y (Node Black c_ v r)
  // a = ln.left, x = ln.key, b = lrn.left, y = lrn.key, c_ = lrn.right

  // Reuse lp for Node Black a x b
  lp := { key = ln.key; color = S.Black; left = ln.left; right = lrn.left };
  intro_is_rbtree_node l lp;

  // New node for Node Black c_ v r
  let right_black = new_node v S.Black lrn.right r;

  // Reuse lrp for Node Red root
  lrp := { key = lrn.key; color = S.Red; left = l; right = right_black };
  intro_is_rbtree_node (Some lrp) lrp;
  with result_tree. rewrite (is_rbtree (Some lrp) result_tree)
       as (is_rbtree (Some lrp) (S.balance S.Black lt v rt));
  Some lrp
}

// RL case: balance Black l v (Node Red (Node Red b y c_) z d)
//   = Node Red (Node Black l v b) y (Node Black c_ z d)
fn balance_rl (l: rb_ptr) (v: int) (r: rb_ptr)
  (#lt #rt: G.erased S.rbtree)
  requires is_rbtree l lt ** is_rbtree r rt **
           pure (S.BC_RL? (S.classify_balance S.Black lt rt))
  returns y: rb_ptr
  ensures is_rbtree y (S.balance S.Black lt v rt)
{
  S.classify_balance_lemma S.Black lt v rt;
  is_rbtree_not_leaf r;
  let rp = Some?.v r;
  rewrite each (Some rp) as r;
  is_rbtree_case_some r rp;
  let rn = !rp;
  // rn.left must be Some (the red grandchild)
  is_rbtree_not_leaf rn.left;
  let rlp = Some?.v rn.left;
  rewrite each (Some rlp) as rn.left;
  is_rbtree_case_some rn.left rlp;
  let rln = !rlp;
  // Build: Node Red (Node Black l v b) y (Node Black c_ z d)
  // b = rln.left, y = rln.key, c_ = rln.right, z = rn.key, d = rn.right

  // New node for Node Black l v b
  let left_black = new_node v S.Black l rln.left;

  // Reuse rp for Node Black c_ z d
  rp := { key = rn.key; color = S.Black; left = rln.right; right = rn.right };
  intro_is_rbtree_node r rp;

  // Reuse rlp for Node Red root
  rlp := { key = rln.key; color = S.Red; left = left_black; right = r };
  intro_is_rbtree_node (Some rlp) rlp;
  with result_tree. rewrite (is_rbtree (Some rlp) result_tree)
       as (is_rbtree (Some rlp) (S.balance S.Black lt v rt));
  Some rlp
}

// RR case: balance Black l v (Node Red b y (Node Red c_ z d))
//   = Node Red (Node Black l v b) y (Node Black c_ z d)
fn balance_rr (l: rb_ptr) (v: int) (r: rb_ptr)
  (#lt #rt: G.erased S.rbtree)
  requires is_rbtree l lt ** is_rbtree r rt **
           pure (S.BC_RR? (S.classify_balance S.Black lt rt))
  returns y: rb_ptr
  ensures is_rbtree y (S.balance S.Black lt v rt)
{
  S.classify_balance_lemma S.Black lt v rt;
  is_rbtree_not_leaf r;
  let rp = Some?.v r;
  rewrite each (Some rp) as r;
  is_rbtree_case_some r rp;
  let rn = !rp;
  // rn.right must be Some (the red grandchild)
  is_rbtree_not_leaf rn.right;
  let rrp = Some?.v rn.right;
  rewrite each (Some rrp) as rn.right;
  is_rbtree_case_some rn.right rrp;
  let rrn = !rrp;
  // Build: Node Red (Node Black l v b) y (Node Black c_ z d)
  // b = rn.left, y = rn.key, c_ = rrn.left, z = rrn.key, d = rrn.right

  // New node for Node Black l v b
  let left_black = new_node v S.Black l rn.left;

  // Reuse rrp for Node Black c_ z d
  rrp := { key = rrn.key; color = S.Black; left = rrn.left; right = rrn.right };
  intro_is_rbtree_node rn.right rrp;

  // Reuse rp for Node Red root
  rp := { key = rn.key; color = S.Red; left = left_black; right = rn.right };
  intro_is_rbtree_node r rp;
  with result_tree. rewrite (is_rbtree r result_tree)
       as (is_rbtree r (S.balance S.Black lt v rt));
  r
}

fn rb_balance (c: S.color) (l: rb_ptr) (v: int) (r: rb_ptr)
  (#lt #rt: G.erased S.rbtree)
  requires is_rbtree l lt ** is_rbtree r rt
  returns y: rb_ptr
  ensures is_rbtree y (S.balance c lt v rt)
{
  let bc = classify_runtime c l r;
  match bc {
    S.BC_LL -> {
      let y = balance_ll l v r;
      rewrite (is_rbtree y (S.balance S.Black lt v rt))
           as (is_rbtree y (S.balance c lt v rt));
      y
    }
    S.BC_LR -> {
      let y = balance_lr l v r;
      rewrite (is_rbtree y (S.balance S.Black lt v rt))
           as (is_rbtree y (S.balance c lt v rt));
      y
    }
    S.BC_RL -> {
      let y = balance_rl l v r;
      rewrite (is_rbtree y (S.balance S.Black lt v rt))
           as (is_rbtree y (S.balance c lt v rt));
      y
    }
    S.BC_RR -> {
      let y = balance_rr l v r;
      rewrite (is_rbtree y (S.balance S.Black lt v rt))
           as (is_rbtree y (S.balance c lt v rt));
      y
    }
    S.BC_None -> {
      S.classify_balance_lemma c lt v rt;
      let y = new_node v c l r;
      with result_tree. rewrite (is_rbtree y result_tree)
           as (is_rbtree y (S.balance c lt v rt));
      y
    }
  }
}
//SNIPPET_END: rb_balance

// ========== Search ==========

//SNIPPET_START: rb_search
fn rec rb_search (tree: rb_ptr) (k: int)
  preserves is_rbtree tree 'ft
  returns result: option int
  ensures pure (result == S.search 'ft k)
{
  match tree {
    None -> {
      is_rbtree_case_none (None #rb_node_ptr);
      rewrite is_rbtree (None #rb_node_ptr) 'ft as is_rbtree tree 'ft;
      None #int
    }
    Some vl -> {
      is_rbtree_case_some (Some vl) vl;
      let node = !vl;
      if (k < node.key) {
        let res = rb_search node.left k;
        intro_is_rbtree_node (Some vl) vl;
        with t. rewrite (is_rbtree (Some vl) t) as (is_rbtree tree 'ft);
        res
      } else if (k > node.key) {
        let res = rb_search node.right k;
        intro_is_rbtree_node (Some vl) vl;
        with t. rewrite (is_rbtree (Some vl) t) as (is_rbtree tree 'ft);
        res
      } else {
        intro_is_rbtree_node (Some vl) vl;
        with t. rewrite (is_rbtree (Some vl) t) as (is_rbtree tree 'ft);
        Some node.key
      }
    }
  }
}
//SNIPPET_END: rb_search

// ========== Insert ==========

//SNIPPET_START: rb_ins
fn rec rb_ins (tree: rb_ptr) (k: int)
  requires is_rbtree tree 'ft
  returns y: rb_ptr
  ensures is_rbtree y (S.ins 'ft k)
{
  match tree {
    None -> {
      is_rbtree_case_none (None #rb_node_ptr);
      // 'ft == S.Leaf, so is_rbtree None 'ft is just pure(None==None)
      // Consume the old tree's slprop (Leaf = no heap resources)
      rewrite is_rbtree (None #rb_node_ptr) 'ft as is_rbtree (None #rb_node_ptr) S.Leaf;
      elim_is_rbtree_leaf (None #rb_node_ptr);
      // Create Node Red Leaf k Leaf
      let left_leaf : rb_ptr = None #rb_node_ptr;
      intro_is_rbtree_leaf left_leaf;
      let right_leaf : rb_ptr = None #rb_node_ptr;
      intro_is_rbtree_leaf right_leaf;
      let y = new_node k S.Red left_leaf right_leaf;
      with t. rewrite (is_rbtree y t) as (is_rbtree y (S.ins 'ft k));
      y
    }
    Some vl -> {
      is_rbtree_case_some (Some vl) vl;
      let node = !vl;
      if (k < node.key) {
        let new_left = rb_ins node.left k;
        Box.free vl;
        let y = rb_balance node.color new_left node.key node.right;
        with t. rewrite (is_rbtree y t) as (is_rbtree y (S.ins 'ft k));
        y
      } else if (k > node.key) {
        let new_right = rb_ins node.right k;
        Box.free vl;
        let y = rb_balance node.color node.left node.key new_right;
        with t. rewrite (is_rbtree y t) as (is_rbtree y (S.ins 'ft k));
        y
      } else {
        // Duplicate key — return Node c l v r unchanged
        vl := node;
        intro_is_rbtree_node (Some vl) vl;
        with t. rewrite (is_rbtree (Some vl) t) as (is_rbtree tree (S.ins 'ft k));
        tree
      }
    }
  }
}
//SNIPPET_END: rb_ins

//SNIPPET_START: rb_make_black
fn rb_make_black (tree: rb_ptr)
  requires is_rbtree tree 'ft
  returns y: rb_ptr
  ensures is_rbtree y (S.make_black 'ft)
{
  match tree {
    None -> {
      // 'ft must be Leaf since tree == None  
      is_rbtree_case_none (None #rb_node_ptr);
      // is_rbtree None 'ft is preserved, and 'ft == S.Leaf
      // S.make_black S.Leaf == S.Leaf == 'ft, so just rewrite  
      rewrite is_rbtree (None #rb_node_ptr) 'ft as is_rbtree tree (S.make_black 'ft);
      tree
    }
    Some vl -> {
      is_rbtree_case_some (Some vl) vl;
      let node = !vl;
      vl := { key = node.key; color = S.Black; left = node.left; right = node.right };
      intro_is_rbtree_node (Some vl) vl;
      with t. rewrite (is_rbtree (Some vl) t) as (is_rbtree tree (S.make_black 'ft));
      tree
    }
  }
}
//SNIPPET_END: rb_make_black

//SNIPPET_START: rb_insert
fn rb_insert (tree: rb_ptr) (k: int)
  requires is_rbtree tree 'ft
  returns y: rb_ptr
  ensures is_rbtree y (S.insert 'ft k)
{
  let t = rb_ins tree k;
  rb_make_black t
}
//SNIPPET_END: rb_insert
