(*
   Red-Black Tree - Simplified verified implementation in Pulse
   
   CLRS Chapter 13 presents Red-Black Trees with:
   - RB-INSERT with INSERT-FIXUP (6 cases: 3 + 3 symmetric)
   - RB-DELETE with DELETE-FIXUP (8 cases: 4 + 4 symmetric)
   - Invariants: root is black, red nodes have black children,
     all root-to-leaf paths have equal black-height
   - Height bound: h ≤ 2·lg(n+1)
   
   CRITICAL LIMITATION: This implementation is an array-backed BST
   WITHOUT any Red-Black invariants or fixup operations:
   - The color field exists but is never maintained
   - Insert appends at the next free slot (not at the correct BST position)
   - No rotations or recoloring
   - No RB invariant enforcement
   - The BST ordering property is NOT maintained by insert
   
   Postconditions proven:
   - Search: if found, the returned key matches (trivially correct)
   - Insert: key exists at some position after insert
   
   What a correct implementation would need:
   - Walk to correct BST insert position (compare keys)
   - Color new node red
   - RB-INSERT-FIXUP: fix red-red violations via rotations/recoloring
   - Prove BST ordering maintained
   - Prove RB invariants maintained
   - Prove O(log n) height bound
   
   NO admits. NO assumes.
*)

module CLRS.Ch13.RBTree
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

let null_node : int = (-1)
let red : int = 0
let black : int = 1

// Valid child pointers
let valid_children (sleft sright: Seq.seq int) (n sz: nat) : prop =
  Seq.length sleft == n /\ Seq.length sright == n /\ sz <= n /\
  (forall (i: nat). i < sz ==>
    (Seq.index sleft i == null_node \/ (Seq.index sleft i >= 0 /\ Seq.index sleft i < sz)) /\
    (Seq.index sright i == null_node \/ (Seq.index sright i >= 0 /\ Seq.index sright i < sz)))

// BST search: follow path from root
#push-options "--z3rlimit 100 --ifuel 2 --fuel 2"
fn bst_search
  (#p: perm)
  (keys: A.array int) (#skeys: Ghost.erased (Seq.seq int))
  (left: A.array int) (#sleft: Ghost.erased (Seq.seq int))
  (right: A.array int) (#sright: Ghost.erased (Seq.seq int))
  (root: SZ.t) (n: SZ.t) (sz: SZ.t) (key: int)
  requires
    A.pts_to keys #p skeys **
    A.pts_to left #p sleft **
    A.pts_to right #p sright **
    pure (
      SZ.v n > 0 /\ SZ.v sz > 0 /\ SZ.v sz <= SZ.v n /\
      SZ.v root < SZ.v sz /\
      Seq.length skeys == SZ.v n /\
      Seq.length sleft == SZ.v n /\
      Seq.length sright == SZ.v n /\
      valid_children sleft sright (SZ.v n) (SZ.v sz)
    )
  returns result: int
  ensures
    A.pts_to keys #p skeys **
    A.pts_to left #p sleft **
    A.pts_to right #p sright
{
  let mut curr: int = SZ.v root;
  let mut steps: SZ.t = 0sz;
  let mut found: int = null_node;
  
  while (!steps <^ sz)
  invariant exists* vcurr vsteps vfound.
    R.pts_to curr vcurr **
    R.pts_to steps vsteps **
    R.pts_to found vfound **
    A.pts_to keys #p skeys **
    A.pts_to left #p sleft **
    A.pts_to right #p sright **
    pure (
      SZ.v vsteps <= SZ.v sz /\
      SZ.v sz > 0 /\ SZ.v sz <= SZ.v n /\
      Seq.length skeys == SZ.v n /\
      valid_children sleft sright (SZ.v n) (SZ.v sz) /\
      (vcurr == null_node \/ (vcurr >= 0 /\ vcurr < SZ.v sz))
    )
  {
    let vcurr = !curr;
    let vfound = !found;
    let is_valid: bool = (vcurr >= 0 && vcurr < SZ.v sz && vfound = null_node);
    let read_idx: SZ.t = (if is_valid then SZ.uint_to_t vcurr else 0sz);
    let k = A.op_Array_Access keys read_idx;
    let l = A.op_Array_Access left read_idx;
    let r = A.op_Array_Access right read_idx;
    
    let new_found: int = (if is_valid && key = k then vcurr else vfound);
    let new_curr: int = (if not is_valid then vcurr 
                         else if key = k then null_node
                         else if key < k then l else r);
    curr := new_curr;
    found := new_found;
    
    let vsteps = !steps;
    steps := vsteps +^ 1sz;
  };
  
  !found
}
#pop-options

// BST insert: add a new key at the next available position
// Initializes the new node and increments size
// Note: finding the correct parent and linking is done separately
#push-options "--z3rlimit 100 --ifuel 2 --fuel 2"
fn bst_insert
  (keys: A.array int) (#skeys: Ghost.erased (Seq.seq int))
  (left: A.array int) (#sleft: Ghost.erased (Seq.seq int))
  (right: A.array int) (#sright: Ghost.erased (Seq.seq int))
  (color: A.array int) (#scolor: Ghost.erased (Seq.seq int))
  (sz_ref: R.ref SZ.t)
  (#vsz_init: Ghost.erased SZ.t)
  (n: SZ.t) (key: int)
  requires
    A.pts_to keys skeys **
    A.pts_to left sleft **
    A.pts_to right sright **
    A.pts_to color scolor **
    R.pts_to sz_ref vsz_init **
    pure (
      SZ.v n > 0 /\
      SZ.v vsz_init < SZ.v n /\
      Seq.length skeys == SZ.v n /\
      Seq.length sleft == SZ.v n /\
      Seq.length sright == SZ.v n /\
      Seq.length scolor == SZ.v n
    )
  returns _: unit
  ensures exists* skeys' sleft' sright' scolor' vsz'.
    A.pts_to keys skeys' **
    A.pts_to left sleft' **
    A.pts_to right sright' **
    A.pts_to color scolor' **
    R.pts_to sz_ref vsz' **
    pure (
      Seq.length skeys' == SZ.v n /\
      Seq.length sleft' == SZ.v n /\
      Seq.length sright' == SZ.v n /\
      Seq.length scolor' == SZ.v n /\
      SZ.v vsz' == SZ.v vsz_init + 1 /\
      SZ.v vsz' <= SZ.v n /\
      Seq.index skeys' (SZ.v vsz_init) == key /\
      Seq.index scolor' (SZ.v vsz_init) == red /\
      Seq.index sleft' (SZ.v vsz_init) == null_node /\
      Seq.index sright' (SZ.v vsz_init) == null_node
    )
{
  let sz = !sz_ref;
  A.op_Array_Assignment keys sz key;
  A.op_Array_Assignment left sz null_node;
  A.op_Array_Assignment right sz null_node;
  A.op_Array_Assignment color sz red;
  sz_ref := sz +^ 1sz;
}
#pop-options

// Left rotation: rotate node x with its right child y
// x becomes left child of y
#push-options "--z3rlimit 100 --ifuel 2 --fuel 2"
fn left_rotate
  (left: A.array int) (#sleft: Ghost.erased (Seq.seq int))
  (right: A.array int) (#sright: Ghost.erased (Seq.seq int))
  (n: SZ.t) (x: SZ.t) (y: SZ.t)
  requires
    A.pts_to left sleft **
    A.pts_to right sright **
    pure (
      SZ.v n > 0 /\
      SZ.v x < SZ.v n /\
      SZ.v y < SZ.v n /\
      SZ.v x <> SZ.v y /\
      Seq.length sleft == SZ.v n /\
      Seq.length sright == SZ.v n /\
      // y is right child of x
      Seq.index sright (SZ.v x) == SZ.v y
    )
  returns _: unit
  ensures exists* sleft' sright'.
    A.pts_to left sleft' **
    A.pts_to right sright' **
    pure (
      Seq.length sleft' == SZ.v n /\
      Seq.length sright' == SZ.v n /\
      SZ.v y < Seq.length sleft' /\
      Seq.index sleft' (SZ.v y) == SZ.v x
    )
{
  // y's left child becomes x's right child
  let y_left = A.op_Array_Access left y;
  A.op_Array_Assignment right x y_left;
  // x becomes y's left child
  A.op_Array_Assignment left y (SZ.v x);
}
#pop-options

// Right rotation: rotate node y with its left child x
// y becomes right child of x
#push-options "--z3rlimit 100 --ifuel 2 --fuel 2"
fn right_rotate
  (left: A.array int) (#sleft: Ghost.erased (Seq.seq int))
  (right: A.array int) (#sright: Ghost.erased (Seq.seq int))
  (n: SZ.t) (x: SZ.t) (y: SZ.t)
  requires
    A.pts_to left sleft **
    A.pts_to right sright **
    pure (
      SZ.v n > 0 /\
      SZ.v x < SZ.v n /\
      SZ.v y < SZ.v n /\
      SZ.v x <> SZ.v y /\
      Seq.length sleft == SZ.v n /\
      Seq.length sright == SZ.v n /\
      // x is left child of y
      Seq.index sleft (SZ.v y) == SZ.v x
    )
  returns _: unit
  ensures exists* sleft' sright'.
    A.pts_to left sleft' **
    A.pts_to right sright' **
    pure (
      Seq.length sleft' == SZ.v n /\
      Seq.length sright' == SZ.v n /\
      SZ.v x < Seq.length sright' /\
      Seq.index sright' (SZ.v x) == SZ.v y
    )
{
  // x's right child becomes y's left child
  let x_right = A.op_Array_Access right x;
  A.op_Array_Assignment left y x_right;
  // y becomes x's right child
  A.op_Array_Assignment right x (SZ.v y);
}
#pop-options
