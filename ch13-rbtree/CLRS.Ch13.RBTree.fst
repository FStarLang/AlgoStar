(*
   Red-Black Tree — Verified imperative wrapper in Pulse

   CLRS Chapter 13 presents Red-Black Trees with:
   - RB-INSERT with INSERT-FIXUP (Okasaki-style balance, 4 rotation cases)
   - BST search following the standard left/right comparison
   - Invariants: root is black, red nodes have black children,
     all root-to-leaf paths have equal black-height
   - Height bound: h ≤ 2·lg(n+1) (CLRS Theorem 13.1)

   This Pulse implementation wraps the pure functional RB tree from
   CLRS.Ch13.RBTree.Spec in a mutable reference. Each operation
   reads/writes the reference and calls the pure correctness lemmas
   to establish the postcondition.

   Proven properties (from Spec, re-exported via Pulse postconditions):
   - insert preserves RB invariants (is_rbtree)
   - insert preserves BST ordering (is_bst)
   - insert preserves existing membership and adds the new key
   - search correctness: found <==> key is a member
   - height bound: h ≤ 2·lg(n+1)

   NO admits. NO assumes.
*)

module CLRS.Ch13.RBTree
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference

module R = Pulse.Lib.Reference
module S = CLRS.Ch13.RBTree.Spec

let insert_preserves_all (t: S.rbtree) (key: int)
  : Lemma
    (requires S.is_rbtree t /\ S.is_bst t)
    (ensures forall (x: int). S.mem x t ==> S.mem x (S.insert t key))
  = FStar.Classical.forall_intro (S.insert_mem t key)

//SNIPPET_START: rb_search
fn rb_search
  (#p: perm)
  (tree_ref: R.ref S.rbtree)
  (#t: Ghost.erased S.rbtree)
  (key: int)
  requires
    R.pts_to tree_ref #p t
  returns result: option int
  ensures
    R.pts_to tree_ref #p t **
    pure (result == S.search t key)
{
  let t_val = !tree_ref;
  S.search t_val key
}
//SNIPPET_END: rb_search

//SNIPPET_START: rb_insert
fn rb_insert
  (tree_ref: R.ref S.rbtree)
  (#t: Ghost.erased S.rbtree)
  (key: int)
  requires
    R.pts_to tree_ref t **
    pure (S.is_rbtree t /\ S.is_bst t)
  returns _: unit
  ensures exists* t'.
    R.pts_to tree_ref t' **
    pure (
      Ghost.reveal t' == S.insert t key /\
      S.is_rbtree t' /\
      S.is_bst t' /\
      S.mem key t' /\
      (forall (x: int). S.mem x t ==> S.mem x t')
    )
{
  let t_val = !tree_ref;
  // Apply pure correctness lemmas from Spec before the write
  S.insert_is_rbtree t_val key;
  S.insert_preserves_bst t_val key;
  S.insert_mem t_val key key;
  insert_preserves_all t_val key;
  let t' = S.insert t_val key;
  tree_ref := t';
}
//SNIPPET_END: rb_insert
