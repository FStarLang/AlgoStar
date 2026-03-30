module CLRS.Ch13.RBTree.Main
#lang-pulse
open Pulse.Lib.Pervasives

module T = CLRS.Ch13.RBTree.ImplTest

fn main ()
  requires emp
  returns r: bool
  ensures emp ** pure (r == true)
{
  T.test_rbtree_insert_search_delete ()
}
