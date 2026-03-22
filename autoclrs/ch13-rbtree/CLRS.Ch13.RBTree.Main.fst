module CLRS.Ch13.RBTree.Main
#lang-pulse
open Pulse.Lib.Pervasives

module T = CLRS.Ch13.RBTree.ImplTest

fn main ()
  requires emp
  ensures emp
{
  T.test_rbtree_insert_search_delete ()
}
