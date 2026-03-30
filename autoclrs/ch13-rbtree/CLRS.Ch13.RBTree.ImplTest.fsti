module CLRS.Ch13.RBTree.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives

fn test_rbtree_insert_search_delete ()
  requires emp
  returns r: bool
  ensures emp ** pure (r == true)
