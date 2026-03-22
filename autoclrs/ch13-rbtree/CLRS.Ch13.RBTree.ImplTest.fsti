module CLRS.Ch13.RBTree.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives

fn test_rbtree_insert_search_delete ()
  requires emp
  returns _: unit
  ensures emp
