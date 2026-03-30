module CLRS.Ch12.BSTArray.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives

fn test_bstarray_search_insert ()
  requires emp
  returns r: bool
  ensures pure (r == true)
