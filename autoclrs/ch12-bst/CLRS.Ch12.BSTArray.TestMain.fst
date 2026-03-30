module CLRS.Ch12.BSTArray.TestMain
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch12.BSTArray.ImplTest

fn main ()
  requires emp
  returns r: bool
  ensures pure (r == true)
{
  let r = test_bstarray_search_insert ();
  r
}
