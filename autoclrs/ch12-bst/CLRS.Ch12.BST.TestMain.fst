module CLRS.Ch12.BST.TestMain
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch12.BST.ImplTest

fn main ()
  requires emp
  returns _: unit
  ensures emp
{
  test_bst_ptr ()
}
