module CLRS.Ch15.RodCutting.ImplTest
#lang-pulse

open Pulse.Lib.Pervasives

fn test_rod_cutting ()
  requires emp
  returns r: bool
  ensures pure (r == true)
