module CLRS.Ch22.TopologicalSort.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives

fn test_topo_sort_3 ()
  requires emp
  returns r: bool
  ensures emp ** pure (r == true)
