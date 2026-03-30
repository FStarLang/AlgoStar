module CLRS.Ch22.DFS.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives

fn test_dfs_3 ()
  requires emp
  returns r: bool
  ensures emp ** pure (r == true)
