module CLRS.Ch22.BFS.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives

fn test_bfs_3 ()
  requires emp
  returns r: bool
  ensures emp ** pure (r == true)
