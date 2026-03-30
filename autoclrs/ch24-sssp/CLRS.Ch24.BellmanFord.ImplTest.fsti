module CLRS.Ch24.BellmanFord.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives

fn test_bellman_ford_3 (_: unit)
  requires emp
  returns r: bool
  ensures pure (r == true)
