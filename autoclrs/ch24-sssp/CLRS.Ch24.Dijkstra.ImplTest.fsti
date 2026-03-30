module CLRS.Ch24.Dijkstra.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives

fn test_dijkstra_3 (_: unit)
  requires emp
  returns r: bool
  ensures pure (r == true)
