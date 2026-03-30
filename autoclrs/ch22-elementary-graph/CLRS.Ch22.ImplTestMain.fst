(**
 * Ch22 ImplTest Main — Entry point for C extraction.
 *
 * Calls all three ImplTest functions (BFS, DFS, TopologicalSort).
 * Returns true iff all runtime checks pass.
 * This module has no .fsti so all declarations are public for krml extraction.
 *)
module CLRS.Ch22.ImplTestMain
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch22.BFS.ImplTest
open CLRS.Ch22.DFS.ImplTest
open CLRS.Ch22.TopologicalSort.ImplTest

fn run_all_tests ()
  requires emp
  returns r: bool
  ensures emp ** pure (r == true)
{
  let r1 = test_bfs_3 ();
  let r2 = test_dfs_3 ();
  let r3 = test_topo_sort_3 ();
  (r1 && r2 && r3)
}
