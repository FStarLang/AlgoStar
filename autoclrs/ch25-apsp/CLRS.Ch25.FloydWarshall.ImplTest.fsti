module CLRS.Ch25.FloydWarshall.ImplTest

#lang-pulse
open Pulse.Lib.Pervasives

fn test_floyd_warshall_impl ()
  requires emp
  returns r: bool
  ensures pure (r == true)

fn test_neg_cycle_check_true ()
  requires emp
  returns r: bool
  ensures pure (r == true)

fn test_neg_cycle_check_false ()
  requires emp
  returns r: bool
  ensures pure (r == true)

fn test_floyd_warshall_safe_impl ()
  requires emp
  returns r: bool
  ensures pure (r == true)
