module CLRS.Ch33.JarvisMarch.ImplTest
#lang-pulse
open Pulse.Lib.Pervasives

fn test_find_leftmost ()
  requires emp
  returns result: bool
  ensures emp ** pure (result == true)

fn test_find_next ()
  requires emp
  returns result: bool
  ensures emp ** pure (result == true)

fn test_jarvis_march ()
  requires emp
  returns result: bool
  ensures emp ** pure (result == true)

fn test_jarvis_march_with_hull ()
  requires emp
  returns result: bool
  ensures emp ** pure (result == true)
